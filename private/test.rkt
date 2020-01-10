#lang racket/base

(module+ test
  (require (for-syntax racket/base)
           redex/reduction-semantics
           rackunit
           syntax/macro-testing
           racket/set
           "../parameter.rkt")

  (define (apply-rr . xs)
    (apply set (apply apply-reduction-relation xs)))

  ;; L0

  (define-language L0
    [m ::= number]
    [E ::= (wrap E) hole])

  (define-metafunction L0
    [(-foo-mf m) 1])

  (define-judgment-form L0
    #:mode (-foo-jf I O)
    [(-foo-jf m 1)])

  (define-reduction-relation r0-mf
    L0
    #:parameters ([foo-mf -foo-mf])
    [--> m (foo-mf m)])

  (define-reduction-relation r0-jf
    L0
    #:parameters ([foo-jf -foo-jf])
    [--> m_1 m_2 (judgment-holds (foo-jf m_1 m_2))])

  (define-reduction-relation r0-rr
    L0
    #:parameters ([r r0-mf])
    [--> m_1 m_2
         (where (_ ... m_2 _ ...)
                ,(apply-reduction-relation r (term m_1)))])

  (test-case "Normal functioning."
    (check-equal? (apply-rr r0-mf (term 0)) (set 1))
    (check-equal? (apply-rr r0-jf (term 0)) (set 1))
    (check-equal? (apply-rr r0-rr (term 0)) (set 1)))

  (define-metafunction L0
    [(-bar-mf m) 2])

  (define-judgment-form L0
    #:mode (-bar-jf I O)
    [(-bar-jf m 2)])

  (define r* (r0-mf [foo-mf -bar-mf]))

  (test-case "Explicit parameterization."
    (check-equal? (apply-rr (r0-mf [foo-mf -bar-mf]) (term 0)) (set 2))
    (check-equal? (apply-rr (r0-jf [foo-jf -bar-jf]) (term 0)) (set 2))
    (check-equal? (apply-rr (r0-rr [r r*]) (term 0)) (set 2)))

  (test-case "Explicit parameterization failures."
    (check-exn
     #rx"invalid parameter"
     (λ () (convert-syntax-error (apply-rr (r0-mf [oops-mf bar-mf]) (term 0)))))

    (check-exn
     #rx"duplicate parameter"
     (λ ()
       (convert-syntax-error (apply-rr (r0-mf [foo-mf -bar-mf]
                                              [foo-mf -bar-mf])
                                       (term 0))))))

  ;; L1

  (define-extended-language L1 L0
    [m ::= .... string])

  (define-reduction-relation r-immediate
    L1
    #:parameters ([mf-immediate -foo-mf])
    [--> m (mf-immediate m)])

  (test-case "Immediate lift."
    (check-equal? (apply-rr r-immediate (term "hi"))
                  (set 1)))

  (define normal-rr
    (reduction-relation
     L0
     [--> m 1]))

  (define-extended-reduction-relation normal-extended
    normal-rr L1
    [--> m 10])

  (test-case "Extension of normal reduction relation."
    (check-equal? (apply-rr normal-extended (term "hi")) (set 1 10)))

  (define-extended-reduction-relation r1-rr-no-extend r0-rr L1)

  (test-case "Implicit lifting of reduction relation."
    (check-equal? (apply-rr r1-rr-no-extend (term "hi")) (set 1)))

  (define-extended-reduction-relation r1-mf
    r0-mf L1
    [--> m 13])

  (define-extended-reduction-relation r1-jf
    r0-jf L1
    [--> m 13])

  (define-extended-reduction-relation r1-rr r0-rr L1)

  (test-case "Normal extension."
    (check-equal? (apply-rr r1-mf (term 0)) (set 1 13))
    (check-equal? (apply-rr r1-jf (term 0)) (set 1 13)))

  (test-case "Extension with implicit lifting."
    (check-equal? (apply-rr r1-mf (term "hi")) (set 1 13))
    (check-equal? (apply-rr r1-jf (term "hi")) (set 1 13))
    (check-equal? (apply-rr r1-rr (term "hi")) (set 1 13)))

  (test-case "Explicit parameterization of an extension."
    (check-equal? (apply-rr (r1-mf [foo-mf -bar-mf]) (term 0)) (set 2 13))
    (check-equal? (apply-rr (r1-jf [foo-jf -bar-jf]) (term 0)) (set 2 13)))

  (define-metafunction L1
    [(-foo-mf* m) 3])

  (define-judgment-form L1
    #:mode (-foo-jf* I O)
    [(-foo-jf* m 3)])

  (define-extended-reduction-relation r1-mf*
    r0-mf L1 #:parameters ([foo-mf* -foo-mf*])
    [--> m (foo-mf* m)])

  (define-extended-reduction-relation r1-jf*
    r0-jf L1 #:parameters ([foo-jf* -foo-jf*])
    [--> m_1 m_2 (judgment-holds (foo-jf* m_1 m_2))])

  (test-case "Normal extension with new parameter."
    (check-equal? (apply-rr r1-mf* (term 0)) (set 1 3))
    (check-equal? (apply-rr r1-jf* (term 0)) (set 1 3)))

  (test-case "Explicit parameterization of an new parameter."
    (check-equal? (apply-rr (r1-mf* [foo-mf* -bar-mf]) (term 0)) (set 1 2))
    (check-equal? (apply-rr (r1-jf* [foo-jf* -bar-jf]) (term 0)) (set 1 2))
    (check-equal? (apply-rr (r1-mf* [foo-mf -bar-mf] [foo-mf* -bar-mf]) (term 0))
                  (set 2))
    (check-equal? (apply-rr (r1-jf* [foo-jf -bar-jf] [foo-jf* -bar-jf]) (term 0))
                  (set 2)))

  (define-extended-metafunction -foo-mf L1
    [(-foo-mf** m) 4])

  (define-extended-judgment -foo-jf L1
    #:mode (-foo-jf** I O)
    [(-foo-jf** m 4)])

  (define-extended-reduction-relation r1-mf** r0-mf L1)
  (define-extended-reduction-relation r1-jf** r0-jf L1)

  (test-case "Normal extension with parameter from extension."
    (check-equal? (apply-rr r1-mf** (term 0)) (set 4))
    (check-equal? (apply-rr r1-jf** (term 0)) (set 1 4)))

  (define-extended-reduction-relation r0-mf-wrap
    (context-closure s current-language E)
    L0
    #:parameters ([s r0-mf]))

  (test-case "Extend closure of reduction relation."
    (check-equal? (apply-rr r0-mf-wrap (term (wrap 0)))
                  (set (term (wrap 1)))))

  (define-extended-reduction-relation r1-mf-wrap r0-mf-wrap L1)

  (test-case "Closure with reduction relation extension."
    (check-equal? (apply-rr r1-mf-wrap (term (wrap "hi")))
                  (set (term (wrap 4)))))

  (define-extended-language L2 L1
    [m ::= .... boolean])

  (define-metafunction L0
    [(gimme-one m) 1])

  (define-reduction-relation r0-triple
    L0
    #:parameters ([triple-mf gimme-one])
    [--> m (triple-mf m)])

  (define-extended-reduction-relation r1-triple r0-triple L1)

  (define-extended-metafunction gimme-one L2
    [(gimme-seventeen m) 17])

  (define-extended-reduction-relation r2-triple r1-triple L2)

  (test-case "Extend metafunction one level down."
    (check-equal? (apply-rr r0-triple 0) (set 1))
    (check-equal? (apply-rr r1-triple "hi") (set 1))
    (check-equal? (apply-rr r2-triple #t) (set 17))))
