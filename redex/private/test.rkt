#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require "../parameter.rkt"
         (for-syntax racket/base)
         redex/reduction-semantics
         rackunit
         syntax/macro-testing
         racket/set)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (apply-rr . xs)
  (apply set (apply apply-reduction-relation xs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; L0

(define-language L0
  [m ::= number])

(define-metafunction L0
  [(foo-mf m) 1])

(define-judgment-form L0
  #:mode (foo-jf I O)
  [(foo-jf m 1)])

(define-reduction-relation r0-mf
  L0
  #:parameters (foo-mf)
  [--> m (foo-mf m)])

(define-reduction-relation r0-jf
  L0
  #:parameters (foo-jf)
  [--> m_1 m_2 (judgment-holds (foo-jf m_1 m_2))])

(test-case "Normal functioning."
  (check-equal? (apply-rr r0-mf (term 0)) (set 1))
  (check-equal? (apply-rr r0-jf (term 0)) (set 1)))

(define-metafunction L0
  [(bar-mf m) 2])

(define-judgment-form L0
  #:mode (bar-jf I O)
  [(bar-jf m 2)])

(test-case "Explicit parameterization."
  (check-equal? (apply-rr (r0-mf [foo-mf bar-mf]) (term 0)) (set 2))
  (check-equal? (apply-rr (r0-jf [foo-jf bar-jf]) (term 0)) (set 2)))

(test-case "Explicit parameterization failures."
  (check-exn
   #rx"invalid parameter"
   (λ () (convert-syntax-error (apply-rr (r0-mf [oops-mf bar-mf]) (term 0)))))

  (check-exn
   #rx"duplicate parameter"
   (λ ()
     (convert-syntax-error (apply-rr (r0-mf [foo-mf bar-mf]
                                            [foo-mf bar-mf])
                                     (term 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; L1

(define-extended-language L1 L0
  [m ::= .... string])

(define-extended-reduction-relation r1-mf
  r0-mf L1
  [--> m 13])

(define-extended-reduction-relation r1-jf
  r0-jf L1
  [--> m 13])

(test-case "Normal extension."
  (check-equal? (apply-rr r1-mf (term 0)) (set 1 13))
  (check-equal? (apply-rr r1-jf (term 0)) (set 1 13)))

(test-case "Extension with implicit lifting."
  (check-equal? (apply-rr r1-mf (term "hi")) (set 1 13))
  (check-equal? (apply-rr r1-jf (term "hi")) (set 1 13)))

(test-case "Explicit parameterization of an extension."
  (check-equal? (apply-rr (r1-mf [foo-mf bar-mf]) (term 0)) (set 2 13))
  (check-equal? (apply-rr (r1-jf [foo-jf bar-jf]) (term 0)) (set 2 13)))

(define-metafunction L1
  [(foo-mf* m) 3])

(define-judgment-form L1
  #:mode (foo-jf* I O)
  [(foo-jf* m 3)])

(define-extended-reduction-relation r1-mf*
  r0-mf L1 #:parameters (foo-mf*)
  [--> m (foo-mf* m)])

(define-extended-reduction-relation r1-jf*
  r0-jf L1 #:parameters (foo-jf*)
  [--> m_1 m_2 (judgment-holds (foo-jf* m_1 m_2))])

(test-case "Normal extension with new parameter."
  (check-equal? (apply-rr r1-mf* (term 0)) (set 1 3))
  (check-equal? (apply-rr r1-jf* (term 0)) (set 1 3)))

(test-case "Explicit parameterization of an new parameter."
  (check-equal? (apply-rr (r1-mf* [foo-mf* bar-mf]) (term 0)) (set 1 2))
  (check-equal? (apply-rr (r1-jf* [foo-jf* bar-jf]) (term 0)) (set 1 2))
  (check-equal? (apply-rr (r1-mf* [foo-mf bar-mf] [foo-mf* bar-mf]) (term 0))
                (set 2))
  (check-equal? (apply-rr (r1-jf* [foo-jf bar-jf] [foo-jf* bar-jf]) (term 0))
                (set 2)))

(define-extended-metafunction foo-mf L1
  [(foo-mf** m) 4])

(define-extended-judgment foo-jf L1
  #:mode (foo-jf** I O)
  [(foo-jf** m 4)])

(define-extended-reduction-relation r1-mf**
  r0-mf L1
  [--> m (foo-mf** m)])

(define-extended-reduction-relation r1-jf**
  r0-jf L1
  [--> m_1 m_2 (judgment-holds (foo-jf** m_1 m_2))])

(test-case "Normal extension with parameter from extension."
  (check-equal? (apply-rr r1-mf** (term 0)) (set 4))
  (check-equal? (apply-rr r1-jf** (term 0)) (set 1 4)))

(test-case "Explicit parameterization with old name."
  (check-exn
   #rx"invalid parameter"
   (λ () (convert-syntax-error
          (apply-rr (r1-mf** [foo-mf bar-mf]) (term 0))))))

(test-case "Explicit parameterization with parameter from extension."
  (check-equal? (apply-rr (r1-mf** [foo-mf** bar-mf]) (term 0)) (set 2))
  (check-equal? (apply-rr (r1-jf** [foo-jf** bar-jf]) (term 0)) (set 2)))

(define-reduction-relation r0-rename-mf
  L0 #:parameters (bar-mf) [--> m (bar-mf m)])

(define-syntax bar-rename (make-rename-transformer #'bar-mf))

(define-extended-reduction-relation r1-rename-mf
  r0-rename-mf L1 #:parameters (bar-rename))

(test-case "Explicit parameterization with old name."
  (check-exn
   #rx"invalid parameter"
   (λ () (convert-syntax-error
          (apply-rr (r1-rename-mf [bar-mf foo-mf]) (term 0))))))

(test-case "Parameter that is free-identifier=? existing one."
  (check-equal? (apply-rr (r1-rename-mf [bar-rename foo-mf]) (term 0))
                (set 1)))
