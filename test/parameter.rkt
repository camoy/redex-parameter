#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; require

(require redex/reduction-semantics
         redex/parameter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test

(module+ test
  (provide L0 L1
           (redex-out foo-mf0 foo-jf0
                      r0-mf r0-jf r0-rr))

  (require chk
           racket/set)

  ;;
  ;; Languages
  ;;

  (define-language L0
    [m ::= number])

  (define-language L1
    [m ::= number string])

  ;;
  ;; Reduction Relations
  ;;

  ;; This is to make sure that locally-defined identifiers are correctly
  ;; exported.
  (define (identity x) x)

  (define-metafunction* L0
    foo-mf0 : m -> m
    [(foo-mf0 m) ,(identity 0)])

  (define-judgment-form* L0
    #:mode (foo-jf0 I O)
    [(foo-jf0 m 0)])

  (define-reduction-relation* r0-mf
    L0
    #:parameters ([foo-mf foo-mf0])
    [--> m (foo-mf m)])

  (define-reduction-relation* r0-jf
    L0
    #:parameters ([foo-jf foo-jf0])
    [--> m_1 m_2 (judgment-holds (foo-jf m_1 m_2))])

  (define-reduction-relation* r0-rr
    L0
    #:parameters ([r r0-mf])
    [--> m_1 m_2
         (where (_ ... m_2 _ ...)
                ,(apply-reduction-relation r (term m_1)))])

  (chk
   (apply-reduction-relation r0-mf (term 42)) '(0)
   (apply-reduction-relation r0-jf (term 42)) '(0)
   (apply-reduction-relation r0-rr (term 42)) '(0)
   )

  ;;
  ;; Reduction Relation (lifted)
  ;;

  (define-extended-reduction-relation* r1-mf r0-mf L1)
  (define-extended-reduction-relation* r1-jf r0-jf L1)
  (define-extended-reduction-relation* r1-rr r0-rr L1)

  (chk
   (apply-reduction-relation r1-mf (term "foo")) '(0)
   (apply-reduction-relation r1-jf (term "foo")) '(0)
   (apply-reduction-relation r1-rr (term "foo")) '(0)
   )

  ;;
  ;; Reduction Relation (extended)
  ;;

  (define-extended-metafunction* foo-mf0 L1
    foo-mf1 : m -> m
    [(foo-mf1 m) 1.5])

  (define-extended-judgment-form* foo-jf0 L1
    #:mode (foo-jf1 I O)
    [(foo-jf1 m 1.5)])

  (define-extended-reduction-relation* r1.5-mf r0-mf L1)
  (define-extended-reduction-relation* r1.5-jf r0-jf L1)
  (define-extended-reduction-relation* r1.5-rr r0-rr L1)

  (chk
   (apply-reduction-relation r1.5-mf (term "foo")) '(1.5)
   #:eq set=? (apply-reduction-relation r1.5-jf (term "foo")) '(0 1.5)
   (apply-reduction-relation r1.5-rr (term "foo")) '(1.5)
   )

  ;;
  ;; Judgment Form
  ;;

  (define-metafunction* L0
    bar-mf0 : m -> m
    [(bar-mf0 m) 0])

  (define-judgment-form* L0
    #:parameters ([bar-mf bar-mf0])
    #:mode (bar-jf0 I O)
    [(bar-jf0 m (bar-mf m))])

  (define-extended-judgment-form* bar-jf0 L1
    #:mode (bar-jf1 I O))

  (chk
   #:t (judgment-holds (bar-jf0 0 0))
   #:t (judgment-holds (bar-jf1 "bar" 0))
   ))
