#lang racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; require

(require redex/reduction-semantics
         redex/parameter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test

(module+ test
  (require (for-syntax racket/base)
           (submod "parameter.rkt" test)
           chk
           racket/set)

  ;;
  ;; Reduction Relation (extended)
  ;;

  (define-extended-metafunction* foo-mf0 L1
    foo-mf1 : m -> m
    [(foo-mf1 m) 1.75])

  (define-extended-judgment-form* foo-jf0 L1
    #:mode (foo-jf1 I O)
    [(foo-jf1 m 1.75)])

  (define-extended-reduction-relation* r1.75-mf r0-mf L1)
  (define-extended-reduction-relation* r1.75-jf r0-jf L1)
  (define-extended-reduction-relation* r1.75-rr r0-rr L1)

  (chk
   (apply-reduction-relation r1.75-mf (term "foo")) '(1.75)
   #:eq set=? (apply-reduction-relation r1.75-jf (term "foo")) '(0 1.75)
   (apply-reduction-relation r1.75-rr (term "foo")) '(1.75)
   ))
