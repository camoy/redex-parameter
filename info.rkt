#lang info
(define collection 'multi)
(define deps '("base"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define scribblings '(("scribblings/redex-parameter.scrbl" ())))
(define pkg-desc "Support for parameterized reduction relations in Redex.")
(define version "0.0")
(define pkg-authors '(camoy))
