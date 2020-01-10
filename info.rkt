#lang info
(define collection "redex")
(define deps '("base"))
(define build-deps
  '("scribble-lib"
    "racket-doc"
    "rackunit-lib"
    "redex-lib"
    "redex-doc"
    "sandbox-lib"))
(define scribblings '(("scribblings/redex-parameter.scrbl" ())))
(define pkg-desc "Parameterized reduction relations in Redex.")
(define version "0.0")
(define pkg-authors '(camoy))
