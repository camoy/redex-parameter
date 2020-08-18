#lang info

;; General

(define collection "redex")
(define pkg-desc "Extension parameters in Redex.")
(define version "0.0")
(define pkg-authors '(camoy))
(define scribblings '(("scribblings/redex-parameter.scrbl" ())))
(define compile-omit-paths '("test"))

;; Dependencies

(define deps
  '("base"
    "redex-lib"))

(define build-deps
  '("chk-lib"
    "scribble-lib"
    "racket-doc"
    "rackunit-lib"
    "redex-doc"
    "sandbox-lib"))
