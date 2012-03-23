#lang racket

(require redex)
(require "mathtypes.rkt")

(define harper (term (μ α (N ∪ (Z ∪ (α → ,Ω* α))))))

(define BADTYPES 0)
(define (check-subtype τ)
  (if (not (term (wf-type () ,τ)))
      (begin (set! BADTYPES (add1 BADTYPES)) #t)
      (term (subtype ,τ ,univ))))

(redex-check λmathτ τ (check-subtype (term τ)) #:attempts 10000)
(display (format "There were ~a ill-formed types\n" BADTYPES))

