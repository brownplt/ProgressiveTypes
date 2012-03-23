#lang racket

(require redex)
(require "mathtypes.rkt")

(define Ω* '(div-0 div-0 div-λ add-λ app-n app-0))
(define univ (term (μ α (N ∪ (Z ∪ (⊥ → ,Ω* α))))))

(define BADTYPES 0)
(define (check-subtype τ)
  (if (not (term (wf-type () ,τ)))
      (begin (set! BADTYPES (add1 BADTYPES)) #t)
      (term (subtype ,τ ,univ))))

(redex-check λmathτ τ (check-subtype (term τ)) #:attempts 10000)
(display (format "There were ~a ill-formed types\n" BADTYPES))

