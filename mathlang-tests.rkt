#lang racket

(require redex)
(require "mathlang.rkt")

(define id (term ((λ (x) x) 4)))
(define four (term 4))

(test--> eval-λmath id four)

(define appn (term (5 5)))
(define errappn (term (err app-n)))

(test--> eval-λmath appn errappn)

(define app0 (term (0 5)))
(define errapp0 (term (err app-0)))

(test--> eval-λmath app0 errapp0)

(define (check-term e)
  (or (not (empty? ((term-match λmath
                      [(err ω) #t]
                      [v #t]) e)))
      (not (empty? (apply-reduction-relation eval-λmath e)))))


(check-reduction-relation eval-λmath check-term
  #:attempts 6000
  ;; just give a plain value if it generates something initially
  ;; containing a free variable
  #:prepare
  (λ (e)
    (let ([vars (term (fv ,e ()))])
      (if (not (empty? vars))
            (foldr (λ (x e)
              (term (subst ,x ,(generate-term λmath prim 5) ,e)))
              e vars)
          e))))
  
  
