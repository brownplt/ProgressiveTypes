#lang racket

(require redex)
(require rackunit)
(require "mathtypes.rkt")

(define Ω* (term (div-0 div-λ add-λ app-n app-0)))
(define harper (term (μ α (N ∪ (Z ∪ (α → ,Ω* α))))))

(define (check-length typs n m)
  (if (not (= (length typs) n))
      (begin
        (display (format "~a; Wrong number of things: ~a != ~a\n" m typs n)) #f)
      #t))

(define ((check-termτ rr) e)
  (display (format "Checking ~a\n" e))
  (let ([typs (judgment-holds (type ,Ω* () ,e τ) τ)])
    (display (format "typed to ~a\n" typs))
    (and
      (check-length typs 1 "Types")
      (or (if (not (empty? ((term-match λmathτ
                          [(err ω) #t]
                          [v #t])
                          e)))
              #t
              (begin
                (display (format "Wasn't err or value: ~a\n" e))
                #f))
          (let ([step (apply-reduction-relation rr e)])
            (and
              (check-length step 1 "Exprs")
              (display (format "Rewritten: ~a\n" step))
              (let ([newtyps (judgment-holds (type ,Ω* () ,(first step) τ) τ)])
                (display (format "After step, typed to: ~a\n" newtyps))
                (check-length newtyps 1 "Types2")
                (term (subtype ,(first newtyps) ,(first typs))))))))))

(define-metafunction λmathτ
  harperize : e -> e
  [(harperize number) number]
  [(harperize (c e)) (c (harperize e))]
  [(harperize (e_1 e_2)) ((harperize e_1) (harperize e_2))]
  [(harperize (err ω)) (err ω)]
  [(harperize x) x]
  [(harperize (λ (x τ Ω) e))
   (λ (x ,harper ,Ω*) (harperize e))])

(check-reduction-relation eval-λmathτ (check-termτ eval-λmathτ)
  #:attempts 10000
  ;; just give a plain value if it generates something initially
  ;; containing a free variable
  #:prepare
  (λ (e)
    (let* ([vars (term (fvτ ,e ()))]
           [newterm
            (foldr (λ (x e)
              (term (substτ ,x ,(generate-term λmathτ number 5) ,e)))
              e vars)])
      (term (harperize ,newterm)))))
      

