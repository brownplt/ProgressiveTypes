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

(define (check-term e)
  (let ([typs (with-handlers
          [(exn:fail:redex?
            (λ (err) (display (format "Failed: ~a\n (~a)\n" e err)) '()))]
          (judgment-holds (type ,Ω* () ,e τ) τ))])
    (if (= (length typs) 0)
      (display (format "No types: ~a\n" e))
      (begin
        (display (format "Got some typs: ~a : ~a\n" e typs))
        (or
          (if (not (empty? ((term-match λmathτ
                            [(err ω) #t]
                            [v #t])
                            e)))
                #t
                (begin
                  (display (format "Wasn't err or value: ~a\n" e))
                  #f))
          (let ([step (apply-reduction-relation eval-λmathτ e)])
            (and
              (check-length step 1 "Exprs")
              (display (format "Rewritten: ~a\n" step))
              (let ([newtyps (judgment-holds (type ,Ω* () ,(first step) τ) τ)])
                (display (format "After step, typed to: ~a\n" newtyps))
                (check-length newtyps 1 "Types2")
                (term (subtype ,(first newtyps) ,(first typs)))))))))))

(define (calculate-argtyp) (term N))

(define-metafunction λmathτ
  repair-applications : Γ e -> e
  [(repair-applications Γ number) number]
  [(repair-applications Γ (c e)) (c (repair-applications e))]
  [(repair-applications Γ (λ (x τ Ω) e))
   (λ (x τ Ω) (repair-applications (extend-Γ Γ x τ) e))]
  [(repair-applications x) x]
  [(repair-applications ((λ (x τ Ω) e_1) e_2))
   ((λ (x ,(calculate-argtyp (term τ) (term e_1)) Ω)
      (repair-applications e_1))
    (repair-applications e_2))]
  [(repair-applications (e_1 e_2))
   ((repair-applications e_1) (repair-applications e_2))])

#;(check-reduction-relation eval-λmathτ check-term
  #:attempts 1000
  ;; just give a plain value if it generates something initially
  ;; containing a free variable
  #:prepare
  (λ (e)
    (let* ([vars (term (fvτ ,e ()))]
           [newterm
            (foldr (λ (x e)
              (term (substτ ,x ,(generate-term λmathτ number 5) ,e)))
              e vars)])
      (term ,newterm))))

(define (uniq l) (set->list (apply set l)))

(define-metafunction λmathτ
  error-τruncate : τ -> τ
  [(error-τruncate N) N]
  [(error-τruncate Z) Z]
  [(error-τruncate ⊥) ⊥]
  [(error-τruncate x) x]

  [(error-τruncate (μ x τ)) (μ x (error-τruncate τ))]

  [(error-τruncate (τ_1 → Ω τ_2))
   ((error-τruncate τ_1) → ,(uniq (term Ω))
    (error-τruncate τ_2))]

  [(error-τruncate (τ_1 ∪ τ_2))
   ((error-τruncate τ_1) ∪ (error-τruncate τ_2))])

(define-metafunction λmathτ
  error-truncate : e -> e
  [(error-truncate number) number]
  [(error-truncate (c e)) (c (error-truncate e))]
  [(error-truncate (e_1 e_2)) ((error-truncate e_1) (error-truncate e_2))]
  [(error-truncate (err ω)) (err ω)]
  [(error-truncate x) x]
  [(error-truncate (λ (x τ Ω) e))
   (λ (x (error-τruncate τ) ,(uniq (term Ω))) (error-truncate e))])

(redex-check λmathτ ((λ (x τ Ω) e) v_2)
    (check-term (term ((λ (x τ Ω) e) v_2)))
  #:attempts 10000
  #:attempt-size (λ (s) (inexact->exact (ceiling (sqrt s))))
  #:print? #t
  ;; just give a plain value if it generates something initially
  ;; containing a free variable
  #:prepare
  (λ (e)
    (let* ([vars (term (fvτ ,e ()))]
           [newterm
            (foldr (λ (x e)
              (term (substτ ,x ,(generate-term λmathτ number 5) ,e)))
              e vars)])
      (term (error-truncate ,newterm)))))

