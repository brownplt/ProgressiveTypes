#lang racket

(require redex)
(require srfi/1)
(require "mathlang.rkt")
(provide (all-defined-out))

(define-extended-language λmathτ λmath
  (v (λ (x τ Ω) e) prim)
  (τ Z N (τ ∪ τ) ⊥ ⊤ σ)
  (σ (σ ∩ σ) (τ → Ω τ))
  (Γ ((x τ) ...))
  (Ω (ω ...)))

(define eval-λmathτ
  (extend-reduction-relation eval-λmath λmathτ
    (==> ((λ (x τ Ω) e) v) (substτ x v e) "βv")
    (==> (c v) (δτ c v) "δ")
   with
    [(--> (in-hole E e_1) (in-hole E e_2))
     (==> e_1 e_2)]))

(define-metafunction/extension fv λmathτ
  fvτ : e (x ...) -> (x ...)
  [(fvτ (λ (x τ Ω) e) (y ...))
   (fvτ e (x y ...))]
  [(fvτ (e_1 e_2) (x ...))
    (join (fvτ e_1 (x ...)) (fvτ e_2 (x ...)))])

(define-metafunction/extension subst λmathτ
  substτ : x v any -> any
  [(substτ x v (λ (x τ Ω) e)) (λ (x τ Ω) e)]
  [(substτ x v (λ (y τ Ω) e)) (λ (y τ Ω) (substτ x v e))]
  [(substτ x v (e_1 e_2)) ((substτ x v e_1) (substτ x v e_2))])

(define-metafunction/extension δ λmathτ
  δτ : c v -> any
  [(δτ ÷ (λ (x τ Ω) e)) (err div-λ)]
  [(δτ +1 (λ (x τ Ω) e)) (err div-λ)])

(define-judgment-form λmathτ
  ;; Three inputs: Ω, Γ, e, and yields a type τ
  #:mode (type I I I O)
  [(type Ω Γ 0 Z)]
  [(type Ω Γ (side-condition number (not (= 0 (term number)))) N)]
  [(type Ω Γ x (lookup-Γ Γ x))]
  [(type Ω_1 Γ (λ (x τ_1 Ω_2) e) (τ_1 → Ω_2 τ_2))
   (type Ω_2 (extend-Γ Γ x τ_1) e τ_2)]
  [(type Ω Γ (e_1 e_2) (appli τ_1 τ_2 Ω))
   (type Ω Γ e_1 τ_1) (type Ω Γ e_2 τ_2)])

(define-metafunction λmathτ
  appli : τ τ Ω -> τ
  [(appli ⊥ τ Ω) ⊥]
  [(appli τ ⊥ Ω) ⊥]

  [(appli (τ_1 ∪ τ_2) τ_3 Ω)
   ((appli τ_1 τ_3 Ω) ∪ (appli τ_2 τ_3 Ω))]

  [(appli (τ_1 → Ω_2 τ_2) τ_1 Ω_1)
   τ_2
   ;; inclusion by Racket lists
   (side-condition
      (every (λ (ω) (member ω (term Ω_1))) (term Ω_2)))]

  [(appli Z τ Ω) ⊥
   (side-condition (member (term app-0) (term Ω)))]
  [(appli N τ Ω) ⊥
   (side-condition (member (term app-N) (term Ω)))])

(define-metafunction λmathτ
  lookup-Γ : Γ x -> τ
  [(lookup-Γ ((x τ) (y τ_2) ...) x) τ]
  [(lookup-Γ ((y τ_1) (z τ_2)...) x) 
   (lookup-Γ ((z τ_2) ...) x)
   (side-condition (not (equal? (term x) (term y))))])

(define-metafunction λmathτ
  extend-Γ : Γ x τ -> Γ
  [(extend-Γ ((y τ_1) ...) x τ_2) ((x τ_2) (y τ_1) ...)])

