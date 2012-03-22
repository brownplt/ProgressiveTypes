#lang racket

;; TODO
;; - δτ to give back the intersections
;; - subsumption (probably explicit expr)

(require redex)
(require srfi/1)
(require "mathlang.rkt")
(provide (all-defined-out))

;; TODO(joe): investigate why α and (variable-not-otherwise-mentioned)
;; behave strangely, requiring use of x for type idents
(define-extended-language λmathτ λmath
  (v (λ (x τ Ω) e) prim)
  (τ Z N (τ ∪ τ) ⊥ (μ x τ) x σ)
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

(define-relation λmathτ
  subtype ⊆ τ × τ
  [(subtype τ_1 τ_2) (subtype-c () τ_1 τ_2)])

(define-relation λmathτ
  ;; Three inputs: cache, and two types
  subtype-c ⊆ ((τ τ) ...) × τ × τ
  ;; subtyping succeeds for elements that match in the cache
  [(subtype-c ((τ_1 τ_2) ... (τ_i τ_j) (τ_m τ_n) ...) τ_i τ_j)]

  ;; S-Refl
  [(subtype-c any τ τ)]

  ;; S-Bot
  [(subtype-c any ⊥ τ)]

  ;; S-Fold
  [(subtype-c ((τ_1 τ_2) ...) (μ x τ_3) τ_4)
   (subtype-c (((μ x τ_3) τ_4) (τ_1 τ_2) ...)
              (typ-subst x (μ x τ_3) τ_3)
              τ_4)]

  ;; S-Unfold
  [(subtype-c ((τ_1 τ_2) ...) τ_3 (μ x τ_4))
   (subtype-c ((τ_3 (μ x τ_4)) (τ_1 τ_2) ...)
              τ_3
              (typ-subst x (μ x τ_4) τ_4))]

  ;; S-Union-L
  [(subtype-c ((τ_1 τ_2) ...) τ_L (τ_R1 ∪ τ_R2))
   (subtype-c ((τ_L (τ_R1 ∪ τ_R2)) (τ_1 τ_2) ...) τ_L τ_R1)]

  ;; S-Union-R
  [(subtype-c ((τ_1 τ_2) ...) τ_L (τ_R1 ∪ τ_R2))
   (subtype-c ((τ_L (τ_R1 ∪ τ_R2)) (τ_1 τ_2) ...) τ_L τ_R2)]

  ;; S-Union-Join
  [(subtype-c ((τ_1 τ_2) ...) (τ_L1 ∪ τ_L2) τ_R)
   (subtype-c (((τ_L1 ∪ τ_L2) τ_R) (τ_1 τ_2) ...) τ_L1 τ_R)
   (subtype-c (((τ_L1 ∪ τ_L2) τ_R) (τ_1 τ_2) ...) τ_L2 τ_R)]

  ;; S-Inter-L
  [(subtype-c ((τ_1 τ_2) ...) (τ_L1 ∩ τ_L2) τ_R)
   (subtype-c (((τ_L1 ∩ τ_L2) τ_R) (τ_1 τ_2) ...) τ_L1 τ_R)]

  ;; S-Inter-R
  [(subtype-c ((τ_1 τ_2) ...) (τ_L1 ∩ τ_L2) τ_R)
   (subtype-c (((τ_L1 ∩ τ_L2) τ_R) (τ_1 τ_2) ...) τ_L2 τ_R)]
  
  ;; S-Inter-Join
  [(subtype-c ((τ_1 τ_2) ...) τ_L (τ_R1 ∩ τ_R2))
   (subtype-c ((τ_L (τ_R1 ∩ τ_R2)) (τ_1 τ_2) ...) τ_L τ_R1)
   (subtype-c ((τ_L (τ_R1 ∩ τ_R2)) (τ_1 τ_2) ...) τ_L τ_R2)]

  ;; S-Arrow
  [(subtype-c ((τ_i τ_j) ...) (τ_1 → Ω_1 τ_2) (τ_3 → Ω_2 τ_4))
   (subtype-c (((τ_1 → Ω_1 τ_2) (τ_3 → Ω_2 τ_4)) (τ_i τ_j) ...)
              τ_2 τ_4)
   (subtype-c (((τ_1 → Ω_1 τ_2) (τ_3 → Ω_2 τ_4)) (τ_i τ_j) ...)
              τ_3 τ_1)
   ;; inclusion by Racket lists
   (side-condition
      (every (λ (ω) (member ω (term Ω_1))) (term Ω_2)))]

  ;; S-Inter-Arrow
  [(subtype-c any
              ((τ_1 → Ω τ) ∩ (τ_2 → Ω τ))
              ((τ_1 ∪ τ_2) → Ω τ))]

  ;; S-Inter-Arrow2
  ;; Trying more algorithmic versions (going off the rails?)
  [(subtype-c any
              ((τ_1 → (ω_1 ...) τ_3) ∩ (τ_2 → (ω_2 ...) τ_4))
              ((τ_1 ∪ τ_2) → (ω_1 ... ω_2 ...) (τ_3 ∪ τ_4)))]

  ;; S-Inter-Arrow3
  [(subtype-c ((τ_i τ_j) ...)
              ((τ_1 → (ω_1 ...) τ_3) ∩ (τ_2 → (ω_2 ...) τ_4))
              ((τ_1 ∪ τ_2) → (ω_1 ... ω_2 ...) τ_3))
   (subtype-c ((((τ_1 → (ω_1 ...) τ_3) ∩ (τ_2 → (ω_2 ...) τ_4))
                ((τ_1 ∪ τ_2) → (ω_1 ... ω_2 ...) τ_3))
               (τ_i τ_j) ...)
              τ_4 τ_3)]
                
  ;; S-Inter-Arrow4
  [(subtype-c ((τ_i τ_j) ...)
              ((τ_1 → (ω_1 ...) τ_3) ∩ (τ_2 → (ω_2 ...) τ_4))
              ((τ_1 ∪ τ_2) → (ω_1 ... ω_2 ...) τ_4))
   (subtype-c ((((τ_1 → (ω_1 ...) τ_3) ∩ (τ_2 → (ω_2 ...) τ_4))
                ((τ_1 ∪ τ_2) → (ω_1 ... ω_2 ...) τ_3))
               (τ_i τ_j) ...)
              τ_3 τ_4)]

)

(define-relation λmathτ
  ;; Variables seen and a type
  wf-type ⊆ (x ...) × τ
  [(wf-type (x ...) N)]
  [(wf-type (x ...) Z)]
  [(wf-type (x ...) ⊥)]

  [(wf-type (x_1 ... x_i x_n ...) x_i)]

  [(wf-type (x ...) (μ y (τ_1 → Ω τ_2)))
   (wf-type (y x ...) τ_1)
   (wf-type (y x ...) τ_2)]
  [(wf-type (x ...) (μ y (τ_1 ∪ τ_2)))
   (wf-type (y x ...) τ_1)
   (wf-type (y x ...) τ_2)]
  [(wf-type (x ...) (μ y (τ_1 ∩ τ_2)))
   (wf-type (y x ...) τ_1)
   (wf-type (y x ...) τ_2)]
  [(wf-type (x ...) (μ y (μ z τ)))
   (wf-type (y x ...) (μ z τ))]

  [(wf-type (x ...) (τ_1 → Ω τ_2))
   (wf-type (x ...) τ_1)
   (wf-type (x ...) τ_2)]
  [(wf-type (x ...) (τ_1 ∪ τ_2))
   (wf-type (x ...) τ_1)
   (wf-type (x ...) τ_2)]
  [(wf-type (x ...) (τ_1 ∩ τ_2))
   (wf-type (x ...) τ_1)
   (wf-type (x ...) τ_2)])
  

(define-metafunction λmathτ
  typ-subst : x τ τ -> τ
  [(typ-subst x τ N) N]
  [(typ-subst x τ Z) Z]
  [(typ-subst x τ ⊥) ⊥]

  [(typ-subst x τ x) τ]
  [(typ-subst x_1 τ x_2) x_2]

  [(typ-subst x τ_1 (μ x τ_2)) (μ x τ_2)]
  [(typ-subst x_1 τ_1 (μ x_2 τ_2))
   (μ x_2 (typ-subst x_1 τ_1 τ_2))]

  [(typ-subst x τ_1 (τ_2 → Ω τ_3))
   ((typ-subst x τ_1 τ_2) → Ω (typ-subst x τ_1 τ_3))]

  [(typ-subst x τ_1 (τ_2 ∪ τ_3))
   ((typ-subst x τ_1 τ_2) ∪ (typ-subst x τ_1 τ_3))]
  [(typ-subst x τ_1 (τ_2 ∩ τ_3))
   ((typ-subst x τ_1 τ_2) ∩ (typ-subst x τ_1 τ_3))])

