#lang racket

(require redex)
(provide (all-defined-out))

(define-language λmath
  (prim number c)
  (v (λ (x) e) prim)
  (c ÷ +1)
  (e v x (err ω) (e e))
  (ω div-0 div-λ div-c add-λ add-c app-n app-0)
  (E hole (E e) (v E))
  ((f g x y z) variable-not-otherwise-mentioned))

(define-metafunction λmath
  subst : x v any -> any
  [(subst x v x) v]
  [(subst x v y) y]
  [(subst x v (λ (x) e)) (λ (x) e)]
  [(subst x v (λ (y) e)) (λ (x) (subst x v e))]
  [(subst x v c) c]
  [(subst x v number) number]
  [(subst x v (err ω)) (err ω)]
  [(subst x v (e_1 e_2)) ((subst x v e_1) (subst x v e_2))])

(define-metafunction λmath
  δ : c v -> any
  [(δ ÷ 0) (err div-0)]
  [(δ ÷ number) (/ 1 (term number))]
  [(δ ÷ (λ (x) e)) (err div-λ)]
  [(δ ÷ c) (err div-c)]

  [(δ +1 number) (add1 (term number))]
  [(δ +1 (λ (x) e)) (err div-λ)]
  [(δ +1 c) (err div-c)])

(define-metafunction λmath
  fv : e (x ...) -> (x ...)
  [(fv number (x ...)) ()]
  [(fv (err ω) (x ...)) ()]
  [(fv c (x ...)) ()]
  [(fv x_1 (x_2 ...)) (x_1)
    (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  [(fv x_1 (x_2 ...)) ()]
  [(fv (λ (x) e) (x_1 ...))
    (fv e (x x_1 ...))]
  [(fv (e_1 e_2) (x ...))
    (∪ (fv e_1 (x ...)) (fv e_2 (x ...)))])

(define-metafunction λmath
  ∪ : (x ...) ... -> (x ...)
  [(∪) ()]
  [(∪ (x_1 ...)) (x_1 ...)]
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...)
   (∪ (x_1 ...   x_2 ...) (x_3 ...) ...)])

(define eval-λmath
  (reduction-relation λmath
    (==> ((λ (x) e) v) (subst x v e) "βv")
    (==> (number v) (err app-n) "βn"
         (side-condition (not (= (term number) 0))))
    (==> (0 v) (err app-0) "β0")
    (==> (c v) (δ c v) "δ")

    (--> (in-hole E (err ω)) (err ω))

   with
    [(--> (in-hole E e_1) (in-hole E e_2))
     (==> e_1 e_2)]))


