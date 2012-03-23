#lang racket

(require redex)
(provide (all-defined-out))

(define-language λmath
  (c ÷ plus1)
  (v (λ (x) e) number)
  (e v x (err ω) (e e) (c e))
  (ω div-0 div-λ add-λ app-n app-0)
  (E hole (E e) (v E) (c E))
  ((f g x y z) variable-not-otherwise-mentioned))

(define-metafunction λmath
  subst : x v any -> any
  [(subst x v x) v]
  [(subst x v y) y]
  [(subst x v (λ (x) e)) (λ (x) e)]
  [(subst x v (λ (y) e)) (λ (y) (subst x v e))]
  [(subst x v (c e)) (c (subst x v e))]
  [(subst x v number) number]
  [(subst x v (err ω)) (err ω)]
  [(subst x v (e_1 e_2)) ((subst x v e_1) (subst x v e_2))])

(define-metafunction λmath
  δ : c v -> any
  [(δ ÷ 0) (err div-0)]
  [(δ ÷ number) ,(/ 1 (term number))]
  [(δ ÷ (λ (x) e)) (err div-λ)]
  [(δ ÷ c) (err div-c)]

  [(δ plus1 number) ,(add1 (term number))]
  [(δ plus1 (λ (x) e)) (err div-λ)]
  [(δ plus1 c) (err div-c)])

(define-metafunction λmath
  fv : e (x ...) -> (x ...)
  [(fv number (x ...)) ()]
  [(fv (err ω) (x ...)) ()]
  [(fv (c e) (x ...)) (fv e (x ...))]
  [(fv x_1 (x_2 ...)) (x_1)
    (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  [(fv x_1 (x_2 ...)) ()]
  [(fv (λ (x) e) (x_1 ...))
    (fv e (x x_1 ...))]
  [(fv (e_1 e_2) (x ...))
    (join (fv e_1 (x ...)) (fv e_2 (x ...)))])

(define-metafunction λmath
  join : (x ...) ... -> (x ...)
  [(join) ()]
  [(join (x_1 ...)) (x_1 ...)]
  [(join (x_1 ...) (x_2 ...) (x_3 ...) ...)
   (join (x_1 ...   x_2 ...) (x_3 ...) ...)])

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

