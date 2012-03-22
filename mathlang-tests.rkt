#lang racket

(require redex)
(require rackunit)
(require "mathlang.rkt")
(require "mathtypes.rkt")

(define id (term ((λ (x) x) 4)))
(define four (term 4))

(test--> eval-λmath id four)

(define appn (term (5 5)))
(define errappn (term (err app-n)))

(test--> eval-λmath appn errappn)

(define app0 (term (0 5)))
(define errapp0 (term (err app-0)))

(test--> eval-λmath app0 errapp0)

(define ((check-term rr) e)
  (or (not (empty? ((term-match λmath
                      [(err ω) #t]
                      [v #t]) e)))
      (not (empty? (apply-reduction-relation rr e)))))


#;(check-reduction-relation eval-λmath (check-term eval-λmath)
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

(check-equal? (judgment-holds (type () () 5 τ) τ) (list (term N)))
(check-true (judgment-holds (type () () 0 Z)))

(check-true (judgment-holds (type () ((x N)) x N)))
(check-true (judgment-holds (type () ((y Z) (x N)) x N)))
(check-true (judgment-holds (type () ((x N) (y Z)) x N)))
(check-exn #rx"lookup-Γ: no clauses"
  (λ () (judgment-holds (type () ((y Z)) x N))))

(check-equal? (judgment-holds
  (type () () (λ (x N (div-0)) 0) τ) τ)
  (list (term (N → (div-0) Z))))

(check-equal? (judgment-holds
  (type (app-0) () (0 0) τ) τ)
  (list (term ⊥)))

(check-exn #rx"appli: no clauses"
  (λ () (judgment-holds (type () () (3 0) τ) τ)))

(check-equal? (judgment-holds
  (type (app-0) ((f (N → (app-0) Z))) (f 4) τ) τ)
  (list (term Z)))

(check-equal? (judgment-holds
  (type (app-0 app-n) ((f (N → (app-0) N))) (f 4) τ) τ)
  (list (term N)))

(check-exn #rx"appli: no clauses"
  (λ () (judgment-holds
  (type (app-n) ((f (N → (app-0) N))) (f 4) τ) τ)))

(check-equal? (term (typ-subst somevar N somevar)) (term N))
(check-equal? (term (typ-subst somevar N anothervar)) (term anothervar))
(check-equal? (term (typ-subst somevar Z N)) (term N))
(check-equal? (term (typ-subst α Z (α → (div-0) N)))
              (term (Z → (div-0) N)))
(check-equal? (term (typ-subst α Z (μ β (β → () α))))
              (term (μ β (β → () Z))))
(check-equal? (term (typ-subst α Z (μ α (α → () α))))
              (term (μ α (α → () α))))


(check-false (term (wf-type () (μ α α))))
(check-false (term (wf-type () α)))
(check-false (term (wf-type () (μ α (μ β α)))))
(check-false (term (wf-type () (μ α (N ∪ (μ β α))))))

(check-true (term (wf-type () (μ α (μ β (α ∪ β))))))
(check-true (term (wf-type () (μ α (μ β (α ∪ Z))))))


(define ((check-termτ rr) e)
  (or (not (empty? ((term-match λmathτ
                      [(err ω) #t]
                      [v #t])
                      e)))
      (not (empty? (apply-reduction-relation rr e)))))

#;(check-reduction-relation eval-λmathτ (check-termτ eval-λmathτ)
  #:attempts 1000
  ;; just give a plain value if it generates something initially
  ;; containing a free variable
  #:prepare
  (λ (e)
    (let ([vars (term (fvτ ,e ()))])
      (if (not (empty? vars))
            (foldr (λ (x e)
              (term (substτ ,x ,(generate-term λmathτ prim 5) ,e)))
              e vars)
          e))))
