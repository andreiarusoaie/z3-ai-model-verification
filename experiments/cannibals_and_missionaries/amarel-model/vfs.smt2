;; a generic sort State, modelled as an array
(define-sort State () (Array Int Int))

;; the state
(declare-const state State)

;; the number of missionaries and cannibals
(declare-const missionaries Int)
(declare-const cannibals Int)

;; helper functions that extract parameters from the state
(define-fun b  ((s State)) Int (select s 0))
(define-fun n1 ((s State)) Int (select s 1))
(define-fun m1 ((s State)) Int (select s 2))
(define-fun bp ((s State)) Int (select s 3))
(define-fun n2 ((s State)) Int (select s 4))
(define-fun m2 ((s State)) Int (select s 5))

;; the validity function for states
(define-fun valid ((s State)) Bool
  (and
   (and
    (and
     (and
      (or (= (bp s) 1) (= (bp s) 2))
      (= missionaries (+ (n1 s) (n2 s)))
      (= cannibals (+ (m1 s) (m2 s)))
      (and
       (implies (> (n1 s) 0) (>= (n1 s) (m1 s)))
       (implies (> (n2 s) 0) (>= (n2 s) (m2 s)))
       ))))
   (and
     (and
      (and (> missionaries 0) (> cannibals 0))
      (forall ((i Int)) (implies (and (>= i 0) (<= i 5)) (>= (select s i) 0)))
     )
     (= (b s) 3)
   )
  )
)

;; the final state
(define-fun final ((s State)) Bool
  (and
   (and
    (= (n2 s) missionaries)
    (= (m2 s) cannibals))
   (= 2 (bp s))))


;; parameter limits for analysis
(assert (and (< 2 missionaries) (<= missionaries 1000)))
(assert (and (< 2 cannibals) (<= cannibals 1000)))

(assert (and (valid state) (final state)))

(check-sat)
(get-model)
