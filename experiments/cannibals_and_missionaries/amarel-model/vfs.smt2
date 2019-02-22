;; a generic sort State, modelled as an array
(define-sort State () (Array Int Int))

;; the state
(declare-const state State)

;; the number of missionaries and cannibals
(declare-const missionaries Int)
(declare-const cannibals Int)

;; helper functions that extract parameters from the state
(define-fun bcap  ((s State)) Int (select s 0))
(define-fun nm1 ((s State)) Int (select s 1))
(define-fun nc1 ((s State)) Int (select s 2))
(define-fun bp ((s State)) Int (select s 3))
(define-fun nm2 ((s State)) Int (select s 4))
(define-fun nc2 ((s State)) Int (select s 5))

;; the validity function for states
(define-fun valid ((s State)) Bool
  (and
   (and
    (and
     (and
      (or (= (bp s) 1) (= (bp s) 2))
      (= missionaries (+ (nm1 s) (nm2 s)))
      (= cannibals (+ (nc1 s) (nc2 s)))
      (and
       (implies (> (nm1 s) 0) (>= (nm1 s) (nc1 s)))
       (implies (> (nc2 s) 0) (>= (nm2 s) (nc2 s)))
       ))))
   (and
     (and
      (and (> missionaries 0) (> cannibals 0))
      (forall ((i Int)) (implies (and (>= i 0) (<= i 5)) (>= (select s i) 0)))
     )
     (= (bcap s) 3)
   )
  )
)

;; the final state
(define-fun final ((s State)) Bool
  (and
   (and
    (= (nm2 s) missionaries)
    (= (nc2 s) cannibals))
   (= 2 (bp s))))


;; parameters constraints
(assert (< 2 missionaries))
(assert (< 2 cannibals))

(assert (and (valid state) (final state)))

(check-sat)
(get-model)
