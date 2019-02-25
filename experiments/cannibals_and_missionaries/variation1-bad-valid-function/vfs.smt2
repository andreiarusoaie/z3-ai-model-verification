;; a generic sort State, modelled as an array
(define-sort State () (Array Int Int))

;; the state
(declare-const state State)

;; the number of missionaries and cannibals
(declare-const missionaries Int)
(declare-const cannibals Int)

;; helper functions that extract parameters from the state
;; boat capacity
(define-fun bcap  ((s State)) Int (select s 0))
;; number of missionaries on the left shore
(define-fun nm1 ((s State)) Int (select s 1))
;; number of cannibals on the left shore
(define-fun nc1 ((s State)) Int (select s 2))
;; the boat position
(define-fun bp ((s State)) Int (select s 3))
;; number of missionaries on the right shore
(define-fun nm2 ((s State)) Int (select s 4))
;; number of cannibals on the right shore
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
       (> (nm1 s) (nc1 s))
       (> (nm2 s) (nc2 s))
       ))))
     (and
      (and (> missionaries 0) (> cannibals 0))
      (forall ((i Int)) (implies (and (>= i 0) (<= i 5)) (>= (select s i) 0)))
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
(assert (< 2 (bcap state)))

(assert (and (valid state) (final state)))

(check-sat)
(get-model)
