;; (set-option :smt.mbqi true)

;; a generic sort State, modelled as an array
(define-sort State () (Array Int Int))
;; a generic sort Parameters, modelled as an array
(define-sort Parameters () (Array Int Int))


;; the state
(declare-const state State)
;; no of transitions 
(declare-const n Int)
;; parameters
(declare-const p Parameters)


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
        (> (n1 s) (m1 s))
        (> (n2 s) (m2 s))
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

;; the initial state
;; note that here we limit the boat size to 3
(define-fun initial  ((s State)) Bool
 (and
  (and
    (and
      (and
        (and
          (= (n1 s) missionaries)
          (= (m1 s) cannibals)
        )
        (= (n2 s) 0)
       )
       (= (m2 s) 0)
     )
    (= (bp s) 1)
  )
  (= (b s) 3)
 )
)

;; transition from s with (missionaries_to_move, cannibals_to_move) as parameters
(define-fun transition ((s State) (missionaries_to_move Int) (cannibals_to_move Int)) State
          (ite (and
                 (>= (b s) (+ missionaries_to_move cannibals_to_move))
                 (> (+ missionaries_to_move cannibals_to_move) 0)
               )
            (ite (= (bp s) 1)
              (ite (and
                     (>= (- (n1 s) missionaries_to_move) 0)
                     (>= (- (m1 s) cannibals_to_move 0))
                    )
                    (store
                      (store
                        (store
                        (store 
                          (store s 1 (- (n1 s) missionaries_to_move))
                          2 (- (m1 s) cannibals_to_move))
                         3 2)
                         4 (+ (n2 s) missionaries_to_move))
                      5 (+ (m2 s) cannibals_to_move))
                      s
              )
              (ite
                (and
                     (>= (- (n2 s) missionaries_to_move) 0)
                     (>= (- (m2 s) cannibals_to_move 0))
                 )
                 (store
                  (store
                      (store
                         (store 
                             (store s 1 (+ (n1 s) missionaries_to_move))
                              2 (+ (m1 s) cannibals_to_move))
                             3 1)
                            4 (- (n2 s) missionaries_to_move))
                        5 (- (m2 s) cannibals_to_move)
                  )
                  s
               )
             )
            s
          )
)


(define-fun-rec tran ((n Int) (state State) (temp_state State) (params Parameters) (len Int)) State
  (ite (<= n 0)
       state
       (ite (valid state)
            (tran (- n 1) (transition state (select p (- len (* 2 n))) (select p (- len (+ 1 (* 2 n))))) state p len)
            (tran (- n 1) temp_state temp_state p len)
       )
  )
)

;; parameter limits for analysis
(assert (and (< 2 missionaries) (<= missionaries 1000)))
(assert (and (< 2 cannibals) (<= cannibals 1000)))
(assert (and (< 0 n) (<= n 1000)))
(assert (forall ((i Int))
           (implies (and (<= 0 i) (<= i (* n 2)))
                    (and (<= 0 (select p i)) (<= (select p i) 3))
           )))

(assert (and
            (initial state)
            (final (tran n state state p (* 2 n)))
        )
)

(check-sat)
;; (get-model)