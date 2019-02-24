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

;; the initial state
;; note that here we limit the boat size to 3
(define-fun initial  ((s State)) Bool
 (and
  (and
    (and
      (and
        (and
          (= (nm1 s) missionaries)
          (= (nc1 s) cannibals)
        )
        (= (nm2 s) 0)
       )
       (= (nc2 s) 0)
     )
    (= (bp s) 1)
  )
  (= (bcap s) 3)
 )
)

;; transition from s with (mm = missionaries to move, mc = cannibals to move) as parameters
(define-fun transition ((s State) (mm Int) (mc Int)) State
          (ite (and
                 (>= (bcap s) (+ mm mc))
                 (> (+ mm mc) 0)
               )
            (ite (= (bp s) 1)
              (ite (and
                     (>= (- (nm1 s) mm) 0)
                     (>= (- (nc1 s) mc 0))
                    )
                    (store
                      (store
                        (store
                        (store 
                          (store s 1 (- (nm1 s) mm))
                          2 (- (nc1 s) mc))
                         3 2)
                         4 (+ (nm2 s) mm))
                      5 (+ (nc2 s) mc))
                      s
              )
              (ite
                (and
                     (>= (- (nm2 s) mm) 0)
                     (>= (- (nc2 s) mc 0))
                 )
                 (store
                  (store
                      (store
                         (store 
                             (store s 1 (+ (nm1 s) mm))
                              2 (+ (nc1 s) mc))
                             3 1)
                            4 (- (nm2 s) mm))
                        5 (- (nc2 s) mc)
                  )
                  s
               )
             )
            s
          )
)


(define-fun-rec tran ((n Int) (state State) (params Parameters) (temp_state State) (len Int)) State
  (ite (<= n 0)
       state
       (ite (valid state)
            (tran (- n 1) (transition state (select p (- len (* 2 n))) (select p (- len (+ 1 (* 2 n))))) p state len)
            (tran (- n 1) temp_state p temp_state len)
       )
  )
)

;; parameter constraints
(assert (< 2 missionaries))
(assert (< 2 cannibals))
(assert (and (< 0 n) (<= n 100)))
(assert (forall ((i Int))
           (implies (and (<= 0 i) (<= i (* n 2)))
                    (and (<= 0 (select p i)) (<= (select p i) 3))
           )))

(assert (and
            (initial state)
            (final (tran n state p state (* 2 n)))
        )
)

(check-sat)
(get-model)