(set-logic LIA)

(synth-fun f ((a Int) (b Int) (c Int)) Int
   ((Start Int (0 1 2 3 4 5 6 7 a b c
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)
                      (< Start Start)
                      (> Start Start)))))

(declare-var a Int)
(declare-var b Int)
(declare-var c Int)

(constraint (=> (and (<= a 1) (and (<= b 1) (and (<= c 1) (and (>= a 0) (and (>= b 0) (>= c 0))))))
  (and 
    (iff (= a 0) (or (= (f a b c) 7) (or (= (f a b c) 2) (or (= (f a b c) 3) (= (f a b c) 5)))))
  (and
    (iff (= b 0) (or (= (f a b c) 7) (or (= (f a b c) 2) (or (= (f a b c) 4) (= (f a b c) 0)))))
  (and
    (iff (= c 0) (or (= (f a b c) 7) (or (= (f a b c) 3) (or (= (f a b c) 4) (= (f a b c) 6)))))
    (and (<= (f a b c) 7) (>= (f a b c) 0))
  )))
))



(check-synth)

