(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int Int ) Bool)
(assert (forall ((N@0 Int)(a@0 (Array Int Int))(.a!size@0 Int)(i@1 Int)) (=> (and (>= |N@0| 0) (= |.a!size@0| (+ (* 3 |N@0|) 1)) (= |i@1| 0)) (!inv0 |N@0| |a@0| |.a!size@0| |i@1|))))
(assert (forall ((N@0 Int)(a@0 (Array Int Int))(.a!size@0 Int)(i@0 Int)) (=> (and (!inv0 |N@0| |a@0| |.a!size@0| |i@0|) (not (<= |i@0| |N@0|)) (not (forall ((k@0 Int)) (=> (and (<= 0 |k@0|) (<= |k@0| (* 3 |N@0|))) (>= (select |a@0| |k@0|) 0))))) false)))
(assert (forall ((N@0 Int)(.a!size@0 Int)(a@0 (Array Int Int))(i@0 Int)(a@1 (Array Int Int))(a@2 (Array Int Int))(a@3 (Array Int Int))(i@1 Int)) (=> (and (!inv0 |N@0| |a@0| |.a!size@0| |i@0|) (<= |i@0| |N@0|) (= |a@1| (store |a@0| (* 3 |i@0|) 0)) (= |a@2| (store |a@1| (+ (* 3 |i@0|) 1) 0)) (= |a@3| (store |a@2| (+ (* 3 |i@0|) 2) 0)) (= |i@1| (+ |i@0| 1))) (!inv0 |N@0| |a@3| |.a!size@0| |i@1|))))
(check-sat)