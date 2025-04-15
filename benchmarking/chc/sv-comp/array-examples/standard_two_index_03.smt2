(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) (Array Int Int) Int Int ) Bool)
(declare-fun !inv1 (Int (Array Int Int) (Array Int Int) Int Int ) Bool)
(assert (forall ((size@0 Int)(a@0 (Array Int Int))(b@0 (Array Int Int))(i@0 Int)(j@0 Int)(i@1 Int)) (=> (and (> |size@0| 0) (= |i@0| 0) (= |j@0| 0) (= |i@1| 1)) (!inv0 |size@0| |a@0| |b@0| |i@1| |j@0|))))
(assert (forall ((size@0 Int)(a@0 (Array Int Int))(b@0 (Array Int Int))(i@0 Int)(j@0 Int)(i@1 Int)(j@1 Int)) (=> (and (!inv0 |size@0| |a@0| |b@0| |i@0| |j@0|) (not (< |i@0| |size@0|)) (= |i@1| 1) (= |j@1| 0)) (!inv1 |size@0| |a@0| |b@0| |i@1| |j@1|))))
(assert (forall ((size@0 Int)(a@0 (Array Int Int))(b@0 (Array Int Int))(i@0 Int)(j@0 Int)(a@1 (Array Int Int))(i@1 Int)(j@1 Int)) (=> (and (!inv0 |size@0| |a@0| |b@0| |i@0| |j@0|) (< |i@0| |size@0|) (= |a@1| (store |a@0| |j@0| (select |b@0| |i@0|))) (= |i@1| (+ |i@0| 3)) (= |j@1| (+ |j@0| 1))) (!inv0 |size@0| |a@1| |b@0| |i@1| |j@1|))))
(assert (forall ((size@0 Int)(a@0 (Array Int Int))(b@0 (Array Int Int))(i@0 Int)(j@0 Int)) (=> (and (!inv1 |size@0| |a@0| |b@0| |i@0| |j@0|) (< |i@0| |size@0|) (not (= (select |a@0| |j@0|) (select |b@0| (+ (* 3 |j@0|) 1))))) false)))
(assert (forall ((size@0 Int)(a@0 (Array Int Int))(b@0 (Array Int Int))(i@0 Int)(j@0 Int)(i@1 Int)(j@1 Int)) (=> (and (!inv1 |size@0| |a@0| |b@0| |i@0| |j@0|) (< |i@0| |size@0|) (= (select |a@0| |j@0|) (select |b@0| (+ (* 3 |j@0|) 1))) (= |i@1| (+ |i@0| 3)) (= |j@1| (+ |j@0| 1))) (!inv1 |size@0| |a@0| |b@0| |i@1| |j@1|))))
(check-sat)