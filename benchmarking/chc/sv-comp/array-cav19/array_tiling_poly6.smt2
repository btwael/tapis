(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int ) Bool)
(declare-fun !inv1 (Int (Array Int Int) Int ) Bool)
(assert (forall ((S@0 Int)(a@0 (Array Int Int))(i@1 Int)) (=> (and (> |S@0| 0) (= |i@1| 0)) (!inv0 |S@0| |a@0| |i@1|))))
(assert (forall ((S@0 Int)(a@0 (Array Int Int))(i@0 Int)(a@1 (Array Int Int))(i@1 Int)) (=> (and (!inv0 |S@0| |a@0| |i@0|) (< |i@0| |S@0|) (= |a@1| (store |a@0| |i@0| (* (- |i@0| 1) (+ |i@0| 1)))) (= |i@1| (+ |i@0| 1))) (!inv0 |S@0| |a@1| |i@1|))))
(assert (forall ((S@0 Int)(a@0 (Array Int Int))(i@0 Int)(i@1 Int)) (=> (and (!inv0 |S@0| |a@0| |i@0|) (not (< |i@0| |S@0|)) (= |i@1| 0)) (!inv1 |S@0| |a@0| |i@1|))))
(assert (forall ((S@0 Int)(a@0 (Array Int Int))(i@0 Int)) (=> (and (!inv1 |S@0| |a@0| |i@0|) (not (< |i@0| |S@0|)) (not (forall ((k@0 Int)) (=> (and (<= 0 |k@0|) (< |k@0| |S@0|)) (= (select |a@0| |k@0|) (- 1)))))) false)))
(assert (forall ((S@0 Int)(a@0 (Array Int Int))(i@0 Int)(a@1 (Array Int Int))(i@1 Int)) (=> (and (!inv1 |S@0| |a@0| |i@0|) (< |i@0| |S@0|) (= |a@1| (store |a@0| |i@0| (- (select |a@0| |i@0|) (* |i@0| |i@0|)))) (= |i@1| (+ |i@0| 1))) (!inv1 |S@0| |a@1| |i@1|))))
(check-sat)