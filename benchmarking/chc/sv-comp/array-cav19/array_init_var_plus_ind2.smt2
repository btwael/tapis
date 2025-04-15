(set-logic HORN)
(declare-fun !inv0 (Int Int Int (Array Int Int) Int ) Bool)
(assert (forall ((N@0 Int)(k@0 Int)(j@0 Int)(a@0 (Array Int Int))(i@1 Int)) (=> (and (> |N@0| 0) (= |j@0| 0) (= |k@0| 0) (= |i@1| 0)) (!inv0 |N@0| |j@0| |k@0| |a@0| |i@1|))))
(assert (forall ((N@0 Int)(j@0 Int)(k@0 Int)(a@0 (Array Int Int))(i@0 Int)(x@0 Bool)) (=> (and (!inv0 |N@0| |j@0| |k@0| |a@0| |i@0|) (< |i@0| |N@0|) |x@0|) (!inv0 |N@0| |j@0| |k@0| |a@0| |i@0|))))
(assert (forall ((N@0 Int)(j@0 Int)(k@0 Int)(a@0 (Array Int Int))(i@0 Int)) (=> (and (!inv0 |N@0| |j@0| |k@0| |a@0| |i@0|) (not (< |i@0| |N@0|)) (not (forall ((l@0 Int)) (=> (and (<= 1 |l@0|) (< |l@0| |i@0|)) (>= (select |a@0| |l@0|) |k@0|))))) false)))
(assert (forall ((N@0 Int)(j@0 Int)(k@0 Int)(a@0 (Array Int Int))(i@0 Int)(x@0 Bool)(a@1 (Array Int Int))(j@1 Int)(k@1 Int)(i@1 Int)) (=> (and (!inv0 |N@0| |j@0| |k@0| |a@0| |i@0|) (= |a@1| (store |a@0| |i@0| |j@0|)) (= |j@1| (+ |j@0| |i@0|)) (= |k@1| (- |k@0| |i@0|)) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (not |x@0|)) (!inv0 |N@0| |j@1| |k@1| |a@1| |i@1|))))
(check-sat)