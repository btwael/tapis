(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Bool ) Bool)
(declare-fun !inv1 (Int (Array Int Int) Bool Int ) Bool)
(assert (forall ((N@0 Int)(a@0 (Array Int Int))(swapped@0 Bool)) (=> (and (> |N@0| 0) (= |swapped@0| true)) (!inv0 |N@0| |a@0| |swapped@0|))))
(assert (forall ((N@0 Int)(swapped@1 Bool)(a@0 (Array Int Int))(swapped@0 Bool)(i@0 Int)) (=> (and (!inv0 |N@0| |a@0| |swapped@0|) |swapped@0| (= |swapped@1| false) (= |i@0| 1)) (!inv1 |N@0| |a@0| |swapped@1| |i@0|))))
(assert (forall ((N@0 Int)(a@0 (Array Int Int))(swapped@0 Bool)(i@0 Int)) (=> (and (not (< |i@0| |N@0|)) (!inv1 |N@0| |a@0| |swapped@0| |i@0|)) (!inv0 |N@0| |a@0| |swapped@0|))))
(assert (forall ((N@0 Int)(a@0 (Array Int Int))(swapped@0 Bool)) (=> (and (!inv0 |N@0| |a@0| |swapped@0|) (not |swapped@0|) (not (forall ((x@0 Int)(y@0 Int)) (=> (and (<= 0 |x@0|) (< |x@0| |N@0|)) (=> (and (<= (+ |x@0| 1) |y@0|) (< |y@0| |N@0|)) (<= (select |a@0| |x@0|) (select |a@0| |y@0|))))))) false)))
(assert (forall ((N@0 Int)(a@0 (Array Int Int))(swapped@0 Bool)(i@0 Int)(i@1 Int)(t@0 Int)(swapped@1 Bool)(a@1 (Array Int Int))(a@2 (Array Int Int))) (=> (and (!inv1 |N@0| |a@1| |swapped@1| |i@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (> (select |a@1| |i@0|) (select |a@1| (- |i@0| 1))) (= |t@0| (select |a@1| |i@0|)) (= |a@2| (store |a@1| |i@0| (select |a@1| (- |i@0| 1)))) (= |a@0| (store |a@2| (- |i@0| 1) |t@0|)) (= |swapped@0| true)) (!inv1 |N@0| |a@0| |swapped@0| |i@1|))))
(assert (forall ((N@0 Int)(a@0 (Array Int Int))(swapped@0 Bool)(i@0 Int)(i@1 Int)) (=> (and (!inv1 |N@0| |a@0| |swapped@0| |i@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (not (> (select |a@0| |i@0|) (select |a@0| (- |i@0| 1))))) (!inv1 |N@0| |a@0| |swapped@0| |i@1|))))
(check-sat)