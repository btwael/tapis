(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) (Array Int Int) (Array Int Int) Int Int ) Bool)
(declare-fun !inv1 (Int (Array Int Int) (Array Int Int) (Array Int Int) Int Int ) Bool)
(assert (forall ((N@0 Int)(a2@0 (Array Int Int))(a1@0 (Array Int Int))(a3@0 (Array Int Int))(z@0 Int)(i@1 Int)) (=> (and (> |N@0| 0) (= |i@1| 0) (<= 0 |z@0|) (< |z@0| |N@0|)) (!inv0 |N@0| |a1@0| |a2@0| |a3@0| |i@1| |z@0|))))
(assert (forall ((N@0 Int)(a1@0 (Array Int Int))(a2@0 (Array Int Int))(a3@0 (Array Int Int))(i@0 Int)(z@0 Int)(i@1 Int)) (=> (and (!inv0 |N@0| |a1@0| |a2@0| |a3@0| |i@0| |z@0|) (not (< |i@0| |N@0|)) (= |i@1| 0)) (!inv1 |N@0| |a1@0| |a2@0| |a3@0| |i@1| |z@0|))))
(assert (forall ((N@0 Int)(a1@0 (Array Int Int))(a2@0 (Array Int Int))(a3@0 (Array Int Int))(i@0 Int)(z@0 Int)) (=> (and (!inv1 |N@0| |a1@0| |a2@0| |a3@0| |i@0| |z@0|) (not (< |i@0| |N@0|)) (not (forall ((x@0 Int)) (=> (and (<= 0 |x@0|) (< |x@0| |N@0|)) (= (select |a1@0| |x@0|) (select |a3@0| |x@0|)))))) false)))
(assert (forall ((N@0 Int)(a1@0 (Array Int Int))(a2@0 (Array Int Int))(a3@0 (Array Int Int))(i@0 Int)(z@0 Int)(i@1 Int)(a3@1 (Array Int Int))) (=> (and (!inv1 |N@0| |a1@0| |a2@0| |a3@1| |i@0| |z@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (not (= |i@0| |z@0|)) (= |a3@0| (store |a3@1| |i@0| (select |a2@0| |i@0|)))) (!inv1 |N@0| |a1@0| |a2@0| |a3@0| |i@1| |z@0|))))
(assert (forall ((N@0 Int)(a1@0 (Array Int Int))(a2@0 (Array Int Int))(a3@0 (Array Int Int))(i@0 Int)(z@0 Int)(i@1 Int)(a2@1 (Array Int Int))) (=> (and (!inv0 |N@0| |a1@0| |a2@1| |a3@0| |i@0| |z@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (not (= |i@0| |z@0|)) (= |a2@0| (store |a2@1| |i@0| (select |a1@0| |i@0|)))) (!inv0 |N@0| |a1@0| |a2@0| |a3@0| |i@1| |z@0|))))
(assert (forall ((N@0 Int)(a1@0 (Array Int Int))(a2@0 (Array Int Int))(a3@0 (Array Int Int))(i@0 Int)(z@0 Int)(i@1 Int)(a3@1 (Array Int Int))) (=> (and (!inv1 |N@0| |a1@0| |a2@0| |a3@1| |i@0| |z@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (not (not (= |i@0| |z@0|))) (= |a3@0| (store |a3@1| |i@0| (select |a1@0| |i@0|)))) (!inv1 |N@0| |a1@0| |a2@0| |a3@0| |i@1| |z@0|))))
(assert (forall ((N@0 Int)(a1@0 (Array Int Int))(a2@0 (Array Int Int))(a3@0 (Array Int Int))(i@0 Int)(z@0 Int)(i@1 Int)) (=> (and (!inv0 |N@0| |a1@0| |a2@0| |a3@0| |i@0| |z@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (not (not (= |i@0| |z@0|)))) (!inv0 |N@0| |a1@0| |a2@0| |a3@0| |i@1| |z@0|))))
(check-sat)