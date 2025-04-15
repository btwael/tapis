(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int ) Bool)
(declare-fun !inv1 (Int (Array Int Int) Int Int ) Bool)
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(i@0 Int)) (=> (and (> |N@0| 0) (= |i@0| 1)) (!inv0 |N@0| |array@0| |i@0|))))
(assert (forall ((N@0 Int)(j@0 Int)(array@0 (Array Int Int))(i@0 Int)) (=> (and (!inv0 |N@0| |array@0| |i@0|) (< |i@0| |N@0|) (= |j@0| |i@0|)) (!inv1 |N@0| |array@0| |i@0| |j@0|))))
(assert (forall ((i@0 Int)(N@0 Int)(array@0 (Array Int Int))(j@0 Int)(tmp@0 Int)(array@1 (Array Int Int))(array@2 (Array Int Int))(j@1 Int)) (=> (and (!inv1 |N@0| |array@0| |i@0| |j@0|) (= |tmp@0| (select |array@0| |j@0|)) (= |array@1| (store |array@0| |j@0| (select |array@0| (- |j@0| 1)))) (= |array@2| (store |array@1| (- |j@0| 1) |tmp@0|)) (= |j@1| (- |j@0| 1)) (> |j@0| 0) (> (select |array@0| (- |j@0| 1)) (select |array@0| |j@0|))) (!inv1 |N@0| |array@2| |i@0| |j@1|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(i@0 Int)(j@0 Int)(i@1 Int)) (=> (and (!inv1 |N@0| |array@0| |i@0| |j@0|) (not (and (> |j@0| 0) (> (select |array@0| (- |j@0| 1)) (select |array@0| |j@0|)))) (= |i@1| (+ |i@0| 1))) (!inv0 |N@0| |array@0| |i@1|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(i@0 Int)) (=> (and (!inv0 |N@0| |array@0| |i@0|) (not (< |i@0| |N@0|)) (not (forall ((k@0 Int)(l@0 Int)) (=> (and (<= 0 |k@0|) (< |k@0| (- |N@0| 1))) (=> (and (<= (+ |k@0| 1) |l@0|) (< |l@0| |N@0|)) (<= (select |array@0| |k@0|) (select |array@0| |l@0|))))))) false)))
(check-sat)