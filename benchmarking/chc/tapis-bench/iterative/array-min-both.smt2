(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int Int Int ) Bool)
(assert (forall ((N@0 Int)(min@0 Int)(array@0 (Array Int Int))(i@0 Int)(j@0 Int)) (=> (and (> |N@0| 0) (= |min@0| (select |array@0| 0)) (= |i@0| 0) (= |j@0| |N@0|)) (!inv0 |N@0| |array@0| |min@0| |i@0| |j@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(min@0 Int)(i@0 Int)(j@0 Int)) (=> (and (!inv0 |N@0| |array@0| |min@0| |i@0| |j@0|) (not (and (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0))) (not (forall ((k@0 Int)) (=> (and (<= 0 |k@0|) (< |k@0| |N@0|)) (>= (select |array@0| |k@0|) |min@0|))))) false)))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(min@0 Int)(i@0 Int)(j@0 Int)(i@1 Int)(j@1 Int)(min@2 Int)) (=> (and (!inv0 |N@0| |array@0| |min@2| |i@0| |j@0|) (= |i@1| (+ |i@0| 1)) (= |j@1| (- |j@0| 1)) (not (> |min@0| (select |array@0| (- |j@0| 1)))) (> |min@2| (select |array@0| |i@0|)) (= |min@0| (select |array@0| |i@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (!inv0 |N@0| |array@0| |min@0| |i@1| |j@1|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(min@0 Int)(i@0 Int)(j@0 Int)(i@1 Int)(j@1 Int)(min@1 Int)(min@3 Int)) (=> (and (!inv0 |N@0| |array@0| |min@3| |i@0| |j@0|) (= |i@1| (+ |i@0| 1)) (= |j@1| (- |j@0| 1)) (> |min@1| (select |array@0| (- |j@0| 1))) (= |min@0| (select |array@0| (- |j@0| 1))) (> |min@3| (select |array@0| |i@0|)) (= |min@1| (select |array@0| |i@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (!inv0 |N@0| |array@0| |min@0| |i@1| |j@1|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(min@0 Int)(i@0 Int)(j@0 Int)(i@1 Int)(j@1 Int)(min@1 Int)) (=> (and (!inv0 |N@0| |array@0| |min@1| |i@0| |j@0|) (= |i@1| (+ |i@0| 1)) (= |j@1| (- |j@0| 1)) (> |min@1| (select |array@0| (- |j@0| 1))) (= |min@0| (select |array@0| (- |j@0| 1))) (not (> |min@1| (select |array@0| |i@0|))) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (!inv0 |N@0| |array@0| |min@0| |i@1| |j@1|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(min@0 Int)(i@0 Int)(j@0 Int)(i@1 Int)(j@1 Int)) (=> (and (!inv0 |N@0| |array@0| |min@0| |i@0| |j@0|) (= |i@1| (+ |i@0| 1)) (= |j@1| (- |j@0| 1)) (not (> |min@0| (select |array@0| (- |j@0| 1)))) (not (> |min@0| (select |array@0| |i@0|))) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (!inv0 |N@0| |array@0| |min@0| |i@1| |j@1|))))
(check-sat)