(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int Int ) Bool)
(assert (forall ((N@0 Int)(j@0 Int)(array@0 (Array Int Int))(argmin@0 Int)) (=> (and (> |N@0| 0) (= |j@0| |N@0|) (= |argmin@0| (- |N@0| 1))) (!inv0 |N@0| |array@0| |j@0| |argmin@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(j@0 Int)(argmin@0 Int)) (=> (and (!inv0 |N@0| |array@0| |j@0| |argmin@0|) (not (> |j@0| 0)) (not (forall ((k@0 Int)) (=> (and (<= 0 |k@0|) (< |k@0| |N@0|)) (>= (select |array@0| |k@0|) (select |array@0| |argmin@0|)))))) false)))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(j@0 Int)(argmin@0 Int)(j@1 Int)(argmin@1 Int)) (=> (and (!inv0 |N@0| |array@0| |j@0| |argmin@1|) (= |j@1| (- |j@0| 1)) (> |j@0| 0) (> (select |array@0| |argmin@1|) (select |array@0| (- |j@0| 1))) (= |argmin@0| (- |j@0| 1))) (!inv0 |N@0| |array@0| |j@1| |argmin@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(j@0 Int)(argmin@0 Int)(j@1 Int)) (=> (and (!inv0 |N@0| |array@0| |j@0| |argmin@0|) (= |j@1| (- |j@0| 1)) (> |j@0| 0) (not (> (select |array@0| |argmin@0|) (select |array@0| (- |j@0| 1))))) (!inv0 |N@0| |array@0| |j@1| |argmin@0|))))
(check-sat)