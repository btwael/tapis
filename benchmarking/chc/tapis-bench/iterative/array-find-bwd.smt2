(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int Int Int ) Bool)
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(j@0 Int)) (=> (and (> |N@0| 0) (= |idx@0| (- 1)) (= |j@0| |N@0|)) (!inv0 |N@0| |array@0| |v@0| |idx@0| |j@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(j@0 Int)) (=> (and (!inv0 |N@0| |array@0| |v@0| |idx@0| |j@0|) (not (> |j@0| 0)) (not (= |idx@0| (- 1))) (not (= |v@0| (select |array@0| |idx@0|)))) false)))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(j@0 Int)(j@1 Int)(idx@1 Int)) (=> (and (!inv0 |N@0| |array@0| |v@0| |idx@1| |j@0|) (= |j@1| (- |j@0| 1)) (> |j@0| 0) (= (select |array@0| (- |j@0| 1)) |v@0|) (= |idx@0| (- |j@0| 1))) (!inv0 |N@0| |array@0| |v@0| |idx@0| |j@1|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(j@0 Int)(j@1 Int)) (=> (and (!inv0 |N@0| |array@0| |v@0| |idx@0| |j@0|) (= |j@1| (- |j@0| 1)) (> |j@0| 0) (not (= (select |array@0| (- |j@0| 1)) |v@0|))) (!inv0 |N@0| |array@0| |v@0| |idx@0| |j@1|))))
(check-sat)