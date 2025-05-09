(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int Int Int ) Bool)
(assert (forall ((N@0 Int)(v@0 Int)(array@0 (Array Int Int))(idx@0 Int)(i@0 Int)) (=> (and (> |N@0| 0) (= |idx@0| (- 1)) (= |i@0| 0)) (!inv0 |N@0| |array@0| |v@0| |idx@0| |i@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(i@0 Int)) (=> (and (!inv0 |N@0| |array@0| |v@0| |idx@0| |i@0|) (not (< |i@0| |N@0|)) (not (= |idx@0| (- 1))) (not (= |v@0| (select |array@0| |idx@0|)))) false)))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(i@0 Int)(i@1 Int)(idx@1 Int)) (=> (and (!inv0 |N@0| |array@0| |v@0| |idx@1| |i@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (= (select |array@0| |i@0|) |v@0|) (= |idx@0| |i@0|)) (!inv0 |N@0| |array@0| |v@0| |idx@0| |i@1|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(i@0 Int)(i@1 Int)) (=> (and (!inv0 |N@0| |array@0| |v@0| |idx@0| |i@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |N@0|) (not (= (select |array@0| |i@0|) |v@0|))) (!inv0 |N@0| |array@0| |v@0| |idx@0| |i@1|))))
(check-sat)