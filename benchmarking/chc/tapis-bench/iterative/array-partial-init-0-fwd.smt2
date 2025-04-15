(set-logic HORN)
(declare-fun !inv0 (Int Int Int (Array Int Int) Int ) Bool)
(assert (forall ((N@0 Int)(begin@0 Int)(end@0 Int)(array@0 (Array Int Int))(i@0 Int)) (=> (and (> |N@0| 0) (= |i@0| |begin@0|) (<= |end@0| |N@0|) (<= 0 |begin@0|) (<= |begin@0| |end@0|)) (!inv0 |N@0| |begin@0| |end@0| |array@0| |i@0|))))
(assert (forall ((N@0 Int)(begin@0 Int)(end@0 Int)(array@0 (Array Int Int))(i@0 Int)) (=> (and (!inv0 |N@0| |begin@0| |end@0| |array@0| |i@0|) (not (< |i@0| |end@0|)) (not (forall ((k@0 Int)) (=> (and (<= |begin@0| |k@0|) (< |k@0| |end@0|)) (= (select |array@0| |k@0|) 0))))) false)))
(assert (forall ((N@0 Int)(begin@0 Int)(end@0 Int)(array@0 (Array Int Int))(i@0 Int)(array@1 (Array Int Int))(i@1 Int)) (=> (and (!inv0 |N@0| |begin@0| |end@0| |array@0| |i@0|) (< |i@0| |end@0|) (= |array@1| (store |array@0| |i@0| 0)) (= |i@1| (+ |i@0| 1))) (!inv0 |N@0| |begin@0| |end@0| |array@1| |i@1|))))
(check-sat)