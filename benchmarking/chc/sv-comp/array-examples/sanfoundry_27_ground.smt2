(set-logic HORN)
(declare-fun !inv0 (Int (Array Int Int) Int Int ) Bool)
(assert (forall ((SIZE@0 Int)(array@0 (Array Int Int))(largest@0 Int)(i@1 Int)) (=> (and (> |SIZE@0| 0) (= |largest@0| (select |array@0| 0)) (= |i@1| 1)) (!inv0 |SIZE@0| |array@0| |i@1| |largest@0|))))
(assert (forall ((SIZE@0 Int)(array@0 (Array Int Int))(i@0 Int)(largest@0 Int)) (=> (and (!inv0 |SIZE@0| |array@0| |i@0| |largest@0|) (not (< |i@0| |SIZE@0|)) (not (forall ((x@0 Int)) (=> (and (<= 0 |x@0|) (< |x@0| |SIZE@0|)) (>= |largest@0| (select |array@0| |x@0|)))))) false)))
(assert (forall ((SIZE@0 Int)(array@0 (Array Int Int))(i@0 Int)(largest@0 Int)(i@1 Int)) (=> (and (!inv0 |SIZE@0| |array@0| |i@0| |largest@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |SIZE@0|) (not (< |largest@0| (select |array@0| |i@0|)))) (!inv0 |SIZE@0| |array@0| |i@1| |largest@0|))))
(assert (forall ((SIZE@0 Int)(array@0 (Array Int Int))(i@0 Int)(largest@0 Int)(i@1 Int)(largest@1 Int)) (=> (and (!inv0 |SIZE@0| |array@0| |i@0| |largest@1|) (= |i@1| (+ |i@0| 1)) (< |i@0| |SIZE@0|) (< |largest@1| (select |array@0| |i@0|)) (= |largest@0| (select |array@0| |i@0|))) (!inv0 |SIZE@0| |array@0| |i@1| |largest@0|))))
(check-sat)