(set-logic HORN)
(declare-fun !inv1 (Int (Array Int Int) Int Int Int ) Bool)
(declare-fun !inv0 (Int (Array Int Int) Int Int ) Bool)
(assert (forall ((CELLCOUNT_2@0 Int)(.volArray!size@0 Int)(volArray@0 (Array Int Int))(i@0 Int)) (=> (and (> (* 2 |CELLCOUNT_2@0|) 1) (= |.volArray!size@0| (* 2 |CELLCOUNT_2@0|)) (= |i@0| 1)) (!inv0 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@0|))))
(assert (forall ((CELLCOUNT_2@0 Int)(volArray@0 (Array Int Int))(.volArray!size@0 Int)(i@0 Int)(j@0 Int)) (=> (and (!inv0 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@0|) (<= |i@0| |CELLCOUNT_2@0|) (= |j@0| 2)) (!inv1 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@0| |j@0|))))
(assert (forall ((CELLCOUNT_2@0 Int)(volArray@0 (Array Int Int))(.volArray!size@0 Int)(i@0 Int)(j@0 Int)(i@1 Int)) (=> (and (!inv1 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@0| |j@0|) (not (>= |j@0| 1)) (= |i@1| (+ |i@0| 1))) (!inv0 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@1|))))
(assert (forall ((CELLCOUNT_2@0 Int)(volArray@0 (Array Int Int))(.volArray!size@0 Int)(i@0 Int)) (=> (and (!inv0 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@0|) (not (<= |i@0| |CELLCOUNT_2@0|)) (not (forall ((k@0 Int)) (=> (and (<= 0 |k@0|) (< |k@0| (* 2 |CELLCOUNT_2@0|))) (or (>= (select |volArray@0| |k@0|) 2) (= (select |volArray@0| |k@0|) 0)))))) false)))
(assert (forall ((CELLCOUNT_2@0 Int)(volArray@0 (Array Int Int))(.volArray!size@0 Int)(i@0 Int)(j@0 Int)(j@1 Int)(volArray@1 (Array Int Int))) (=> (and (!inv1 |CELLCOUNT_2@0| |volArray@1| |.volArray!size@0| |i@0| |j@0|) (= |j@1| (- |j@0| 1)) (>= |j@0| 1) (not (>= |j@0| 2)) (= |volArray@0| (store |volArray@1| (- (* |i@0| 2) |j@0|) 0))) (!inv1 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@0| |j@1|))))
(assert (forall ((CELLCOUNT_2@0 Int)(volArray@0 (Array Int Int))(.volArray!size@0 Int)(i@0 Int)(j@0 Int)(j@1 Int)(volArray@1 (Array Int Int))) (=> (and (!inv1 |CELLCOUNT_2@0| |volArray@1| |.volArray!size@0| |i@0| |j@0|) (= |j@1| (- |j@0| 1)) (>= |j@0| 1) (>= |j@0| 2) (= |volArray@0| (store |volArray@1| (- (* |i@0| 2) |j@0|) |j@0|))) (!inv1 |CELLCOUNT_2@0| |volArray@0| |.volArray!size@0| |i@0| |j@1|))))
(check-sat)