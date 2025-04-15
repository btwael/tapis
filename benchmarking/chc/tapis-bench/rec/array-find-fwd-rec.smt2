(set-logic HORN)
(declare-fun rec_array_find@summary ((Array Int Int) Int Int Int Int Int ) Bool)
(declare-fun rec_array_find@pre ((Array Int Int) Int Int Int Int ) Bool)
(assert (forall ((array@0 (Array Int Int))(v@0 Int)(.array!size@0 Int)(i@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_find@pre |array@0| |.array!size@0| |v@0| |i@0| |N@0|) (< |i@0| |N@0|) (= (select |array@0| |i@0|) |v@0|) (= |!return@0| |i@0|)) (rec_array_find@summary |array@0| |.array!size@0| |v@0| |i@0| |N@0| |!return@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)) (=> (> |N@0| 0) (rec_array_find@pre |array@0| |N@0| |v@0| 0 |N@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(v@0 Int)(idx@0 Int)(!rtrnd1 Int)) (=> (and (rec_array_find@summary |array@0| |N@0| |v@0| 0 |N@0| !rtrnd1) (rec_array_find@pre |array@0| |N@0| |v@0| 0 |N@0|) (> |N@0| 0) (= |idx@0| !rtrnd1) (not (= |idx@0| (- 1))) (not (= |v@0| (select |array@0| |idx@0|)))) false)))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(v@0 Int)(i@0 Int)(N@0 Int)) (=> (and (rec_array_find@pre |array@0| |.array!size@0| |v@0| |i@0| |N@0|) (< |i@0| |N@0|) (not (= (select |array@0| |i@0|) |v@0|))) (rec_array_find@pre |array@0| |.array!size@0| |v@0| (+ |i@0| 1) |N@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(v@0 Int)(i@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_find@pre |array@0| |.array!size@0| |v@0| |i@0| |N@0|) (= |!return@0| (- 1)) (not (< |i@0| |N@0|))) (rec_array_find@summary |array@0| |.array!size@0| |v@0| |i@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(v@0 Int)(i@0 Int)(N@0 Int)(!return@0 Int)(!rtrnd0 Int)) (=> (and (rec_array_find@pre |array@0| |.array!size@0| |v@0| |i@0| |N@0|) (rec_array_find@summary |array@0| |.array!size@0| |v@0| (+ |i@0| 1) |N@0| !rtrnd0) (rec_array_find@pre |array@0| |.array!size@0| |v@0| (+ |i@0| 1) |N@0|) (= |!return@0| !rtrnd0) (< |i@0| |N@0|) (not (= (select |array@0| |i@0|) |v@0|))) (rec_array_find@summary |array@0| |.array!size@0| |v@0| |i@0| |N@0| |!return@0|))))
(check-sat)