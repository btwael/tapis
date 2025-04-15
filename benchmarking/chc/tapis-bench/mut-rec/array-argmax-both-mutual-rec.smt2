(set-logic HORN)
(declare-fun rec_array_argmax_right@pre ((Array Int Int) Int Int Int Int ) Bool)
(declare-fun rec_array_argmax_right@summary ((Array Int Int) Int Int Int Int Int ) Bool)
(declare-fun rec_array_argmax_left@pre ((Array Int Int) Int Int Int Int ) Bool)
(declare-fun rec_array_argmax_left@summary ((Array Int Int) Int Int Int Int Int ) Bool)
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)) (=> (and (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(argmax@0 Int)(!return@0 Int)(!rtrnd0 Int)) (=> (and (rec_array_argmax_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd0) (rec_array_argmax_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |argmax@0| !rtrnd0) (> (select |array@0| |i@0|) (select |array@0| |argmax@0|)) (= |!return@0| |i@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)) (=> (and (rec_array_argmax_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(argmax@0 Int)(!return@0 Int)(!rtrnd1 Int)) (=> (and (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0| !rtrnd1) (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0|) (rec_array_argmax_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |argmax@0| !rtrnd1) (> (select |array@0| |j@0|) (select |array@0| |argmax@0|)) (= |!return@0| |j@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_right@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)) (=> (and (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(argmax@0 Int)(!return@0 Int)(!rtrnd2 Int)) (=> (and (rec_array_argmax_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd2) (rec_array_argmax_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |argmax@0| !rtrnd2) (> (select |array@0| |i@0|) (select |array@0| |argmax@0|)) (= |!return@0| |i@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))) (=> (> |N@0| 0) (rec_array_argmax_left@pre |array@0| |N@0| 0 (- |N@0| 1) |N@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))(argmax@0 Int)(!rtrnd3 Int)) (=> (and (rec_array_argmax_left@summary |array@0| |N@0| 0 (- |N@0| 1) |N@0| !rtrnd3) (rec_array_argmax_left@pre |array@0| |N@0| 0 (- |N@0| 1) |N@0|) (> |N@0| 0) (= |argmax@0| !rtrnd3) (not (forall ((k@0 Int)) (=> (and (<= 0 |k@0|) (< |k@0| |N@0|)) (<= (select |array@0| |k@0|) (select |array@0| |argmax@0|)))))) false)))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |i@0|) (not (and (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)))) (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(argmax@0 Int)(!return@0 Int)(!rtrnd0 Int)) (=> (and (rec_array_argmax_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd0) (rec_array_argmax_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |argmax@0|) (= |argmax@0| !rtrnd0) (not (> (select |array@0| |i@0|) (select |array@0| |argmax@0|))) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_argmax_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |j@0|) (not (and (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)))) (rec_array_argmax_right@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(argmax@0 Int)(!return@0 Int)(!rtrnd1 Int)) (=> (and (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0| !rtrnd1) (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0|) (rec_array_argmax_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |argmax@0|) (= |argmax@0| !rtrnd1) (not (> (select |array@0| |j@0|) (select |array@0| |argmax@0|))) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_right@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |i@0|) (not (and (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)))) (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(argmax@0 Int)(!return@0 Int)(!rtrnd2 Int)) (=> (and (rec_array_argmax_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd2) (rec_array_argmax_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_argmax_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |argmax@0|) (= |argmax@0| !rtrnd2) (not (> (select |array@0| |i@0|) (select |array@0| |argmax@0|))) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_argmax_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(check-sat)