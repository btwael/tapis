(set-logic HORN)
(declare-fun rec_array_max_left@summary ((Array Int Int) Int Int Int Int Int ) Bool)
(declare-fun rec_array_max_left@pre ((Array Int Int) Int Int Int Int ) Bool)
(declare-fun rec_array_max_right@pre ((Array Int Int) Int Int Int Int ) Bool)
(declare-fun rec_array_max_right@summary ((Array Int Int) Int Int Int Int Int ) Bool)
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)) (=> (and (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|))))
(assert (forall ((!rtrnd0 Int)(array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(max@0 Int)(!return@0 Int)) (=> (and (rec_array_max_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd0) (rec_array_max_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |max@0| !rtrnd0) (> (select |array@0| |i@0|) |max@0|) (= |!return@0| (select |array@0| |i@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)) (=> (and (rec_array_max_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0|))))
(assert (forall ((!rtrnd1 Int)(array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(max@0 Int)(!return@0 Int)) (=> (and (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0| !rtrnd1) (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0|) (rec_array_max_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |max@0| !rtrnd1) (> (select |array@0| |j@0|) |max@0|) (= |!return@0| (select |array@0| |j@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_right@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)) (=> (and (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|))))
(assert (forall ((!rtrnd2 Int)(array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(max@0 Int)(!return@0 Int)) (=> (and (rec_array_max_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd2) (rec_array_max_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |max@0| !rtrnd2) (> (select |array@0| |i@0|) |max@0|) (= |!return@0| (select |array@0| |i@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((N@0 Int)(array@0 (Array Int Int))) (=> (> |N@0| 0) (rec_array_max_left@pre |array@0| |N@0| 0 (- |N@0| 1) |N@0|))))
(assert (forall ((!rtrnd3 Int)(N@0 Int)(array@0 (Array Int Int))(max@0 Int)) (=> (and (rec_array_max_left@summary |array@0| |N@0| 0 (- |N@0| 1) |N@0| !rtrnd3) (rec_array_max_left@pre |array@0| |N@0| 0 (- |N@0| 1) |N@0|) (> |N@0| 0) (= |max@0| !rtrnd3) (not (forall ((k@0 Int)) (=> (and (<= 0 |k@0|) (< |k@0| |N@0|)) (<= (select |array@0| |k@0|) |max@0|))))) false)))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| (select |array@0| |i@0|)) (not (and (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)))) (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_max_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| (select |array@0| |j@0|)) (not (and (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)))) (rec_array_max_right@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((!rtrnd1 Int)(array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(max@0 Int)(!return@0 Int)) (=> (and (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0| !rtrnd1) (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| (- |j@0| 1) |N@0|) (rec_array_max_right@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |max@0|) (= |max@0| !rtrnd1) (not (> (select |array@0| |j@0|) |max@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_right@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((!rtrnd0 Int)(array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(max@0 Int)(!return@0 Int)) (=> (and (rec_array_max_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd0) (rec_array_max_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |max@0|) (= |max@0| !rtrnd0) (not (> (select |array@0| |i@0|) |max@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(!return@0 Int)) (=> (and (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| (select |array@0| |i@0|)) (not (and (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)))) (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(assert (forall ((!rtrnd2 Int)(array@0 (Array Int Int))(.array!size@0 Int)(i@0 Int)(j@0 Int)(N@0 Int)(max@0 Int)(!return@0 Int)) (=> (and (rec_array_max_right@summary |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0| !rtrnd2) (rec_array_max_right@pre |array@0| |.array!size@0| (+ |i@0| 1) |j@0| |N@0|) (rec_array_max_left@pre |array@0| |.array!size@0| |i@0| |j@0| |N@0|) (= |!return@0| |max@0|) (= |max@0| !rtrnd2) (not (> (select |array@0| |i@0|) |max@0|)) (<= |i@0| |j@0|) (< |i@0| |N@0|) (> |j@0| 0)) (rec_array_max_left@summary |array@0| |.array!size@0| |i@0| |j@0| |N@0| |!return@0|))))
(check-sat)