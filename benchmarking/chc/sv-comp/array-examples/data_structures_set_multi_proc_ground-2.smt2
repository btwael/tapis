(set-logic HORN)
(declare-fun elem_exists@pre ((Array Int Int) Int Int Int ) Bool)
(declare-fun insert@summary ((Array Int Int) Int Int Int Int (Array Int Int) ) Bool)
(declare-fun insert@pre ((Array Int Int) Int Int Int ) Bool)
(declare-fun elem_exists@summary ((Array Int Int) Int Int Int Bool ) Bool)
(declare-fun !inv0 ((Array Int Int) Int Int Int Int ) Bool)
(declare-fun !inv1 (Int Int (Array Int Int) (Array Int Int) Int ) Bool)
(assert (forall ((.set@0 (Array Int Int))(.set!size@0 Int)(size@0 Int)(value@0 Int)(!return@0 Int)(set@0 (Array Int Int))(set@1 (Array Int Int))) (=> (and (insert@pre |set@0| |.set!size@0| |size@0| |value@0|) (= |.set@0| |set@0|) (= |set@1| (store |set@0| |size@0| |value@0|)) (= |!return@0| (+ |size@0| 1))) (insert@summary |.set@0| |.set!size@0| |size@0| |value@0| |!return@0| |set@1|))))
(assert (forall ((set@0 (Array Int Int))(.set!size@0 Int)(size@0 Int)(value@0 Int)(i@1 Int)) (=> (and (= |i@1| 0) (elem_exists@pre |set@0| |.set!size@0| |size@0| |value@0|)) (!inv0 |set@0| |.set!size@0| |size@0| |value@0| |i@1|))))
(assert (forall ((set@0 (Array Int Int))(.set!size@0 Int)(size@0 Int)(value@0 Int)(i@0 Int)(!return@0 Bool)) (=> (and (!inv0 |set@0| |.set!size@0| |size@0| |value@0| |i@0|) (< |i@0| |size@0|) (= (select |set@0| |i@0|) |value@0|) (= |!return@0| true)) (elem_exists@summary |set@0| |.set!size@0| |size@0| |value@0| |!return@0|))))
(assert (forall ((set@0 (Array Int Int))(.set!size@0 Int)(size@0 Int)(value@0 Int)(i@0 Int)(!return@0 Bool)) (=> (and (!inv0 |set@0| |.set!size@0| |size@0| |value@0| |i@0|) (not (< |i@0| |size@0|)) (= |!return@0| false)) (elem_exists@summary |set@0| |.set!size@0| |size@0| |value@0| |!return@0|))))
(assert (forall ((SIZE@0 Int)(n@0 Int)) (=> (and (> |SIZE@0| 0) (= |n@0| 0) (not (forall ((x@0 Int)(y@0 Int)) (=> (and (<= 0 |x@0|) (< |x@0| |n@0|)) (=> (and (<= (+ |x@0| 1) |y@0|) (< |y@0| |n@0|)) (not (= (select |set@0| |x@0|) (select |set@0| |y@0|)))))))) false)))
(assert (forall ((SIZE@0 Int)(n@0 Int)(set@0 (Array Int Int))(values@0 (Array Int Int))(v@0 Int)) (=> (and (> |SIZE@0| 0) (= |n@0| 0) (forall ((x@0 Int)(y@0 Int)) (=> (and (<= 0 |x@0|) (< |x@0| |n@0|)) (=> (and (<= (+ |x@0| 1) |y@0|) (< |y@0| |n@0|)) (not (= (select |set@0| |x@0|) (select |set@0| |y@0|)))))) (= |v@0| 0)) (!inv1 |SIZE@0| |n@0| |set@0| |values@0| |v@0|))))
(assert (forall ((SIZE@0 Int)(n@0 Int)(set@0 (Array Int Int))(values@0 (Array Int Int))(v@0 Int)) (=> (and (< |v@0| |SIZE@0|) (!inv1 |SIZE@0| |n@0| |set@0| |values@0| |v@0|)) (elem_exists@pre |set@0| |SIZE@0| |n@0| (select |values@0| |v@0|)))))
(assert (forall ((SIZE@0 Int)(n@0 Int)(set@0 (Array Int Int))(values@0 (Array Int Int))(v@0 Int)(!rtrnd0 Bool)) (=> (and (elem_exists@summary |set@0| |SIZE@0| |n@0| (select |values@0| |v@0|) !rtrnd0) (elem_exists@pre |set@0| |SIZE@0| |n@0| (select |values@0| |v@0|)) (!inv1 |SIZE@0| |n@0| |set@0| |values@0| |v@0|) (< |v@0| |SIZE@0|) (not !rtrnd0)) (insert@pre |set@0| |SIZE@0| |n@0| (select |values@0| |v@0|)))))
(assert (forall ((SIZE@0 Int)(n@0 Int)(set@0 (Array Int Int))(values@0 (Array Int Int))(v@0 Int)) (=> (and (!inv1 |SIZE@0| |n@0| |set@0| |values@0| |v@0|) (not (< |v@0| |SIZE@0|)) (not (forall ((z@0 Int)(u@0 Int)) (=> (and (<= 0 |z@0|) (< |z@0| |n@0|)) (=> (and (<= (+ |z@0| 1) |u@0|) (< |u@0| |n@0|)) (not (= (select |set@0| |z@0|) (select |set@0| |u@0|)))))))) false)))
(assert (forall ((SIZE@0 Int)(n@0 Int)(set@0 (Array Int Int))(values@0 (Array Int Int))(v@0 Int)(v@1 Int)(!rtrnd0 Bool)) (=> (and (elem_exists@summary |set@0| |SIZE@0| |n@0| (select |values@0| |v@0|) !rtrnd0) (elem_exists@pre |set@0| |SIZE@0| |n@0| (select |values@0| |v@0|)) (!inv1 |SIZE@0| |n@0| |set@0| |values@0| |v@0|) (= |v@1| (+ |v@0| 1)) (< |v@0| |SIZE@0|) (not (not !rtrnd0))) (!inv1 |SIZE@0| |n@0| |set@0| |values@0| |v@1|))))
(assert (forall ((SIZE@0 Int)(n@0 Int)(set@0 (Array Int Int))(values@0 (Array Int Int))(v@0 Int)(v@1 Int)(n@1 Int)(set@1 (Array Int Int))(!rtrnd0 Bool)(!rtrnd1 Int)) (=> (and (insert@summary |set@1| |SIZE@0| |n@1| (select |values@0| |v@0|) !rtrnd1 |set@0|) (insert@pre |set@1| |SIZE@0| |n@1| (select |values@0| |v@0|)) (elem_exists@summary |set@1| |SIZE@0| |n@1| (select |values@0| |v@0|) !rtrnd0) (elem_exists@pre |set@1| |SIZE@0| |n@1| (select |values@0| |v@0|)) (!inv1 |SIZE@0| |n@1| |set@1| |values@0| |v@0|) (= |v@1| (+ |v@0| 1)) (< |v@0| |SIZE@0|) (not !rtrnd0) (= |n@0| !rtrnd1)) (!inv1 |SIZE@0| |n@0| |set@0| |values@0| |v@1|))))
(assert (forall ((set@0 (Array Int Int))(.set!size@0 Int)(size@0 Int)(value@0 Int)(i@0 Int)(i@1 Int)) (=> (and (!inv0 |set@0| |.set!size@0| |size@0| |value@0| |i@0|) (= |i@1| (+ |i@0| 1)) (< |i@0| |size@0|) (not (= (select |set@0| |i@0|) |value@0|))) (!inv0 |set@0| |.set!size@0| |size@0| |value@0| |i@1|))))
(check-sat)