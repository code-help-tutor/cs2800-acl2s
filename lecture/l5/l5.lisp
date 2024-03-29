WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
;$ACL2s-SMode$;ACL2s
;; Definition of rl using cond

(definec rl (l :tl n :nat) :tl
  (cond ((= n 0) l)
        ((lendp l) l)
        (t (rl (app (tail l) (list (head l))) (1- n)))))

(check= (rl (list 1 2 3) 1) (list 2 3 1))
(check= (rl (list 1 2 3) 2) (list 3 1 2))
(check= (rl (list 1 2 3) 3) (list 1 2 3))

; pattern match version

(definec rl-pm (l :tl n :nat) :tl
  (match (list l n)
    ((:or (() &) (& 0)) l)
    (((f . r) &) (rl-pm (app r (list f)) (1- n)))))

;; Let's test that erl and rl-pm are functionally equivalent.
(property (l :tl n :nat)
  (== (rl-pm l n) (rl l n)))

;; Exercise: define an efficient version.
(definec erl (l :tl n :nat) :tl
  (match l
    (() l)
    (& (rl l (mod n (len l))))))

(check= (erl '(1 2 3 4 5) 3) (rl '(1 2 3 4 5) 3))#|ACL2s-ToDo-Line|#


;; Notice that we used a reduction!

;; That is, erl, when l is not empty, performs the mod operation and
;; then calls rl. This is a reduction because we reduced erl to
;; rl. Reduction is a common technique good programmers use: when
;; writing programs, they make use of any relevant existing
;; code/libraries that they have access to. Reduction often leads to
;; drastically simpler code. For example, to solve the order
;; statistics problem (find the kth largest element of a list), you
;; can use a sorting algorithm. That is not the most efficient way to
;; do it, but it is fast and easy (given that you already have an
;; efficient sorting algorithm, say in an existing library).

;; Let's test that erl and rl are functionally equivalent.
(property (l :tl n :nat)
  :proofs? nil
  (== (erl l n) (rl l n)))

;; ~ 0 seconds, but ~2.5 seconds for rl 
(time$ (erl '(1 2 3 4 5) (expt 10 8)))

;; ~ 0 seconds, but ~2500 seconds for rl 
(time$ (erl '(1 2 3 4 5) (expt 10 11)))

;; Is this the best we can do? That will be covered in HWK2.

;; Review HWK2 and start working on solutions.

