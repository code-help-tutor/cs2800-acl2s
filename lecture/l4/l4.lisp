WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
;$ACL2s-SMode$;ACL2s
;; rl: TL x Nat -> TL
;; Given a list, l, and a natural number, n, rl rotates the list
;; to the left n times

;; Primary consideration: correctness
;; No need to worry about efficiency, can’t use high-order functions

; v1 of rl
(definec rl (l :tl n :nat) :tl
  (cond ((= n 0) l)
        (t (rl (app (tail l) (head l)) (1- n)))))

; v2 of rl
(definec rl (l :tl n :nat) :tl
  (cond ((= n 0) l)
        ((lendp l) l)
        (t (rl (app (tail l) (head l)) (1- n)))))

; v3 of rl
(definec rl (l :tl n :nat) :tl
  (cond ((= n 0) l)
        ((lendp l) l)
        (t (rl (app (tail l) (list (head l))) (1- n)))))

(check= (rl (list 1 2 3) 1) (list 2 3 1))
(check= (rl (list 1 2 3) 2) (list 3 1 2))
(check= (rl (list 1 2 3) 3) (list 1 2 3))

;; ~ 0.025 seconds
(time$ (rl '(1 2 3) (expt 10 6)))

;; now I added just one 0, so the size of the input increased by 1.
;; since this is an exponential time algorithm, the running time will
;; increase by a factor of ~10

;; ~ 0.25 seconds
(time$ (rl '(1 2 3) (expt 10 7)))

;; ~ 2.5 seconds by adding one more 0
(time$ (rl '(1 2 3) (expt 10 8)))
