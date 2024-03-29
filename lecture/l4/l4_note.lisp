WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
;$ACL2s-SMode$;ACL2s
(in-package "ACL2S")

(definec rl (l :tl n :nat) :tl
  (cond 
   ((= n 0) l)
   ((lendp l) l)
   (t (rl (snoc (cdr l) (car l)) (- n 1)))))

(check= (rl (list 1 2 3) 1) (list 2 3 1))
(check= (rl (list 1 2 3) 2) (list 3 1 2))
(check= (rl (list 1 2 3) 3) (list 1 2 3))#|ACL2s-ToDo-Line|#
