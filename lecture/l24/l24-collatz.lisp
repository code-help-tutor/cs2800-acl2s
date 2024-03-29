WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
(program)

(definec c (n :nat) :nat
  (match n
    ((:t (< n 2)) n)
    (:even (c (/ n 2)))
    (& (c (1+ (* 3 n))))))






























(defdata lon (listof nat))

(definec c-list (n :nat) :lon
  (match n
    ((:t (< n 2)) (list n))
    (:even (cons n (c-list (/ n 2))))
    (& (cons n (c-list (1+ (* 3 n)))))))





















(c-list 8)
(c-list 1024)
(c-list 7)


(c-list 9)
(c-list 55)
(c-list 5555555555)
(c-list 6171)
(c-list 837799)
