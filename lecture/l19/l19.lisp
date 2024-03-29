WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
;$ACL2s-SMode$;ACL2s
(definec del (a :all X :tl) :tl
  (cond ((endp X) X)
        ((== a (car X)) (del a (cdr X)))
        (t (cons (car X) (del a (cdr X))))))

; Here is an interesting theorem.
(property (a :all X :tl)
  :hyps (in a X)
  :body (! (in a (del a X))))

; Discussion. 

































; This is better.
(property (a :all X :tl)
  (! (in a (del a X))))#|ACL2s-ToDo-Line|#


; Let's copy the proof obligations and try 
; two of them in ACL2s using equational reasoning.