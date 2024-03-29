WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
(set-termination-method :measure)
(set-well-founded-relation n<)
(set-defunc-typed-undef nil)
(set-defunc-generalize-contract-thm nil)
(set-gag-mode nil)
(set-ignore-ok t)

#|
(definec f (a b :nat) :bool
  (v (= a b)
     (if (< b a)
       (f (1- a) (1+ b))
       (f (1+ b) a))))
||#

(definec f-trace (a b :nat) :tl
  (declare (xargs :mode :program))
  (cond ((= a b) (list (list a b)))
        ((< b a) (cons (list a b)
                       (f-trace (1- a) (1+ b))))
        (t (cons (list a b)
                 (f-trace (1+ b) a)))))

(f-trace 4 4)
(f-trace 10 4)
(f-trace 11 4)
(f-trace 4 10)
(f-trace 4 11)

(definec m-a<=b (a b :nat) :nat
  :ic (<= b a)
  (if (evenp (- a b))
    (/ (- a b) 2)
    (+ 2 (/ (- (1+ a) b) 2))))

(definec m (a b :nat) :nat
  (if (<= b a)
    (m-a<=b a b)
    (1+ (m-a<=b (1+ b) a))))

(property (a b :nat)
  :hyps (^ (!= a b) (< b a))
  (< (m (1- a) (1+ b)) (m a b)))

(property (a b :nat)
  :hyps (^ (!= a b) (! (< b a)))
  (< (m (1+ b) a) (m a b)))

(definec f (a b :nat) :bool
  (declare (xargs :measure (if (^ (natp a) (natp b)) (m a b) 0)))
  (v (= a b)
     (if (< b a)
       (f (1- a) (1+ b))
       (f (1+ b) a))))
