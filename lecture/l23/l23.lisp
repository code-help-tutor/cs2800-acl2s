WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
(set-termination-method :measure)
(set-well-founded-relation n<)
(set-defunc-typed-undef nil)
(set-defunc-generalize-contract-thm nil)
(set-gag-mode nil)
(set-ignore-ok t)

(definec ceil (x :rational) :int
  (ceiling x 1))

; Our measure function
(definec m (x :rational) :nat
  (cond ((<= x 0) 0)
        ((>= x 2) (ceil (* 100 x)))
        ((>= x 1) (ceil (* 100 x)))
        (t 1)))

; One property for the whole function.
(property (x :rational)
  (cond ((<= x 0) t)
        ((>= x 2) (< (m (/ x 2)) (m x)))
        ((>= x 1) (< (m (- x 1/100)) (m x)))
        (t (< (m (- x)) (m x)))))

; Three properties, one for each recursive call
; Helps to localize errors, if you have them.
(property (x :rational)
  (=> (and (! (<= x 0))
           (>= x 2))
      (< (m (/ x 2)) (m x))))

(property (x :rational)
  (=> (and (! (<= x 0))
           (! (>= x 2))
           (>= x 1))
      (< (m (- x 1/100)) (m x))))

(property (x :rational)
  (=> (and (! (<= x 0))
           (! (>= x 2))
           (! (>= x 1)))
      (< (m (- x)) (m x))))

(definec f (x :rational) :rational
  (declare (xargs :measure (if (rationalp x) (m x) 0)))
  (cond ((<= x 0) x)
        ((>= x 2) (f (/ x 2)))
        ((>= x 1) (f (- x 1/100)))
        (t (f (- x)))))
