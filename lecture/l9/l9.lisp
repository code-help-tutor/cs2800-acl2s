WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
;$ACL2s-SMode$;ACL2s
#|

#+AUTHOR: Pete Manolios
#+TITLE: CS2800, Fall 2023, Lecture 9 code
#+EMAIL: pete@ccs.neu.edu
#+DATE: Sep 25, 2023

|#

(definec even-natp (x :nat) :bool
  (natp (/ x 2)))

(definec even-intp (x :int) :bool
  (intp (/ x 2)))

(property (n :nat)
  :proofs? nil
  (== (even-intp n)
      (even-natp n)))

(property (n :int)
  :proofs? t
  (equal (even-intp n)
         (even-natp n)))

(property (n :nat)
  :hyps (< 20/3 n)
  (== (even-intp n)
      (even-natp n)))

(property (n :all)
  :hyps (< 20/3 n)
  :body (== (even-intp n)
            (even-natp n)))

(property (n :neg)
  (== (even-intp n)
      (even-natp (* n -1))))

(property (n :int)
  :hyps (< n 0)
  (== (even-intp n)
      (even-natp (* n -1))))

;; Grade the following.

;; Q5
;;
;; Define last-n, a function that given a true list, l, and a natural
;; number n, returns the last n elements of the list. If the list has
;; less than n elements, it returns the whole list. Do not use match.

;; Make sure that last-n has linear complexity in terms of the
;; length of l (irrespective of what n is). See above comment on
;; complexity. 

(definec last-n (l :tl n :nat) :tl
  (cond
   ((<= (len l) n)
    l)
   (t (last-n (cdr l) n))))

;; Note: Not linear time! Why not?


;; How can we test whether this is linear?

; From HWK
(definec gen-n-to-1 (n :pos) :tl
  (if (= n 1)
      '(1)
    (cons n (gen-n-to-1 (1- n)))))

; prog2$ avoids showing us the list.
; this seems OK. Why?
(time$ (prog2$ (let* ((n (expt 10 5)))
                 (last-n (gen-n-to-1 n) (1- n)))
               nil))

; coming up with worst case requires some thought.
; this pattern tends to work well.
(time$ (prog2$ (let* ((n (expt 10 5))
                      (m (/ n 2)))
                 (last-n (gen-n-to-1 n) m))
               nil))

; But this also works for this example
(time$ (prog2$ (let* ((n (expt 10 5)))
                 (last-n (gen-n-to-1 n) 1))
               nil))

; Make sure gen-n-to-1 is OK
(time$ (prog2$ (let* ((n (expt 10 5)))
                 (gen-n-to-1 n))
               nil))

; A correct solution
(definec last-n2 (l :tl n :nat) :tl
  (let* ((len-l (len l))
         (m (min n len-l)))
    (nthcdr (- len-l m) l)))

(time$ (prog2$ (let* ((n (expt 10 5))
                      (m (/ n 2)))
                 (last-n2 (gen-n-to-1 n) m))
               nil))

; Some sanity checking
(property (l :tl n :nat)
  (== (last-n2 l n)
      (last-n l n)))
