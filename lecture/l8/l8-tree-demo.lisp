WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
#|

#+AUTHOR: Pete Manolios
#+TITLE: CS2800, Fall 2023, Lecture 7 code
#+EMAIL: pete@ccs.neu.edu
#+DATE: Sep 20, 2023

|#
; set session mode
; line mode should always be enforced
; start a new session (delete any session windows before doing this)
; split window

1
2
1/2
2/4
4/2
-8/18
t
nil
()
'()
't
'a
'b
'|a|
"hello"
#\a
'(a "hello" -6/32)
(if t 1 'a)
(if nil 1 'a)
"hello" ; there "bob" ( 1
#| This is 
a multi-line 
comment
|#
"bill"
"show auto-indent"
(if t
  (if t
    (if t nil nil)
    t)
  t)

(and)
(and t nil t)
(or)
(or nil t t)

; contract violation example
(/ 1 0)

; Definitions on trees 
(definec swap (x :all) :all
  (match x
    (:atom x)
    ((f . r) (cons (swap r) (swap f)))))
  
(check= (swap '(1 . 2)) '(2 . 1))
(check= (swap '((1 . 2) . (3 . 4))) '((4 . 3) . (2 . 1)))
(check= (swap '(1 2 3)) '(((nil . 3) . 2) . 1))

; Count the number of atoms in a tree.
(definec tree-size (x :all) :all
  (match x
    (:atom 1)
    ((f . r) (+ (tree-size f) (tree-size r)))))

; true or not?
(property swap-preserves-size (x :all)
  (= (tree-size (swap x))
     (tree-size x)))

; Let's check if e is in x
(definec tree-in (e x :all) :bool
  (match x
    (:atom (== e x))
    ((!e . &) t)
    ((f . r) (or (tree-in e f) (tree-in e r)))))

(check (tree-in 1 '((a . 2) (b . 1))))
(check (! (tree-in nil '(a . 2))))
(check (tree-in nil '((a . 2) (b . 1))))

; true or not?
(property swap-preserves-tree-in (e x :all)
  (== (tree-in e (swap x))
      (tree-in e x)))

; Is there something like the above that we can prove?
(property swap-preserves-tree-in-atom (e :atom x :all)
  (== (tree-in e (swap x))
      (tree-in e x)))

; What if I wrote this? Is it equivalent?
; The idea might be to treat car/cdr symmetrically.

(definec tree-in2 (e x :all) :bool
  (match x
    (:atom (== e x))
    ((!e . &) t)
    ((& . !e) t)
    ((f . r) (or (tree-in2 e f) (tree-in2 e r)))))

(property (e x :all)
  (== (tree-in2 e x)
      (tree-in e x)))

; What happened?
; Note that the innocuous update to the function led to different
; behavior!
; Test, verify!

; What is the spec for tree-in, anyway?
; Specs are important!

; If you don't have a spec, then GIGO
; What if the spec was (tree-in e x) checks if
; e (type :all) appears anywhere in x (type :all)

; Try to write a version that works.
; Do this on your own!
; Ask on Piazza if you have problems or questions.
(definec tree-in-spec (e x :all) :bool
  XXX)

; Some properties

(property (x :all)
  (tree-in-spec x x))

(property (a b :all)
  (^ (tree-in-spec a (cons a b))
     (tree-in-spec b (cons a b))))
