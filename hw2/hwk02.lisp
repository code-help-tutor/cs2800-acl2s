WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
#|

CS 2800 Homework 2 - Fall 2023

 - Due on Friday, Sep 22 by 11:00 pm.

 - You will have to work in groups. Groups should consist of 2-3
   people. Make sure you are in exactly 1 group!  Use the
   piazza "search for teammates" post to find teammates. Please give
   students who don't have a team a home. If you can't find a team ask
   Ankit for help on Piazza.

 - You will submit your hwk via gradescope. Instructions on how to
   do that are on Piazza. If you need help, ask on Piazza.

 - Submit the homework file (this file) on Gradescope. After clicking
   on "Upload", you must add your group members to the submission by
   clicking on "Add Group Member" and then filling their names. Every
   group member can submit the homework and we will only grade the
   last submission. You are responsible for making sure that your
   group submits the right version of the homework for your final
   submission. We suggest you submit early and often. Also, you will
   get feedback on some problems when you submit. However, this
   feedback does not determine your final grade, as we will manually
   review submissions. Submission will be enabled a few days after the
   homework is released, but well before the deadline.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 For this homework you will need to use ACL2s.

 Technical instructions:

 - Open this file in ACL2s.

 - Make sure you are in ACL2s mode. This is essential! Note that you can
   only change the mode when the session is not running, so set the correct
   mode before starting the session.

 - Insert your solutions into this file where indicated (usually as "XXX")

 - Only add to the file. Do not remove or comment out anything pre-existing.

 - Make sure the entire file is accepted by ACL2s. In particular, there must
   be no "XXX" left in the code. If you don't finish all problems, comment
   the unfinished ones out. Comments should also be used for any English
   text that you may add. This file already contains many comments, so you
   can see what the syntax is.

 - When done, save your file and submit it without changing the name
   of the file.

 - Do not submit the session file (which shows your interaction with
   the theorem prover). This is not part of your solution. Only submit
   the lisp file.

 Instructions for programming problems:

 For all function definitions you must:

 (1) Perform contract-based testing (see Lecture Notes) by adding
     appropriate check=/check tests.  You only have to do this for
     functions where you are responsible for at least some part of the
     definition.  This should be done before you define the function,
     as it is intended to make sure you understand the spec.

     We will use ACL2s' check= function for tests. This is a
     two-argument function that rejects two inputs that do not
     evaluate equal. You can think of check= roughly as defined like
     this:

     (definec check= (x :all y :all) :bool
       :input-contract (equal x y)
       :output-contract (== (check= x y) t)
       t)

     That is, check= only accepts two inputs with equal value. For
     such inputs, t (or "pass") is returned. For other inputs, you get
     an error. If any check= test in your file does not pass, your
     file will be rejected.

     We will also use ACL2's check function, which is a version of
     check= that checks if a single form evalutes to t, so you can
     think of

     (check X)

     as being equivalent to

     (check= X t)

 (2) (YOU DON'T HAVE TO DO THIS FOR THIS HWK. PREVIEW OF FUTURE)
     For all functions you define provide enough check= tests so that
     you have 100% expression coverage (see Lecture Notes).  You can
     use whatever tests we provide and your contract-based tests to
     achieve expression coverage, e.g., if the union of the tests we
     gave you and your contract-based tests provide 100% expression
     coverage, there is nothing left to do.

 (3) (YOU DON'T HAVE TO DO THIS FOR THIS HWK. PREVIEW OF FUTURE)
     Contract-based testing and expression coverage are the minimal
     testing requirements.  Feel free to add other tests as you see
     fit that capture interesing aspects of the function.

 (4) (YOU DON'T HAVE TO DO THIS FOR THIS HWK. PREVIEW OF FUTURE)
     For all functions where you are responsible for at least some
     part of the definition, add at least two interesting property
     forms. The intent here is to reinforce property-based testing.

 You can use any types, functions and macros listed on the ACL2s
 Language Reference (from class Webpage, click on "Lectures and Notes"
 and then on "ACL2s Language Reference"). 

 Since this is our first programming exercise, we will simplify the
 interaction with ACL2s somewhat. Instead of requiring ACL2s to prove
 termination and contracts, we allow ACL2s to proceed even if a proof
 fails.  However, if a counterexample is found, ACL2s will report it.
 See the lecture notes for more information.  This is achieved using
 the following directives (do not remove them):

|#

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)
(set-defunc-generalize-contract-thm nil)

; The next form tells ACL2s to not try proving properties, unless
; we explicitly ask. You explicitly ask by adding :proofs? t like this
; (property (..) :proofs? t ...)

(set-acl2s-property-table-proofs? nil)

; The next form tells ACL2s to not check contracts. If ACL2s does not
; prove function contracts when defining functions, then the property
; form will generate errors if it then tries to reason about the
; contracts of these functions. Instead of asking you to add the
; :check-contracts?  keyword command, we are just turning this testing
; off, which means you may not get as much checking as would otherwise
; be the case, so make sure your properties pass contract checking. If
; you want, you can comment out the next line to get more checking
; from ACL2s and if you run into problems, uncomment it.

(set-acl2s-property-table-check-contracts? nil)

#| 

 For this homework, you will be given a set of programming
 exercises. Try to use the techniques we discussed in class for
 defining recursive functions. The goal of this homework is to:

 (1) Help you become a better programmer by practicing how to define
 recursive functions using data-driven definitions and recursive
 thinking, as described in detail in class.

 (2) Help you become a better programmer by checking function and body
 contacts, an especially simple and effective type of invariant
 checking, as described in detail in class.

 (3) Get you familiar with ACL2s, which allows you to specify
 contracts and provides automated support for checking that
 definitions are terminating and satisfy their function and body
 contracts.

 (4) Make you think a little bit about the efficiency of the code you
 write. All great programmers have a deep understanding of algorithmic
 complexity. 

 Since we have not covered ACL2s in any great depth, the functions you
 will define will be recursive, and use basic types like lists
 and numbers.

 Feel free to define helper functions as needed. Remember, you have to
 provide tests for every function you define, including helper functions.

|# 

;; Q1
;;
;; Define gen-n-to-1, a function that given n, a pos, (positive
;; integer) generates the true list (n n-1 ... 1). Notice the type
;; pos, which corresponds to positive integers, ie, it is the same as
;; nat, except it does not inlcude 0. Do not use match.

;; Make sure that gen-n-to-1 has linear complexity in terms of the
;; length of the list it returns. Notice that this is exponential
;; complexity in terms of the input (n), as the size of n is the
;; number of bits required to represent it, which is ~log(n).
;; Hint: count the number of conses (gen-n-to-1 n) performs and make
;; sure it is O((len (gen-n-to-1 n))).

(definec gen-n-to-1 (n :pos) :tl
   XXX)

(check= (gen-n-to-1 10) '(10 9 8 7 6 5 4 3 2 1))

;; Q2
;;
;; Define gen-n-to-1 using match.

(definec gen-n-to-1-pm (n :pos) :tl
   XXX)

;; A property stating that gen-n-to-1-pm is equal to gen-n-to-1
;; This is all the testing you need for gen-n-to-1-pm!

(property (n :pos)
  (== (gen-n-to-1-pm n) (gen-n-to-1 n)))

;; Q3
;;
;; Define first-n, a function that given a true list, l, and a natural
;; number n, returns the first n elements of the list. If the list has
;; less than n elements, it returns the whole list. Do not use match.

;; Make sure that first-n has linear complexity in terms of the
;; length of l (irrespective of what n is). See above comment on
;; complexity. 

(definec first-n (l :tl n :nat) :tl
  XXX)

(check= (first-n '(1 2 3) 0) ())
(check= (first-n '(1 2 3) 2) '(1 2))

;; Q4
;;
;; Define first-n using match.

(definec first-n-pm (l :tl n :nat) :tl
   XXX)

;; A property stating that first-n-pm is equal to first-n
;; This is all the testing you need for first-n-pm!

"Property 0"

(property (l :tl n :nat)
  (== (first-n-pm l n) (first-n l n)))

;; Q5
;;
;; Define last-n, a function that given a true list, l, and a natural
;; number n, returns the last n elements of the list. If the list has
;; less than n elements, it returns the whole list. Do not use match.

;; Make sure that last-n has linear complexity in terms of the
;; length of l (irrespective of what n is). See above comment on
;; complexity. 

(definec last-n (l :tl n :nat) :tl
  XXX)

(check= (last-n '(1 2 3) 0) ())
(check= (last-n '(1 2 3) 2) '(2 3))

;; Q6
;;
;; Define last-n using match.

(definec last-n-pm (l :tl n :nat) :tl
   XXX)

;; A property stating that last-n-pm is equal to last-n
;; This is all the testing you need for last-n-pm!

"Property 1"

(property (l :tl n :nat)
  (== (last-n-pm l n) (last-n l n)))

; Recall the definition of app2 from class.

(definec app2 (x y :tl) :tl
  (match x
    (nil y)
    ((f . r) (cons f (app2 r y)))))

; Recall that the number of conses app2 performs is linear in the
; length of x.

; Recall the definition of rl from class.

;; rl: TL x Nat -> TL
;; Given a list, l, and a natural number, n, rl rotates the list
;; to the left n times

(definec rl (l :tl n :nat) :tl
  (cond ((= n 0) l)
        ((lendp l) l)
        (t (rl (app2 (tail l) (list (head l))) (1- n)))))

;; Q7
;;
;; Write a version of rl that uses match. 

(definec pm-rl (l :tl n :nat) :tl
   XXX)

;; rl is an exponential time algorithm, as discussed in class.

;; Hence, we defined a more efficient version as follows, using the
;; idea of reductions.

(definec erl (l :tl n :nat) :tl
  (match l
    (() l)
    (& (rl l (mod n (len l))))))

;; Q8
;; 
;; What is the complexity of erl in terms of the length of l?
;; Hint: count the number of conses (erl l n) performs where
;; n = (len l) - 1. Uncomment the right answer.

; (defconst *cmplxty* "constant")
; (defconst *cmplxty* "linear")
; (defconst *cmplxty* "quadratic")
; (defconst *cmplxty* "cubic")
; (defconst *cmplxty* "exponential")

;; Provide an explanation of your answer by replacing the XXX in the
;; string below with your answer.

(defconst *erl-explanation* "XXX")


;; Q9
;;
;; Define a linear time version of rl. Feel free to define any
;; helper functions you may need. The only functions you can use are the ones
;; in the ACL2s reference (click on "Lecture Notes" from the class
;; Webpage). 


(definec lrl (l :tl n :nat) :tl
   XXX)

;; Q10
;;
;; State the property that lrl is equivalent to erl.
;; Make sure you don't have any errors.

"Property 2"

(property (l :tl n :nat)
  XXX)

;; Q11
;;
;; Provide an explanation of why lrl is linear time by replacing the
;; XXX in the string below with your answer.

(defconst *lrl-explanation* "XXX")

;; Q12
;; 
;; Define the function rr.
;; rr: TX x Nat -> TL
;; 
;; (rr l n) rotates the true list l to the right n times.
;;
;; Your function should be a linear time function.

(definec rr (l :tl n :nat) :tl
  ...)

(check= (rr '(1 2 3) 1) '(3 1 2))
(check= (rr '(1 2 3) 2) '(2 3 1))
(check= (rr '(1 2 3) 3) '(1 2 3))

;; Q13
;;
;; State a property relating rr to rl. Try and write a property that
;; is as strong as possible, i.e., a property that establishes a
;; strong relationship between rr and rl.

"Property 3"

(property (l :tl n :nat)
  XXX)
