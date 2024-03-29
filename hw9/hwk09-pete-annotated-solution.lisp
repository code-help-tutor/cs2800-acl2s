WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
#|

 CS 2800 Homework 9 - Fall 2023

 - Due on Tuesday, Nov. 21 by 11:00 PM.

 - You will have to work in groups. Groups should consist of 2-3
   people. Make sure you are in exactly 1 group!  Use the
   piazza "search for teammates" post to find teammates. Please give
   students who don't have a team a home. If you can't find a team ask
   Ankit for help on Piazza. 

 - You will submit your hwk via gradescope. Instructions on how to
   do that are on Piazza. If you need help, ask on Piazza.

 - Submit this file, on Gradescope. After clicking on "Upload", you
   must add your group members to the submission by clicking on "Add
   Group Member" and then filling their names. Every group member can
   submit the homework and we will only grade the last submission. You
   are responsible for making sure that your group submits the right
   version of the homework for your final submission. We suggest you
   submit early and often. Also, you will get feedback on some
   problems when you submit. However, this feedback does not determine
   your final grade, as we will manually review
   submissions. Submission will be enabled a few days after the
   homework is released, but well before the deadline.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 For this homework you will need to use the ACL2s proof checker.
 But, you might want to use ACL2s to check properties you come up
 with.

|#

#|

 You accepted a return offer with your compiler wizard mentor,
 congrats.
 
 She gives you an update on the AI project. There are lots of bugs,
 but she doesn't have much to do, since you helped her verify her
 optimizations last time and she continued doing so for all her new
 optimizations. That was a great idea because every bug that has been
 discovered is the AI team's problem.

 Given that there are no fires to put out, she wants you to have a fun
 starter project. She mentions that during her PhD work on compilers,
 she read a paper with the "sexiest compiler optimazation" she ever
 saw. It converted insertion sort into quicksort! She wants you to
 explore that idea in ACL2s.

 You pull out your RAP book and start playting with the relevant
 definitions for isort (insertion sort). 

|#

(defdata lor (listof rational))

(definec orderedp (x :lor) :bool
  (v (endp (cdr x))
     (^ (<= (car x) (second x))
        (orderedp (cdr x)))))

(definec del (e :rational x :lor) :lor
  (cond ((endp x) nil)
        ((equal e (car x)) (cdr x))
        (t (cons (car x) (del e (cdr x))))))

(definec permp (x y :lor) :bool
  (if (endp x)
      (endp y)
    (^ (in (car x) y)
       (permp (cdr x) (del (car x) y)))))

(definec insert (a :rational x :lor) :lor
  (cond ((endp x) (list a))
        ((<= a (car x)) (cons a x))
        (t (cons (car x) (insert a (cdr x))))))

(definec isort (x :lor) :lor
  (if (endp x)
      ()
    (insert (car x) (isort (cdr x)))))

; This isn't needed, as sort-ordered will go through automatically,
; but this is a good helper theorem to have around and avoids nested
; induction proofs for sort-ordered.
(property orderedp-insert (x :rational l :lor)
  :hyps (orderedp l)
  (orderedp (insert x l)))

(property isort-ordered (x :lor)
  (orderedp (isort x)))

(property isort-permp (x :lor)
  (permp (isort x) x))
 
#|

 Next you define qsort (quicksort) as follows.

|#

(definec less (a :rational x :lor) :lor
  (cond ((endp x) x)
        ((< (car x) a)
         (cons (car x) (less a (cdr x))))
        (t (less a (cdr x)))))

(definec notless (a :rational x :lor) :lor
  (cond ((endp x) x)
        ((<= a (car x))
         (cons (car x) (notless a (cdr x))))
        (t (notless a (cdr x)))))

(definec ap (x y :tl) :tl
  (if (endp x)
      y
    (cons (car x) (ap (cdr x) y))))

(property ap-assoc (x y z :tl)
  (== (ap (ap x y) z)
      (ap x (ap y z))))

(property ap-nil (x :tl)
  (== (ap x nil) x))

; Lookup sig in RAP
; This rule implies that if we append two lists of type :lor,
; then the result is of type :lor.
(sig ap ((listof :a) (listof :a)) => (listof :a))

(definec qsort (x :lor) :lor
  (if (endp x)
      x 
    (ap (qsort (less (car x) (cdr x)))
        (cons (car x)
              (qsort (notless (car x) (cdr x)))))))

#|

 You meet with her and propose proving the following theorems.

 (property qsort-orderedp (x :lor)
   (orderedp (qsort x)))

 (property qsort-permp (x :lor)
   (permp (qsort x) x))

 In your next sync up, she tells you that the way her sorting
 algorithm will work will be a bit more complicated. When the list to
 sort becomes small enough, qsort will revert to using isort, since
 that turns out to be faster!

 So, she also wants you to prove

 (property qsort=isort (x :lor)
   (== (qsort x)
       (isort x)))
|#

#|

 You go off to start proving the theorem above in order, but then you
 recall Pete's advice:

 1. Days of proof hacking can save you hours of thinking. 
 2. Months of proof hacking can save you days of thinking. 

 So, you think and realize, hey if I prove qsort=isort, then the other
 theorem are trivial and can be proved using equational reasoning!
 
 Therefore, you try proving qsort=isort first, obviously.

 How will you prove qsort=isort? Induction, obviously.

 What scheme? Who knows? But you know the professional method and
 remember that much of the power of the professional method is the
 ability to start a proof without knowing what you're doing. You delay
 decisions for as long as possible and focus on the interesting parts.

 You don't want to do a lot of writing, so you start with some
 some abbreviations.

  A is ap,  Q is qsort,   L is less,    F is first,
  R is rest, N is notless, In is insert, I is isort

 Here we go with the interesting case.  
  
   (A (Q (L (F x) (R x))) (cons (F x) (Q (N (F x) (R x)))))
 = (In (F x) (I (R x)))

 You can assume (by induction) that 
 (Q (L (F x) (R x))) = (I (L (F x) (R x)))
 (Q (N (F x) (R x))) = (I (N (F x) (R x)))

 so now you have to show

   (A (I (L (F x) (R x))) (cons (F x) (I (N (F x) (R x)))))
 = (In (F x) (I (R x)))

 Wow. This is now just a statement about I (isort).
 You gotta love induction and the professional method. 

 Here's a proof sketch (ignoring relevant hypotheses).

 (A (I (L (F x) (R x))) (cons (F x) (I (N (F x) (R x))))) = (In (F x) (I (R x)))
 <== {generalize: replace (F x), (R x) with vars a, l }
 (A (I (L a l)) (cons a (I (N a l)))) = (In a (I l))
 =  {lemmas L1 & L2 to push I inside of L, N}
 (A (L a (I l)) (cons a (N a (I l)))) = (In a (I l))
 <== {generalize: replace (I l) with l, assume l is ordered}
 (A (L a l) (cons a (N a l))) = (In a l)

 So, you have a plan, which is to prove:

 L1: (I (L a l)) = (L a (I l))
 L2: (I (N a l)) = (N a (I l))
 L3: (O l) => (A (L a l) (cons a (N a l))) = (In a l), where O is orderedp
 L4: (O (I l))

 and that should allow you to finish the proof: (make sure
 that you understand the generalizations)

  (A (I (L (F x) (R x))) (cons (F x) (I (N (F x) (R x)))))
 = { L1, L2 }
  (A (L (F x) (I (R x))) (cons (F x) (N (F x) (I (R x)))))
 =  { L3, L4 }
  (In (F x) (R x))
 =  { Def I }
  (I x)

 Notice that L3 essentially tells you something interesting about
 qsort. It tells you that in the recursive case, qsort inserts (F x)
 into the sorted list!

 Also, we already have L4, so no need to prove that!

 To summarize, you will prove qsort=isort, without using permp.  This
 is interesting because it is an approach to specification based on
 refinement. It is conceptually easier to see that any sorting
 algorithm that is equivalent to isort is a sorting
 algorithm. Consider that students in CS2800 have difficulty coming up
 with permp, but less difficulty with defining isort.  The idea with
 refinement is that a spec is just the simplest function definition
 that does what you want it to. An advantage is that you don't need to
 argue that it is a complete spec, e.g., in our case, insertion sort
 is complete, as given any legal input it defines exactly what the
 output should be.

 If we want to base the specification for sorting on ordered
 permutations, how do we know that that is a complete specification?
 Well, we can prove that, but that requires a fair amount of work.

 Refinement is a very natural way of specifying correctness and the
 theory of refinement is very interesting, especially when you get to
 reactive systems (like network protocols, operating systems, etc).

 Finish the proof using the proof checker by proving lemmas L1, L2, L3,
 qsort=isort, qsort-orderedp and qsort-permp. 

 You will need some extra lemmas (helper theorems).

|#

#|

 Here is a solution that maximally uses ACL2s, i.e., I'm going to be
 lazy and let ACL2s do most of the work for me and then I'll go back
 and write it up.

|#

#|

 So, I'll try proving the first lemma using ACL2s.

 ; Lemma 1
 (property isort-less (l :lor a :rational)
   (== (isort (less a l))
       (less a (isort l))))

 I see that we get stuck with goals like this.

 (=> (^ ... (< (car l) a))
     (== (insert (car l)
                 (isort (less a (cdr l))))
         (less a (insert (car l) (isort (cdr l))))))

 Of course, if I had done any thinking I would have realized that I am
 trying to prove L1, which is about a relationship that isort and less
 enjoy, but isort is defined in terms of insert, so I need a lemma
 about insert and less. I want to generalize as much as possible, as
 shown below. Notice that I told ACL2s what induction scheme I want. I
 won't bother doing that for other lemmas.

|#

; Lemma 5
(property less-insert-< (l :lor a b :rational)
  :h (^ (< b a) (orderedp l))
  :b (== (insert b (less a l))
         (less a (insert b l)))
  :hints (("goal" :induct (less a l))))

#|

 Now the proof of lemma1 goes through, but ACL2s did a nested
 induction, so I'll generate a lemma for that.

|#

; Lemma 6
(property less-insert-<= (l :lor a b :rational)
  :h (<= a b)
  :b (== (less a (insert b l))
         (less a l)))

; Lemma 1
(property isort-less (l :lor a :rational)
  (== (isort (less a l))
      (less a (isort l))))

#|

 L2 is going to be essentially symmetric to L1, so here are the
 lemmas analogous to less-insert-< and less-insert-<=. Note that the
 lemmas are not exactly symmetric, e.g., for notless-insert-<=, we
 don't need the assumption that l is ordered.

 Theorem proving strategy (for paper-pencil proofs too!): make sure
 you need all the hypotheses in a property. You can easily use ACL2s
 to check if you aren't sure.  So, get into the habit of removing hyps
 and seeing if you get proofs or counterexamples. Following advice,
 did I need the (orderedp l) hypothesis for less-insert-<? Yes, since
 I get counterexamples if I remove the hypothesis.

 BTW, ACL2s can prove L2, but performs nested inductions.

|#

; Lemma 7
(property notless-insert-<= (l :lor a b :rational)
  :h (<= a b)
  :b (== (insert b (notless a l))
         (notless a (insert b l))))

; Lemma 8
(property notless-insert-< (l :lor a b :rational)
  :h (< b a)
  :b (== (notless a (insert b l))
         (notless a l)))

; Lemma 2 
(property isort-notless (l :lor a :rational)
  (== (isort (notless a l))
      (notless a (isort l))))

#|

 OK. Only Lemma 3 is left. Let's try it.

 ; Lemma 3
 (property ap-less-not-less (l :lor a :rational)
   :h (orderedp l)
   :b (== (ap (less a l) (cons a (notless a l)))
          (insert a l)))


 I get subgoals of the form

 (=> (^ ... (<= a (car l)) (orderedp (cdr l)))
     (== (ap (less a (cdr l))
             (list* a (car l) (notless a (cdr l))))
         (cons a l))) 

 This is interesting because if (<= a (car l)) and (orderedp l)
 hold, then (less a l) is empty.
 
 Let's prove that.

|#

; Lemma 9
(property less-nil (l :lor a :rational)
  :h (^ (consp l) (orderedp l) (<= a (car l)))
  (== (less a l) nil))

; And another one done.
; Lemma 3
(property ap-less-not-less (l :lor a :rational)
  :h (orderedp l)
  :b (== (ap (less a l) (cons a (notless a l)))
         (insert a l)))

; Did my hard work pay off?
; If yes, then the this proof should go through.

(property qsort=isort (x :lor)
  (== (qsort x)
      (isort x)))

; Now the last two theorems follow from equational reasoning. 
(property qsort-orderedp (x :lor)
  (orderedp (qsort x)))

(property qsort-permp (x :lor)
  (permp (qsort x) x))

; Go back and do L1 in the proof checker.  Now that you have the
; induction schemes and the lemmas you need, it is just equational
; reasoning and crossing t's and dotting i's.



; Wrapping up, if I didn't care about nested inductions, below is a
; short proof script with all the properties I need.

; First, let me undo up to the definition of qsort.
(ubt! 'less-insert-<)

; And here is the proof script.
(property less-insert-< (l :lor a b :rational)
  :h (^ (< b a) (orderedp l))
  :b (== (insert b (less a l))
         (less a (insert b l)))
  :hints (("goal" :induct (less a l))))

(property isort-less (l :lor a :rational)
  (== (isort (less a l))
      (less a (isort l))))

(property isort-notless (l :lor a :rational)
  (== (isort (notless a l))
      (notless a (isort l))))

(property less-nil (l :lor a :rational)
  :h (^ (consp l) (orderedp l) (<= a (car l)))
  (== (less a l) nil))

(property ap-less-not-less (l :lor a :rational)
  :h (orderedp l)
  :b (== (ap (less a l) (cons a (notless a l)))
         (insert a l)))

(property qsort=isort (x :lor)
  (== (qsort x)
      (isort x)))

(property qsort-orderedp (x :lor)
  (orderedp (qsort x)))

(property qsort-permp (x :lor)
  (permp (qsort x) x))

