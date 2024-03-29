WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
(acl2s-defaults :set testing-enabled nil)

(definec in (a :all x :tl) :bool
  (and (consp x)
       (or (== a (car x))
           (in a (cdr x)))))

(definec ap (x y :tl) :tl
  (if (endp x)
      y
    (cons (car x) (ap (cdr x) y))))

(definec rv (x :tl) :tl
  (if (endp x)
      x
    (ap (rv (cdr x)) (list (car x)))))

(definec rem-dups (x :tl) :tl
  (cond ((endp x) x)
        ((in (car x) (cdr x))
         (rem-dups (cdr x)))
        (t (cons (car x) (rem-dups (cdr x))))))

; You get this property for free, since we did it in class.  See
; l26.proof for the proof checker proof. You will have to do similar
; proofs for this homework.

(property ap-assoc (x y z :tl)
  (== (ap (ap x y) z)
      (ap x (ap y z))))

; The first two lemmas are proof checker proofs of in-ap using
; different induction schemes.

Lemma in-ap1:
(=> (^ (tlp x) (tlp y))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Proof by: Induction on (in a x)


Contract Case 1:
(=> (! (^ (tlp x) (tlp y)))
    (=> (^ (tlp x) (tlp y))
        (== (in a (ap x y))
            (v (in a x) (in a y)))))

Exportation:
(=> (^ (! (^ (tlp x) (tlp y)))
       (tlp x)
       (tlp y))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Context:
C1. (! (^ (tlp x) (tlp y)))
C2. (tlp x)
C3. (tlp y)

Derived Context:
D1. nil {C1, C2, C3, PL}

QED

Base Case 1:
(=> (^ (tlp x) (tlp y) (! (consp x)))
    (=> (^ (tlp x) (tlp y))
        (== (in a (ap x y))
            (v (in a x) (in a y)))))

Exportation:
(=> (^ (tlp x)
       (tlp y)
       (! (consp x)))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (! (consp x))

Derived Context:
D1. (== x nil) { C1, C3, Def tlp }

Goal: (== (in a (ap x y))
          (v (in a x) (in a y)))

Proof:
(in a (ap x y))
== { D1, Def ap }
(in a y)
== { PL }
(v nil (in a y))
== { D1, Def in, PL }
(v (in a x) (in a y))

QED


Base Case 2:
(=> (^ (tlp x) (tlp y) (consp x) (== a (car x)))
    (=> (^ (tlp x) (tlp y))
        (== (in a (ap x y))
            (v (in a x) (in a y)))))

Exportation:
(=> (^ (tlp x)
       (tlp y)
       (consp x)
       (== a (car x)))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (consp x)
C4. (== a (car x))

Goal: (== (in a (ap x y))
          (v (in a x) (in a y)))

Proof:
(in a (ap x y))
== { C3, Def ap }
(in a (cons (car x) (ap (cdr x) y)))
== { C4, Def in, cons axioms }
t
== { C4, Def in, PL }
(v (in a x) (in a y))

QED


Induction Case 1:
(=> (^ (tlp x) (tlp y) (consp x) (!= a (car x))
       (=> (^ (tlp (cdr x)) (tlp y))
           (== (in a (ap (cdr x) y))
               (v (in a (cdr x)) (in a y)))))
    (=> (^ (tlp x) (tlp y))
        (== (in a (ap x y))
            (v (in a x) (in a y)))))

Exportation:
(=> (^ (tlp x)
       (tlp y)
       (consp x)
       (!= a (car x))
       (=> (^ (tlp (cdr x)) (tlp y))
           (== (in a (ap (cdr x) y))
               (v (in a (cdr x)) (in a y)))))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (consp x)
C4. (!= a (car x))
C5. (=> (^ (tlp (cdr x)) (tlp y))
        (== (in a (ap (cdr x) y))
            (v (in a (cdr x)) (in a y))))

Derived Context:
D1. (tlp (cdr x)) { C1, C3, Def tlp }
D2. (== (in a (ap (cdr x) y))
        (v (in a (cdr x)) (in a y)))
    { C5, D1, C2, MP }

Goal: (== (in a (ap x y))
          (v (in a x) (in a y)))

Proof:
(in a (ap x y))
== { C3, Def ap }
(in a (cons (car x) (ap (cdr x) y)))
== { cons axioms, Def in, C4 }
(in a (ap (cdr x) y))
== { D2 }
(v (in a (cdr x)) (in a y))
== { C4, Def in, cons axioms }
(v (in a x) (in a y))

QED

QED


Lemma in-ap2:
(=> (^ (tlp x) (tlp y))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Proof by: Induction on (tlp x)

Base Case 1:
(=> (! (consp x))
    (=> (^ (tlp x) (tlp y))
        (== (in a (ap x y))
            (v (in a x) (in a y)))))

Exportation:
(=> (^ (tlp x)
       (tlp y)
       (! (consp x)))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (! (consp x))

Derived Context:
D1. (== x nil) { C1, C3, Def tlp }

Goal: (== (in a (ap x y))
          (v (in a x) (in a y)))

Proof:
(in a (ap x y))
== { D1, Def ap }
(in a y)
== { PL }
(v nil (in a y))
== { D1, Def in, PL }
(v (in a x) (in a y))

QED


Induction Case 1:
(=> (^ (consp x)
       (=> (^ (tlp (cdr x)) (tlp y))
           (== (in a (ap (cdr x) y))
               (v (in a (cdr x)) (in a y)))))
    (=> (^ (tlp x) (tlp y))
        (== (in a (ap x y))
            (v (in a x) (in a y)))))

Exportation:
(=> (^ (tlp x)
       (tlp y)
       (consp x)
       (=> (^ (tlp (cdr x)) (tlp y))
           (== (in a (ap (cdr x) y))
               (v (in a (cdr x)) (in a y)))))
    (== (in a (ap x y))
        (v (in a x) (in a y))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (consp x)
C4. (=> (^ (tlp (cdr x)) (tlp y))
        (== (in a (ap (cdr x) y))
            (v (in a (cdr x)) (in a y))))

Derived Context:
D1. (tlp (cdr x)) { C1, C3, Def tlp }
D2. (== (in a (ap (cdr x) y))
        (v (in a (cdr x)) (in a y)))
    { C4, D1, C2, MP }

Goal: (== (in a (ap x y))
          (v (in a x) (in a y)))

Proof:
(in a (ap x y))
== { C3, Def ap }
(in a (cons (car x) (ap (cdr x) y)))
== { Def in, cons axioms }
(v (== a (car x))
   (in a (ap (cdr x) y)))
== { D2, PL }
(v (== a (car x))
   (in a (cdr x))
   (in a y))
== { PL, Def in }
(v (in a x)
   (in a y))

QED

QED

#|

 Which of the following induction schemes is not viable
 to prove Conjecture 2?
 
 1. (ap x y)
 2. (in a y)

 Explain why not by showing where a proof attempt using the non-viable
 induction scheme fails.

 XXX

|#

; Notice that you can use lemmas you have proved in subsequent proofs,
; e.g., you can use in-ap1 in the proof of in-rv or any other subsequent lemma.

Lemma in-rv:
(=> (tlp x)
    (== (in a (rv x))
        (in a x)))

Proof by: Induction on (rv x)

Contract Case 1:
(=> (! (tlp x))
    (=> (tlp x)
        (== (in a (rv x))
            (in a x))))

Exportation:
(=> (^ (! (tlp x))
       (tlp x))
    (== (in a (rv x))
        (in a x)))

Context:
C1. (! (tlp x))
C2. (tlp x)

Derived Context:
D1. nil { C1, C2, PL }

QED

Base Case 1:
(=> (^ (tlp x) (endp x))
    (=> (tlp x)
        (== (in a (rv x))
            (in a x))))

Exportation:
(=> (^ (tlp x)
       (endp x))
    (== (in a (rv x))
        (in a x)))

Context:
C1. (tlp x)
C2. (endp x)

Derived Context:
D1. (== x nil) { C1, C2, Def tlp }

Goal: (== (in a (rv x))
          (in a x))

Proof:
(in a (rv x))
== { D1, Def rv }
(in a nil)
== { C2 }
(in a x)

QED


Induction Case 1:
(=> (^ (tlp x)
       (! (endp x))
       (=> (tlp (cdr x))
           (== (in a (rv (cdr x)))
               (in a (cdr x)))))
    (=> (tlp x)
        (== (in a (rv x))
            (in a x))))

Exportation:
(=> (^ (tlp x)
       (! (endp x))
       (=> (tlp (cdr x))
           (== (in a (rv (cdr x)))
               (in a (cdr x)))))
    (== (in a (rv x))
        (in a x)))

Context:
C1. (tlp x)
C2. (! (endp x))
C3. (=> (tlp (cdr x))
        (== (in a (rv (cdr x)))
            (in a (cdr x))))

Derived Context:
D1. (tlp (cdr x)) { C1, C2, Def tlp }
D2. (== (in a (rv (cdr x)))
        (in a (cdr x)))
    { C3, D1, MP }

Goal: (== (in a (rv x))
          (in a x))

Proof:
(in a (rv x))
== { C2, Def rv }
(in a (ap (rv (cdr x)) (list (car x))))
== { Lemma in-ap1 ((x (rv (cdr x))) (y (list (car x)))) }
(v (in a (rv (cdr x))) (in a (list (car x))))
== { D2 }
(v (in a (cdr x)) (in a (list (car x))))
== { PL }
(v (in a (list (car x))) (in a (cdr x)))
== { Lemma in-ap1 ((x (list (car x))) (y (cdr x))) }
(in a (ap (list (car x)) (cdr x)))
== { Def ap, C2, cons axioms }
(in a x)

QED

QED


; This is a proof of in-rem-dups
Lemma in-rem-dups:
(=> (tlp x)
    (== (in a (rem-dups x))
        (in a x)))

Proof by: Induction on (rem-dups x)

Contract Case 1:
(=> (! (tlp x))
    (=> (tlp x)
        (== (in a (rem-dups x))
            (in a x))))

Exportation:
(=> (^ (! (tlp x))
       (tlp x))
    (== (in a (rem-dups x))
        (in a x)))

Context:
C1. (! (tlp x))
C2. (tlp x)

Derived Context:
D1. nil { C1, C2, PL }

QED

Base Case 1:
(=> (^ (tlp x) (endp x))
    (=> (tlp x)
        (== (in a (rem-dups x))
            (in a x))))

Exportation:
(=> (^ (tlp x)
       (endp x))
    (== (in a (rem-dups x))
        (in a x)))

Context:
C1. (tlp x)
C2. (endp x)

Derived Context:
D1. (== x nil) { C1, C2, Def tlp }

Goal: (== (in a (rem-dups x))
          (in a x))

Proof:
(in a (rem-dups x))
== { D1, Def rem-dups }
(in a nil)
== { C2 }
(in a x)

QED


Induction Case 1:
(=> (^ (tlp x)
       (! (endp x))
       (in (car x) (cdr x))
       (=> (tlp (cdr x))
           (== (in a (rem-dups (cdr x)))
               (in a (cdr x)))))
    (=> (tlp x)
        (== (in a (rem-dups x))
            (in a x))))

Exportation:
(=> (^ (tlp x)
       (! (endp x))
       (in (car x) (cdr x))
       (=> (tlp (cdr x))
           (== (in a (rem-dups (cdr x)))
               (in a (cdr x)))))
    (== (in a (rem-dups x))
        (in a x)))

Context:
C1. (tlp x)
C2. (! (endp x))
C3. (in (car x) (cdr x))
C4. (=> (tlp (cdr x))
        (== (in a (rem-dups (cdr x)))
            (in a (cdr x))))

Derived Context:
D1. (tlp (cdr x)) { C1, C2, Def tlp }
D2. (== (in a (rem-dups (cdr x)))
        (in a (cdr x)))
    { C4, D1, MP }

Goal: (== (in a (rem-dups x))
          (in a x))

Proof:
(in a (rem-dups x))
== { C2, C3, Def rem-dups }
(in a (rem-dups (cdr x)))
== { D2 }
(in a (cdr x))
== { Def in, C2, C3 }
(in a x)

QED


Induction Case 2:
(=> (^ (tlp x)
       (! (endp x))
       (! (in (car x) (cdr x)))
       (=> (tlp (cdr x))
           (== (in a (rem-dups (cdr x)))
               (in a (cdr x)))))
    (=> (tlp x)
        (== (in a (rem-dups x))
            (in a x))))

Exportation:
(=> (^ (tlp x)
       (! (endp x))
        (! (in (car x) (cdr x)))
       (=> (tlp (cdr x))
           (== (in a (rem-dups (cdr x)))
               (in a (cdr x)))))
    (== (in a (rem-dups x))
        (in a x)))

Context:
C1. (tlp x)
C2. (! (endp x))
C3.  (! (in (car x) (cdr x)))
C4. (=> (tlp (cdr x))
        (== (in a (rem-dups (cdr x)))
            (in a (cdr x))))

Derived Context:
D1. (tlp (cdr x)) { C1, C2, Def tlp }
D2. (== (in a (rem-dups (cdr x)))
        (in a (cdr x)))
    { C4, D1, MP }

Goal: (== (in a (rem-dups x))
          (in a x))

Proof:
(in a (rem-dups x))
== { C2, C3, Def rem-dups }
(in a (cons (car x) (rem-dups (cdr x))))
== { Def ap, cons axioms }
(in a (ap (list (car x)) (rem-dups (cdr x))))
== { Lemma in-ap1 ((x (list (car x))) (y (rem-dups (cdr x)))) }
(v (in a (list (car x))) (in a (rem-dups (cdr x))))
== { D2 }
(v (in a (list (car x))) (in a (cdr x)))
== { Lemma in-ap1 ((x (list (car x))) (y (cdr x))) }
(in a (ap (list (car x)) (cdr x)))
== { cons axioms, Def ap, C2 }
(in a x)

QED

QED


#|

 Formalize this property and prove it using the above lemmas.
 Hint: do not use induction, just equational reasoning!

 (property (el :all a b c d :tl)
   (== (in el (rem-dups (rv (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d))))))
       (v (in el a) (in el b) (in el c) (in el d))))

|#

Conjecture sanity-check:
(=> (^ (tlp a)
       (tlp b)
       (tlp c)
       (tlp d))
    (== (in el (rem-dups (rv (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d))))))
        (v (in el a) (in el b) (in el c) (in el d))))

Context:
C1. (tlp a)
C2. (tlp b)
C3. (tlp c)
C4. (tlp d)

Goal: (== (in el (rem-dups (rv (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d))))))
          (v (in el a) (in el b) (in el c) (in el d)))

Proof:
(in el (rem-dups (rv (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d))))))
== { Lemma in-rem-dups ((a el) (x (rv (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d)))))) }
(in el (rv (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d)))))
== { Lemma in-rv ((a el) (x (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d))))) }
(in el (rem-dups (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d))))
== { Lemma in-rem-dups ((a el) (x (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d)))) }
(in el (rv (ap (rv (ap (rv (ap a b)) (ap a c))) d)))
== { Lemma in-rv ((a el) (x (ap (rv (ap (rv (ap a b)) (ap a c))) d))) }
(in el (ap (rv (ap (rv (ap a b)) (ap a c))) d))
== { Lemma in-ap2 ((a el) (x (rv (ap (rv (ap a b)) (ap a c)))) (y d)) }
(v (in el (rv (ap (rv (ap a b)) (ap a c))))
   (in el d))
== { Lemma in-rv ((a el) (x (ap (rv (ap a b)) (ap a c)))) }
(v (in el (ap (rv (ap a b)) (ap a c)))
   (in el d))
== { Lemma in-ap2 ((a el) (x (rv (ap a b))) (y (ap a c))) }
(v (in el (rv (ap a b)))
   (in el (ap a c))
   (in el d))
== { Lemma in-rv ((a el) (x (ap a b))) }
(v (in el (ap a b))
   (in el (ap a c))
   (in el d))
== { Lemma in-ap2 ((a el) (x a) (y b)), PL }
(v (in el a)
   (in el b)
   (in el (ap a c))
   (in el d))
== { Lemma in-ap2 ((a el) (x a) (y c)), PL }
(v (in el a)
   (in el b)
   (in el c)
   (in el d))

QED


; Prove the following lemma. You will need helper lemmas.
; Hint: the lecture notes are your friend.


Lemma ap-nil:
(=> (tlp x)
    (== (ap x nil) x))

Proof by: Induction on (tlp x)

Base Case 1:
(=> (! (consp x))
    (=> (tlp x)
        (== (ap x nil) x)))

Exportation:
(=> (^ (tlp x)
       (! (consp x)))
    (== (ap x nil) x))

Context:
C1. (tlp x)
C2. (! (consp x))

Derived Context:
D1. (== x nil) { C1, C2, Def tlp }

Goal: (== (ap x nil) x)

Proof:
(ap x nil)
== { D1 }
(ap nil nil)
== { Def ap }
nil
== { D1 }
x

QED

Induction Case 1:
(=> (^ (consp x)
       (=> (tlp (cdr x))
           (== (ap (cdr x) nil) (cdr x))))
    (=> (tlp x)
        (== (ap x nil) x)))

Exportation:
(=> (^ (tlp x)
       (consp x)
       (=> (tlp (cdr x))
           (== (ap (cdr x) nil) (cdr x))))
    (== (ap x nil) x))

Context:
C1. (tlp x)
C2. (consp x)
C3. (=> (tlp (cdr x))
        (== (ap (cdr x) nil) (cdr x)))

Derived Context:
D1. (tlp (cdr x)) { C1, C2, Def tlp }
D2. (== (ap (cdr x) nil) (cdr x)) { C3, D1, MP }

Goal: (== (ap x nil) x)

Proof:
(ap x nil)
== { Def ap, C2 }
(cons (car x) (ap (cdr x) nil))
== { D2 }
(cons (car x) (cdr x))
== { cons axioms }
x

QED

QED

Lemma rv-ap:
(=> (^ (tlp x)
       (tlp y))
    (== (rv (ap x y))
        (ap (rv y) (rv x))))

Proof by: Induction on (tlp x)

Base Case 1:
(=> (! (consp x))
    (=> (^ (tlp x)
           (tlp y))
        (== (rv (ap x y))
            (ap (rv y) (rv x)))))

Exportation:
(=> (^ (tlp x)
       (tlp y)
       (! (consp x)))
    (== (rv (ap x y))
        (ap (rv y) (rv x))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (! (consp x))


Derived Context:
D1. (== x nil) { C1, C3, Def tlp }

Goal: (== (rv (ap x y))
          (ap (rv y) (rv x)))

Proof:
(rv (ap x y))
== { D1 }
(rv (ap nil y))
== { Def ap }
(rv y)
== { Lemma ap-nil ((x (rv y))) }
(ap (rv y) nil)
== { Def rv, D1}
(ap (rv y) (rv x))

QED

Induction Case 1:
(=> (^ (consp x)
       (=> (^ (tlp (cdr x))
              (tlp y))
           (== (rv (ap (cdr x) y))
               (ap (rv y) (rv (cdr x))))))
    (=> (^ (tlp x) (tlp y))
        (== (rv (ap x y))
            (ap (rv y) (rv x)))))

Exportation:
(=> (^ (tlp x)
       (tlp y)
       (consp x)
       (=> (^ (tlp (cdr x))
              (tlp y))
           (== (rv (ap (cdr x) y))
               (ap (rv y) (rv (cdr x))))))
    (== (rv (ap x y))
        (ap (rv y) (rv x))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (consp x)
C4. (=> (^ (tlp (cdr x))
           (tlp y))
        (== (rv (ap (cdr x) y))
            (ap (rv y) (rv (cdr x)))))

Derived Context:
D1. (tlp (cdr x)) { C1, C3, Def tlp }
D2. (== (rv (ap (cdr x) y))
        (ap (rv y) (rv (cdr x))))
{ C4, D1, C2, MP }

Goal: (== (rv (ap x y))
          (ap (rv y) (rv x)))

Proof:
(rv (ap x y))
== { Def ap, C3 }
(rv (cons (car x) (ap (cdr x) y)))
== { Def rv, cons axioms }
(ap (rv (ap (cdr x) y)) (list (car x)))
== { D2 }
(ap (ap (rv y) (rv (cdr x))) (list (car x)))
== { Lemma ap-assoc ((x (rv y)) (y (rv (cdr x))) (z (list (car x))))}
(ap (rv y) (ap (rv (cdr x)) (list (car x))))
== { Def rv, C3 }
(ap (rv y) (rv x))

QED

QED



Lemma rv-rv:
(=> (tlp x)
    (== (rv (rv x))
        x))

Proof by: Induction on (tlp x)

Base Case 1:
(=> (! (consp x))
    (=> (tlp x)
        (== (rv (rv x))
            x)))

Exportation:
(=> (^ (tlp x)
       (! (consp x)))
    (== (rv (rv x))
        x))

Context:
C1. (tlp x)
C2. (! (consp x))

Derived Context:
D1. (== x nil) { C1, C2, Def tlp }

Goal: (== (rv (rv x))
          x)

Proof:
(rv (rv x))
== { Def rv, C2 }
(rv nil)
== { Def rv }
nil
== { D1 }
x

QED
       

Induction Case 1:
(=> (^ (consp x)
       (=> (tlp (cdr x))
           (== (rv (rv (cdr x)))
               (cdr x))))
    (=> (tlp x)
        (== (rv (rv x))
            x)))

Exportation:
(=> (^ (tlp x)
       (consp x)
       (=> (tlp (cdr x))
           (== (rv (rv (cdr x)))
               (cdr x))))
    (== (rv (rv x))
        x))
    
    
Context:
C1. (tlp x)
C2. (consp x)
C3. (=> (tlp (cdr x))
        (== (rv (rv (cdr x)))
            (cdr x)))

Derived Context:
D1. (tlp (cdr x)) { C1, C2, Def tlp }
D2. (== (rv (rv (cdr x)))
        (cdr x))
    { C3, D1, MP }

Goal: (== (rv (rv x)) x)

Proof:
(rv (rv x))
== { Def rv, C2 }
(rv (ap (rv (cdr x)) (list (car x))))
== { Lemma rv-ap ((x (rv (cdr x))) (y (list (car x)))) }
(ap (rv (list (car x))) (rv (rv (cdr x))))
== { D2 }
(ap (rv (list (car x))) (cdr x))
== { Def rv, cons axioms }
(ap (ap (rv nil) (list (car x))) (cdr x))
== { Def rv }
(ap (ap nil (list (car x))) (cdr x))
== { Def ap }
(ap (list (car x)) (cdr x))
== { cons axioms, Def ap }
x

QED

QED



; Here is another function that your mentor wants you to reason about.
(definec make-n-xs (n :nat x :all) :tl
  (if (zp n)
      nil
    (cons x (make-n-xs (1- n) x))))

; She claims that the following is a theorem you should prove.
; Actually, it isn't a theorem. Think about why and change the RHS as
; little as possible to make this a theorem and prove it. You can only
; change the RHS.
Lemma in-make-n-xs:
(=> (natp x)
    (== (in a (make-n-xs x y))
        (^ (! (zp x))
           (== a y))))

Proof by: Induction on (make-n-xs x y)

Contract Case 1:
(=> (! (natp x))
    (=> (natp x)
        (== (in a (make-n-xs x y))
            (^ (! (zp x))
               (== a y)))))

Exportation:
(=> (^ (! (natp x))
       (natp x))
    (== (in a (make-n-xs x y))
        (^ (! (zp x))
           (== a y))))

Context:
C1. (! (natp x))
C2.  (natp x)

Derived Context:
D1. nil { C1, C2, PL }

QED
    

Base Case 1:
(=> (zp x)
    (=> (natp x)
        (== (in a (make-n-xs x y))
            (^ (! (zp x))
               (== a y)))))

Exportation:
(=> (^ (natp x)
       (zp x))
    (== (in a (make-n-xs x y))
        (^ (! (zp x))
           (== a y))))

Context:
C1. (natp x)
C2. (zp x)

Goal: (== (in a (make-n-xs x y))
          (^ (! (zp x))
             (== a y)))

Proof:
(in a (make-n-xs x y))
== { Def make-n-xs, C2 }
(in a nil)
== { Def in }
nil
== { C2, PL }
(^ (! (zp x))
   (== a y))

QED


Induction Case 1:
(=> (^ (! (zp x))
       (=> (natp (1- x))
           (== (in a (make-n-xs (1- x) y))
               (^ (! (zp (1- x)))
                  (== a y)))))
    (=> (natp x)
        (== (in a (make-n-xs x y))
            (^ (! (zp x))
               (== a y)))))


Exportation:
(=> (^ (natp x)
       (! (zp x))
       (=> (natp (1- x))
           (== (in a (make-n-xs (1- x) y))
               (^ (! (zp (1- x)))
                  (== a y)))))
    (== (in a (make-n-xs x y))
        (^ (! (zp x))
           (== a y))))

Context:
C1. (natp x)
C2. (! (zp x))
C3. (=> (natp (1- x))
        (== (in a (make-n-xs (1- x) y))
            (^ (! (zp (1- x)))
               (== a y))))

Derived Context:
D1. (natp (1- x)) { C1, C2, Obvious }
D2. (== (in a (make-n-xs (1- x) y))
        (^ (! (zp (1- x)))
           (== a y)))
{ C3, D1, MP }

Goal: (== (in a (make-n-xs x y))
          (^ (! (zp x))
             (== a y)))

Proof:
(in a (make-n-xs x y))
== { Def make-n-xs, C2 }
(in a (cons y (make-n-xs (1- x) y)))
== { cons axioms, Def ap }
(in a (ap (list y) (make-n-xs (1- x) y)))
== { Lemma in-ap1 ((x (list y)) (y (make-n-xs (1- x) y))) }
(v (in a (list y))
   (in a (make-n-xs (1- x) y)))
== { D2, PL }
(v (in a (list y))
   (^ (! (zp (1- x)))
      (== a y)))
== { Def in, cons axioms, PL }
(v (== a y)
   (^ (! (zp (1- x)))
      (== a y)))
== { PL }
(== a y)
== { C2, PL }
(^ (! (zp x))
   (== a y))

QED

QED


   

;; Your mentor is busy building her compiler and you have some free
;; time. After doing some LeetCode exercises, you get bored and decide
;; to go talk to the AI team. They are building an AI that can solve
;; recurrence relations. They gave you a few examples that they want to
;; be able to solve.
;;
;; Find closed form solutions and prove them correct.

(definec r1 (n :nat) :pos
  (if (zp n)
      1
    (+ (r1 (1- n)) (expt 2 n))))

Lemma r1-closed-form:
(=> (natp n)
	(= (r1 n)
   	   (1- (expt 2 (1+ n)))))

Proof by: Induction on (r1 n)

Contract Case 1:
(=> (! (natp n))
	(=> (natp n)
		(=  (r1 n)
   	   		(1- (expt 2 (1+ n))))))

Exportation:
(=> (^ 	(! (natp n))
		(natp n))
	(=  (r1 n)
   	   		(1- (expt 2 (1+ n)))))

Context:
C1. (! (natp n))
C2. (natp n)


Derived Context:
D1. nil { C1, C2, PL }

QED

Base Case 1:
(=> (zp n)
	(=> (natp n)
		(=  (r1 n)
   	   		(1- (expt 2 (1+ n))))))
   	   		
Exportation:
(=> (^	(natp n) 	
		(zp n))
	(=  (r1 n)
   	   	(1- (expt 2 (1+ n)))))

Context:
C1. (natp n) 
C2. (zp n)
  	   		
Goal: (= (r1 n)
   	     (1- (expt 2 (1+ n))))

Proof:
(= (r1 n) (1- (expt 2 (1+ n))))
== { C2, Def r1 }
(= 1 (1- (expt 2 (1+ n))))
== { Arith, C2 }
t

QED


Induction Case 1:
(=> (^ 	(! (zp n))
		(=> (natp (1- n))
			(=  (r1 (1- n))
   	   			(1- (expt 2 (1+ (1- n)))))))
	(=> (natp n)
		(=  (r1 n)
   	   		(1- (expt 2 (1+ n))))))

Exportation:
(=> (^ 	(natp n)
		(! (zp n))
		(=> (natp (1- n))
			(=  (r1 (1- n))
	   	   		(1- (expt 2 (1+ (1- n)))))))
	(=  (r1 n)
   	   	(1- (expt 2 (1+ n)))))

Context:
C1. (natp n)
C2. (! (zp n))
C3. (=> (natp (1- n))
		(=  (r1 (1- n))
	   	   	(1- (expt 2 (1+ (1- n))))))


Derived Context:
D1. (natp (1- n)) { C1, C2, Obvious }
D2. (=  (r1 (1- n))
	   	(1- (expt 2 (1+ (1- n))))) { C3, D1, MP }
D3. (= 	(r1 (1- n))
		(1- (expt 2 n))) { Arith, D2 }

Goal: (= (r1 n)
   	     (1- (expt 2 (1+ n))))

Proof:
(r1 n)
== { Def r1, C2 }
(+ (r1 (1- n)) (expt 2 n))
== { D3 }
(+ (1- (expt 2 n)) (expt 2 n))
== { Arith }
(1- (expt 2 (1+ n)))
QED
QED



;; ===== r2 =======

(definec r2 (n :pos) :int
  :skip-tests t
  (match n
    (1 0)
    (2 3)
    (3 8)
    (& (+ (r2 (1- n)) (r2 (- n 2)) (- (r2 (- n 3))) 4))))


Lemma r2-closed-form:
(=> (posp n)
	(= (r2 n)
	   (1- (expt n 2))))


Proof by: Induction on (r2 n)


Contract Case 1:
(=> (! (posp n))
	(=> (posp n)
		(= 	(r2 n)
	   	   	(1- (expt n 2)))))
	 
Exportation:
(=> (^ 	(! (posp n))
		(posp n))
	(= 	(r2 n)
	   	(1- (expt n 2))))
	
Context:
C1. (! (posp n))
C2. (posp n)

Derived Context:
D1. nil { C1, C2, PL }

QED


Base Case 1:
(=> (^  (posp n)
	    (eql n 1))
	(=> (posp n)
		(= (r2 n)
	   	   (1- (expt n 2)))))
	 
Exportation:
(=> (^ 	(posp n)
		(eql n 1))
	(=  (r2 n)
	   	(1- (expt n 2))))
	
Context:
C1. (posp n)
C2. (eql n 1)

Goal: 
(= 	(r2 n)
	(1- (expt n 2)))
	
Proof:
(= (r2 n) (1- (expt n 2)))
== { C2, eval }
t
QED


Base Case 2:
(=> (^  (posp n)
	    (eql n 2))
	(=> (posp n)
		(= 	(r2 n)
	   	   	(1- (expt n 2)))))
	 
Exportation:
(=> (^ 	(posp n)
		(eql n 2))
	(= 	(r2 n)
	   	(1- (expt n 2))))
	
Context:
C1. (posp n)
C2. (eql n 2)

Goal: 
(= 	(r2 n)
	(1- (expt n 2)))
	
Proof:
(= (r2 n) (1- (expt n 2)))
== { C2, eval }
t
QED



Base Case 3:
(=> (^  (posp n)
	    (eql n 3))
	(=> (posp n)
		(= 	(r2 n)
	   	   	(1- (expt n 2)))))
	 
Exportation:
(=> (^ 	(posp n)
		(eql n 3))
	(= 	(r2 n)
	   	(1- (expt n 2))))
	
Context:
C1. (posp n)
C2. (eql n 3)

Goal: 
(= 	(r2 n)
	(1- (expt n 2)))
	
Proof:
(= (r2 n) (1- (expt n 2)))
== { C2, eval }
t
QED


Induction Case 1:
(=> (^ (posp n)
	   (! (eql n 1))
       (! (eql n 2))
       (! (eql n 3))
       (=> (posp (1- n))
           (= (r2 (1- n)) 
              (1- (expt (1- n) 2))))
       (=> (posp (- n 2))
           (= (r2 (- n 2)) 
              (1- (expt (- n 2) 2))))
       (=> (posp (- n 3))
           (= (r2 (- n 3)) 
              (1- (expt (- n 3) 2)))))
    (=> (posp n)
        (= (r2 n)
           (1- (expt n 2)))))

Exportation:
(=> (^	(posp n)
		(! (eql n 1))
		(! (eql n 2))
		(! (eql n 3))
		(=> (posp (1- n))
			(= 	(r2 (1- n)) 
				(1- (expt (1- n) 2))))
		(=> (posp (- n 2))
			(= 	(r2 (- n 2)) 
				(1- (expt (- n 2) 2))))
		(=> (posp (- n 3))
			(= 	(r2 (- n 3)) 
				(1- (expt (- n 3) 2)))))
	(= 	(r2 n)
	   	(1- (expt n 2))))
	   	   	
Context:
C1. (posp n)
C2. (! (eql n 1))
C3. (! (eql n 2))
C4. (! (eql n 3))
C5. (=> (posp (1- n))
		(= 	(r2 (1- n)) 
			(1- (expt (1- n) 2))))
C6. (=> (posp (- n 2))
		(= 	(r2 (- n 2)) 
			(1- (expt (- n 2) 2))))
C7.	(=> (posp (- n 3))
		(= 	(r2 (- n 3)) 
			(1- (expt (- n 3) 2))))

Derived Context:
D1. (posp (1- n)) { C1, C2 }
D2. (posp (- n 2)) { C1, C2, C3 }
D3. (posp (- n 3)) { C1, C2, C3, C4 }
D4. (= 	(r2 (1- n)) 
		(1- (expt (1- n) 2))) { C5, D1 }
D5. (= 	(r2 (- n 2)) 
		(1- (expt (- n 2) 2))) { C6, D2 }
D6. (= 	(r2 (- n 3)) 
		(1- (expt (- n 3) 2))) { C7, D3 }
		
Goal: 
(= 	(r2 n)
	(1- (expt n 2)))

Proof:
(r2 n)
== { Def r2, C1, C2, C3, C4 }
(+ (r2 (1- n)) (r2 (- n 2)) (- (r2 (- n 3))) 4)
== { D4 }
(+ (1- (expt (1- n) 2)) (r2 (- n 2)) (- (r2 (- n 3))) 4)
== { D5 }
(+ (1- (expt (1- n) 2)) (1- (expt (- n 2) 2)) (- (r2 (- n 3))) 4)
== { D6 }
(+ (1- (expt (1- n) 2)) (1- (expt (- n 2) 2)) (- (1- (expt (- n 3) 2))) 4)
== { Def expt }
(+ (1- (* (1- n) (1- n))) 
   (1- (* (- n 2) (- n 2)))
   (- (1- (* (- n 3) (- n 3))))
   4)
== { Arith }
(+ (* n n) -1)
== { Arith }
(1- (expt n 2))
QED

QED



; After doing the above proofs, you decide to see if ACL2s can do this
; for you.
;
; Write Lemma r1-closed-form in ACL2s as a property and see if ACL2s
; can prove it automatically (use .lisp file for that).

(property (n :nat)
  (= (r1 n)
     (1- (expt 2 (1+ n)))))

; Write Lemma r2-closed-form in ACL2s as a property and see if ACL2s
; can prove it automatically (use .lisp file for that).

(property (n :pos)
          (= (r2 n)
             (1- (expt n 2))))

; This gives you an idea, which you pitch to the AI team. To test
; their system, they can use their AI solver to propose solutions to
; recurrences, which then get translated to ACL2s properties that can
; be checked using testing and/or theorem proving.
;
; They try it and find lots of bugs, ah the joys of AI.
;
; The one downside of your coop experience is you have to figure out
; whether to accept the return offer from the compiler team or the AI
; team. Which one will you choose? Tell us below. (Free points)

"XXX"

