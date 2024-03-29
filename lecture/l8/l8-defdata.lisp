WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
;$ACL2s-SMode$;ACL2s
#|

#+AUTHOR: Pete Manolios
#+TITLE: CS2800, Fall 2023, Lecture 8 code
#+EMAIL: pete@ccs.neu.edu
#+DATE: Sep 21, 2023

We introduce the ACL2s data definition framework via a sequence
of examples.

Singleton types allow us to define types that contain only one
object. For example:
|#

(defdata one 1)

#|
All data definitions give rise to a recognizer.  The above data
definition gives rise to the recognizer onep.
|#

(onep 1)
(onep '1)
(onep 2)
(onep 'hello)
(onep "1")

#|
Enumerated types allow you to define finite types.
|#

(defdata name (enum '(bob ken david)))

(property (x :name)
  (or (== x 'bob)
      (== x 'ken)
      (== x 'david)))#|ACL2s-ToDo-Line|#

#|
Range types allow you to define a range of numbers.  The two
examples below show how to define the rational interval [0..1]
and the integers greater than 2^{64}.
|#

(defdata probability (range rational (0 <= _ <= 1))) 
(defdata big-nat (range integer ((expt 2 256) < _)))

(property (x y :probability)
  (probabilityp (+ x y)))

(property (x y :probability)
  (probabilityp (- x y)))

(property (x y :probability)
  (probabilityp (* x y)))

(property (x y :big-nat)
  (big-natp (+ x y)))

(property (x y :big-nat)
  (big-natp (- x y)))

(property (x y :big-nat)
  (big-natp (* x y)))

#|
Notice that we need to provide a domain, which is either integer
or rational, and the set of numbers is specified with
inequalities using < and <=.  One of the lower or upper bounds
can be omitted, in which case the corresponding value is taken to
be negative or positive infinity.

Product types allow us to define structured data. The example
below defines a type consisting of list with exactly two strings.
|#

(defdata fullname (list string string))

#|
Records are  product types, where the fields are named. For
example, we could have defined fullname as follows.
|#


(defdata fullname-rec (record (first . string)
                              (last . string)))

#|
In addition to the recognizer fullname-recp, the above type
definition gives rise to the constructor fullname-rec which
takes two strings as arguments and constructs a record of
type fullname-rec. The type definition also generates the
accessors fullname-rec-first and fullname-rec-last
that when applied to an object of type fullname-rec return
the first and last fields, respectively.
|#

(fullname-rec-first (fullname-rec "Wade" "Wilson"))
(fullname-rec-last (fullname-rec "Wade" "Wilson"))

#|
We can create list types using the listof combinator as
follows.
|#


(defdata loi (listof integer))

#|
This defines the type consisting of lists of integers.

Union types allow us to take the union of existing types.
Here is an example.
|#

(defdata intstr (or integer string))

#|
Recursive type expressions involve the or
combinator and product combinations, where additionally there is
a (recursive) reference to the type being defined.
For example, here is another way of defining a list of integers.
|#

(defdata loint (or nil (cons integer loint)))

#|
Notice that this is how we've been describing recursive types so
far!

We now discuss what templates user-defined datatypes that are
recursive give rise to. Many of the datatypes we define are just
lists of existing types. For example, we can define a list of
rationals as follows.
|#

(defdata lor (listof rational))

#|
If we define a function that recurs on one of its arguments,
which is a list of rationals, we just use the list template and
can assume that if the list is non-empty then the first element
is a rational and the rest of the list is a list of rationals.

If we have a more complex data definition, say:
|#

(defdata UnaryOp '~)
(defdata BinOp (enum '(& + => ==)))
(defdata
  (PropEx (oneof boolean 
                 var
                 UPropEx
                 BPropEx))
  (UPropEx (list UnaryOp PropEx))
  (BPropEx (list Binop PropEx PropEx)))

#|
Then the template we wind up with is exactly what you would
expect from the data definition.

(definec foo (px :PropEx  ...) ...
  (match px
    (:bool ...)
    (:var ...)
    (:UPropEx ... (foo (second px) ...))
    (:BPropEx
     (('& p q) ... (foo p) ... (foo q) ...)
     (('+ p q) ...)
     (('=> p q) ...)
     (('== p q) ...))))

Notice that the cases are all exhaustive.

For the recursive cases, we get to assume that foo works correctly on
the destructed argument (second px), p and q.

Let's look at one more example. Consider a filesystem.

A file is a pair consisting of a string (name) and a natural
number (inode).
|#

(defdata file (list string nat))

#|
A directory is a pair consisting of a string (the directory name)
and a list whose elements are either files or directories
(subdirectories). This is a mutually-recursive type definition.
|#

(defdata 
  (dir (list string dir-file-list))
  (dir-file-list (listof file-dir))
  (file-dir (oneof file dir)))

#|
For example, here is a directory that contains you cs2800 hwks
|#

(defconst *cs2800-dir*
  '("cs2800" (("hw2.lisp" 92) ("hw3.lisp" 94))))

#|
It might be a subdirectory of a classes directory

|#
(dirp `("classes" (,*cs2800-dir* ("cs2500" (("hw2.lisp" 92))))))

#|
Notice the backquote, comma duo.

The data definition framework has more advanced features, e.g.,
it supports recursive record types, map types, custom types, and
so on. We will introduce such features as needed.
|#

#|

We could have also defined dir as follows

(defdata 
  (dir (list string dir-file-list))
  (dir-file-list (listof (oneof file dir))))

but it is a good idea to give all reasonable types names since we now
don't have the type file-dir, which may be useful.

So, as a general rule, we will provide names for subtypes, ie, we
prefer the first solution.

|#

#|

For documentation, you can use :doc.

|#

:doc definec
:doc defdata

