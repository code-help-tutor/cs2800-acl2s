WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
(definec-no-test fib (n :nat) :nat
  (if (< n 2)
      n
    (+ (fib (- n 1))
       (fib (- n 2)))))

(time$ (fib 40)) ; ~1 secs = (fib 2) secs
(time$ (fib 41)) ; ~2 secs = (fib 3) secs
(time$ (fib 42)) ; ~3 secs = (fib 4) secs
(time$ (fib 43)) ; ~5 secs = (fib 5) secs
(time$ (fib 44)) ; ~8 secs = (fib 6) secs
















































"
What if I tried this?

(time$ (fib 200))?"



























































"
(time$ (fib 200)) ; ~ (fib 162) secs
                  ; = 3210056809456107725247980776292056 secs
                  ; > 10^26 years
                  ; > 10^15 times the age of the universe
"























































"
How do I even know that, since 

(time$ (fib 162)) ; ~ (fib 124) secs
                  ; ~ 36726740705505779255899443 secs
                  ; > 10^18 years
                  ; > 10^7 times the age of the universe
"
















































"
Challenge problem:
Write code in your favority language so that you can compute
(fib 162) fast.

The simplest solution gets lots of extra credit.
This competition is open to everyone in the room.


"


















































(memoize 'fib)   

(time$ (fib 200))

"
Much better than big-bang computations!
"

"
Compute (fib 10000) in your favorite language
"

(time$ (fib 10000))
