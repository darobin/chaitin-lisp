[[[[[
   Show that a real r is Solovay random
   iff it is strong Chaitin random.

   An effective covering A_k of k is a function
   of k that enumerates bit strings s,
   which are the initial bits of the covered
   reals.  We assume that no s in A_k is a
   proper prefix or extension of another.
   Thus the measure of the cover A_k of k is
   exactly Sum_{s in A_k} of 2^{-|s|},
   where |s| is the length of the bit string s.
]]]]]

[Second part: not Ch random ===> not Sol random] 

define (is-in? x l) [is x an element of list l?]
   if atom l     false
   if = x car l  true
   (is-in? x cdr l)

define      is-in?
value       (lambda (x l) (if (atom l) false (if (= x (car l))
             true (is-in? x (cdr l)))))

define (union x y) [set-theoretic union of two sets x y]
   if atom x y
   if (is-in? car x y) (union cdr x y)
   cons car x (union cdr x y)

define      union
value       (lambda (x y) (if (atom x) y (if (is-in? (car x) y
            ) (union (cdr x) y) (cons (car x) (union (cdr x) y
            )))))

define (is-bit-string? x) [is x a list of 0's and 1's?]
   if = x nil   true
   if atom x    false
   if = 0 car x (is-bit-string? cdr x)
   if = 1 car x (is-bit-string? cdr x)
   false

define      is-bit-string?
value       (lambda (x) (if (= x nil) true (if (atom x) false 
            (if (= 0 (car x)) (is-bit-string? (cdr x)) (if (= 
            1 (car x)) (is-bit-string? (cdr x)) false)))))

define C [test computer---real thing is eval read-exp]
   let (loop x y) [xx yy zz 01 ===> xyz]
     if = x y cons x (loop read-bit read-bit)
     nil
   (loop read-bit read-bit)

define      C
value       ((' (lambda (loop) (loop (read-bit) (read-bit)))) 
            (' (lambda (x y) (if (= x y) (cons x (loop (read-b
            it) (read-bit))) nil))))

[
 The hypothesis that
 the real number r is not Chaitin random
 means that there is a K such that
 for infinitely many values of n
   H(r_n) < n + K, 
 where r_n is the first n bits of r.

 For this example, let's suppose that K = 5.
]

define K 5

define      K
value       5

[
 Our proof depends on the fact that there is a c such that
 the probability that an n-bit string s has
  H(s) < n + K 
 is less than 2^{-H(n) + K + c}.
]

[
 Now let's do stage N of A_n = n-bit strings s with H(s) < |s| + K. 
 At stage N we look at all programs p less than n + K bits in size for time up to N.
]

define (quasi-compressible N n)
   (look-at nil)

define      quasi-compressible
value       (lambda (N n) (look-at nil))

[this routine has free parameters N, n, K, C]

define (look-at p) [produces quasi-compressible strings of length n]
   if = length p + n K [p too long?]
      nil
   let v try N C ['eval read-exp] p
   if = success car v
      let w cadr v   
      if (is-bit-string? w)
         if = n length w
            cons w nil
         nil
      nil
   [
    Also works with append below instead of union
    because duplicates are removed later by (process interval).
   ]
   (union (look-at append p cons 0 nil)
          (look-at append p cons 1 nil))

define      look-at
value       (lambda (p) (if (= (length p) (+ n K)) nil ((' (la
            mbda (v) (if (= success (car v)) ((' (lambda (w) (
            if (is-bit-string? w) (if (= n (length w)) (cons w
             nil) nil) nil))) (car (cdr v))) (union (look-at (
            append p (cons 0 nil))) (look-at (append p (cons 1
             nil))))))) (try N C p))))

[
 List of intervals in covering so far.
 used to avoid overlapping intervals in covering.

 This is easy to do because here because
 all intervals are the same length.
]
define intervals ()

define      intervals
value       ()

define (process-all x) [process list of intervals x]
   if atom x  intervals
   let intervals append (process car x) intervals
   (process-all cdr x)

define      process-all
value       (lambda (x) (if (atom x) intervals ((' (lambda (in
            tervals) (process-all (cdr x)))) (append (process 
            (car x)) intervals))))

define (process interval) [process individual interval]
   if (is-in? interval intervals) 
      [then don't need to repeat it]
      nil
      [else interval is fine as is]
      cons display interval nil 

define      process
value       (lambda (interval) (if (is-in? interval intervals)
             nil (cons (display interval) nil)))

[
 Put it all together---Here is cover A_n
 covering all reals r having n-bit prefix r_n 
 with H(r_n) < n + K.

 And we have measure \mu A_n <= 2^{-H(n)+K+c}
 so that Sum_n \mu A_n <= \Omega 2^{K+c} <= 2^{K+c} < infinity .

 Hence a real r which is not strongly Chaitin random
 will be in infinitely many of the A_n, 
 which have convergent total measure,
 and hence will not be Solovay random.
]
define (A n)
   let intervals nil
   let (stage N)
      if = N 7 stop! [to stop test run---remove if real thing]
      let quasi-compressible-strings (quasi-compressible N n)
      let intervals (process-all quasi-compressible-strings) 
      (stage + 1 N)
   [go!!!!!]
   (stage 0)

define      A
value       (lambda (n) ((' (lambda (intervals) ((' (lambda (s
            tage) (stage 0))) (' (lambda (N) (if (= N 7) stop!
             ((' (lambda (quasi-compressible-strings) ((' (lam
            bda (intervals) (stage (+ 1 N)))) (process-all qua
            si-compressible-strings)))) (quasi-compressible N 
            n)))))))) nil))

[n = 2, i.e., quasi-compressible 2-bit strings]
(A 2)

expression  (A 2)
display     (0 0)
display     (0 1)
display     (1 0)
display     (1 1)
value       stop!
