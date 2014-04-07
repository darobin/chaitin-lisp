[[[[[
   Show that a real r is Solovay random
   iff it is Martin-Lof random.

   An effective covering A_k of k is a function
   of k that enumerates bit strings s,
   which are the initial bits of the covered
   reals.  We assume that no s in A_k is a
   proper prefix or extension of another.
   Thus the measure of the cover A_k of k is
   exactly Sum_{s in A_k} of 2^{-|s|},
   where |s| is the length of the bit string s.
]]]]]

[First part: not M-L random ===> not Solovay random] 

[
This is immediate.  We are given coverings A_k such
that real r is in A_k for all k and the measure of A_k <= 2^{-k}.
It follows immediately that r is in infinitely many of the
A_k and the sum of the measure of A_k summed over all k converges.
Thus r is not Solovay random.
]

[Second part: not Solovay random ===> not M-L random] 

[
Suppose that a real r is in infinitely many of the 
coverings A_n and that Sum_k mu A_n <= 2^c.
Consider B_k defined as the set of all reals that are
in at least 2^{k+c} of the A_n.
Then r is in all of the B_k and the measure of 
B_k is <= 2^{-k}, so r is not Martin-Lof random.

Now let's program this!

Instead, I'll program B_k which is the set of all reals
that are in at least k of the A_n.
The proof then results from considering B_{2^{k+c}} .

The main function has two parameters, the stage n, and
the number of times something has to be repeated to
be taken into account.  At stage n, with number 
of repeats r, we look at A_0 through A_n for time n,
and put into our condensed result cover only subintervals
that are covered at least r times.

The key auxiliary function given n generates A_0 through A_n for time n,
then expands all intervals to the same max length and counts how
many times each is repeated.  Then it is easy to select those that
are covered the requisite number of times.

First step is to run A_0 through A_n for time n and append the results.
Then we get the max length and do a binary tree walk.  We start with
s and see if it's a prefix of at least r things.
If so, s will be in our result, and we backtrack.
If not, if s has max length, we stop recursion.
Otherwise, we look at s0 and at s1.
And we start with s = nil.
This gives our covering at stage n,
then we have to eliminate overlaps to
get our final result.
]

[ 
 Test case: A_n is defined to be the set of
 all natural numbers greater than n,
 where k is represented as k 1's followed by a 0.
 Then measure of A_n is 2^{-n-1}, and
 1=10 is in one of the A_n, 2=110 is in two of them,
 3=1110 is in three of them, etc.

 I.e., 1=10 is only in A_0,
       2=110 is only in A_0 & A_1,
       3=1110 is only in A_0 A_1 & A_2, etc.

 In this case the total measure of the A_n is 
 1/2 + 1/4 + 1/8 + ... = 1.
 For the proof in general, all we know is that
 this total measure converges to a finite sum, not 1.
]
define (A n) [displays infinite set 1^k 0, k > n] 
  let (loop k)
      cons display 
         append base10-to-2 - ^ 2 k 1 [2^k - 1 = k 1's]
            cons 0 nil [followed by a 0 bit]
      (loop + k 1)
  (loop + n 1)

define      A
value       (lambda (n) ((' (lambda (loop) (loop (+ n 1)))) ('
             (lambda (k) (cons (display (append (base10-to-2 (
            - (^ 2 k) 1)) (cons 0 nil))) (loop (+ k 1)))))))

 

[now put together in one list stage n of A_0 through A_n]
define (sum n)
   let (loop k sum)
      if > k n sum
      (loop + k 1 
            append caddr try n cons cons "' cons A nil cons k nil nil
                   sum)
   (loop 0 nil)

define      sum
value       (lambda (n) ((' (lambda (loop) (loop 0 nil))) (' (
            lambda (k sum) (if (> k n) sum (loop (+ k 1) (appe
            nd (car (cdr (cdr (try n (cons (cons ' (cons A nil
            )) (cons k nil)) nil)))) sum)))))))

[
 (count x y) 
 Now count how many times something x is contained in / 
 is an extension of an element of y
]
define (count x y) 
   if atom y 0
   if (is-prefix-of? car y x) + 1 (count x cdr y)
   (count x cdr y)

define      count
value       (lambda (x y) (if (atom y) 0 (if (is-prefix-of? (c
            ar y) x) (+ 1 (count x (cdr y))) (count x (cdr y))
            )))

define (is-prefix-of? x y) [is bit string x a prefix of bit string y?]
   if atom x  true
   if atom y  false
   if = car x car y (is-prefix-of? cdr x cdr y)
   false

define      is-prefix-of?
value       (lambda (x y) (if (atom x) true (if (atom y) false
             (if (= (car x) (car y)) (is-prefix-of? (cdr x) (c
            dr y)) false))))

[get maximum length of a list of bit strings]
define (max-length list) 
   if atom list   0
   let len1 length car list
   let len2 (max-length cdr list)
   if > len1 len2   
      [then] len1 
      [else] len2 

define      max-length
value       (lambda (list) (if (atom list) 0 ((' (lambda (len1
            ) ((' (lambda (len2) (if (> len1 len2) len1 len2))
            ) (max-length (cdr list))))) (length (car list))))
            )

[
 Now we get what (sum n) covers with multiplicity >= k.
 The measure of the multiplicity k covering will
 be bounded by the finite total measure (here 1) divided by k.
]

define (exceeds-count n k)
   let sum-n (sum n)
   let max-length-sum-n (max-length sum-n)
   (look-at nil)

define      exceeds-count
value       (lambda (n k) ((' (lambda (sum-n) ((' (lambda (max
            -length-sum-n) (look-at nil))) (max-length sum-n))
            )) (sum n)))

[
 This routine has free parameters sum-n, max-length-sum-n, k.
 It gets us the MINIMAL multiplicity >= k covering for (sum n)!
]
define (look-at x) [produces strings x covered with multiplicity >= k in (sum n)]
   if = length x max-length-sum-n
      let n (count x sum-n)
      if >= n k cons x nil [found an interval x that is covered >= k times]
                nil  [didn't find an interval x that is covered >= k times]
   [otherwise break x into subintervals]
   let x0 append x cons 0 nil
   let x1 append x cons 1 nil
   let v  append (look-at x0)
                 (look-at x1)
   [consolidate subintervals?]
   if = v cons x0 cons x1 nil [yes!] cons x nil
          [no, leave covering as is] v

define      look-at
value       (lambda (x) (if (= (length x) max-length-sum-n) ((
            ' (lambda (n) (if (>= n k) (cons x nil) nil))) (co
            unt x sum-n)) ((' (lambda (x0) ((' (lambda (x1) ((
            ' (lambda (v) (if (= v (cons x0 (cons x1 nil))) (c
            ons x nil) v))) (append (look-at x0) (look-at x1))
            ))) (append x (cons 1 nil))))) (append x (cons 0 n
            il)))))

[
 Now we put this all together into B_k, which is
 the limit as n goes to infinity of (exceeds-count n k),
 k fixed, n --> infinity.

 I.e., B_k is what A_0, A_1, A_2, ... covers with
 multiplicity >= k.

 Thus the measure of B_k will be bounded by the
 total measure of the A_n (if it exists) divided by k.

 The main problem is to avoid overlaps in B_k,
 which we do using a completely general algorithm.
]

[list of intervals in covering so far]
[used to avoid overlapping intervals in covering]
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
   if (new-interval-covered-by-previous-one? interval intervals) 
      [then don't need to repeat it]
      nil
   let holes (new-interval-covers-previous-ones interval intervals)
   if atom holes
      [then interval is fine as is]
      [output it with display!]
      cons display interval nil 
   [get max granularity needed]
   let max (max-length holes) 
   [convert everything to same granularity]
   let holes (extend-all holes max)
   [and remove overlap]
   [subtract will output residue with display]
   (subtract (extend interval max) holes)

define      process
value       (lambda (interval) (if (new-interval-covered-by-pr
            evious-one? interval intervals) nil ((' (lambda (h
            oles) (if (atom holes) (cons (display interval) ni
            l) ((' (lambda (max) ((' (lambda (holes) (subtract
             (extend interval max) holes))) (extend-all holes 
            max)))) (max-length holes))))) (new-interval-cover
            s-previous-ones interval intervals))))

[returns true/false]
define (new-interval-covered-by-previous-one? interval intervals)
   if atom intervals  false
   if (is-prefix-of? car intervals interval)  true
   (new-interval-covered-by-previous-one? interval cdr intervals)

define      new-interval-covered-by-previous-one?
value       (lambda (interval intervals) (if (atom intervals) 
            false (if (is-prefix-of? (car intervals) interval)
             true (new-interval-covered-by-previous-one? inter
            val (cdr intervals)))))

[returns set of previous intervals covered by this one]
define (new-interval-covers-previous-ones interval intervals)
   if atom intervals  nil
   if (is-prefix-of? interval car intervals)
      [then] cons car intervals (new-interval-covers-previous-ones interval cdr intervals)
      [else]                    (new-interval-covers-previous-ones interval cdr intervals)

define      new-interval-covers-previous-ones
value       (lambda (interval intervals) (if (atom intervals) 
            nil (if (is-prefix-of? interval (car intervals)) (
            cons (car intervals) (new-interval-covers-previous
            -ones interval (cdr intervals))) (new-interval-cov
            ers-previous-ones interval (cdr intervals)))))

   
[produce set of all extensions of a given bit string to a given length]
[(assumed >= to its current length)]
define (extend bit-string len)
   if = len length bit-string   
      [has correct length; return singleton set]
      cons bit-string nil
   append (extend append bit-string cons 0 nil len)
          (extend append bit-string cons 1 nil len)

define      extend
value       (lambda (bit-string len) (if (= len (length bit-st
            ring)) (cons bit-string nil) (append (extend (appe
            nd bit-string (cons 0 nil)) len) (extend (append b
            it-string (cons 1 nil)) len))))

[extend all the bit strings in a given list to the same length]
define (extend-all list len)
   if atom list   nil
   append (extend     car list len)
          (extend-all cdr list len)

define      extend-all
value       (lambda (list len) (if (atom list) nil (append (ex
            tend (car list) len) (extend-all (cdr list) len)))
            )

[subtract set of intervals y from set of intervals x]
[output residue with display!]
define (subtract x y)
   if atom x   nil    
   if (is-in? car x y)
   [then]                    (subtract cdr x y)
   [else] cons display car x (subtract cdr x y)

define      subtract
value       (lambda (x y) (if (atom x) nil (if (is-in? (car x)
             y) (subtract (cdr x) y) (cons (display (car x)) (
            subtract (cdr x) y)))))

define (is-in? x l) [is x an element of list l?]
   if atom l     false
   if = x car l  true
   (is-in? x cdr l)

define      is-in?
value       (lambda (x l) (if (atom l) false (if (= x (car l))
             true (is-in? x (cdr l)))))

[
 Put it all together---Here is cover B_k,
 which is what is covered by A_0, A_1, A_2, ...
 with multiplicity >= k, and therefore has
 measure bounded by the total measure of the A_n
 divided by k.
 Supposing that this total measure is <= 2^c
 and considering B_{2^{k+c}}, 
 we see that if a real r is in infinitely many of
 the A_n, then it will be in all of the 
 B_{2^{k+c}}, each of which has measure <= 1/2^k.
 Hence if a real r is not Solovay random,
 it follows that it will not be M-L random.
 Here we write the code for B_k, not for
 B_{2^{k+c}}.
]
define (B k)
   let intervals nil
   let (stage n)
      if = n 6 stop! [to stop test run---remove if real thing]
      let exceed-count (exceeds-count n k)
      let intervals (process-all exceed-count) 
      (stage + 1 n)
   [go!!!!!]
   (stage 0)

define      B
value       (lambda (k) ((' (lambda (intervals) ((' (lambda (s
            tage) (stage 0))) (' (lambda (n) (if (= n 6) stop!
             ((' (lambda (exceed-count) ((' (lambda (intervals
            ) (stage (+ 1 n)))) (process-all exceed-count)))) 
            (exceeds-count n k)))))))) nil))

[k = multiplicity = repeated/covered 2 or more times in the A_n]
(B 2)

expression  (B 2)
display     (1 1 0)
display     (1 1 1 0)
display     (1 1 1 1 0)
display     (1 1 1 1 1 0)
display     (1 1 1 1 1 1 0)
display     (1 1 1 1 1 1 1 0)
value       stop!
