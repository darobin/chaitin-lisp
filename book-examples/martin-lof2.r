[[[[[
   Show that a real r is Martin-Lof random
   iff it is Chaitin random.

   An effective covering A_k of k is a function
   of k that enumerates bit strings s,
   which are the initial bits of the covered
   reals.  We assume that no s in A_k is a
   proper prefix or extension of another.
   Thus the measure of the cover A_k of k is
   exactly Sum_{s in A_k} of 2^{-|s|},
   where |s| is the length of the bit string s.
]]]]]

[Second part: not Ch random ===> not M-L random] 

define (is-in? x l) [is x an element of list l?]
   if atom l     false
   if = x car l  true
   (is-in? x cdr l)

define      is-in?
value       (lambda (x l) (if (atom l) false (if (= x (car l))
             true (is-in? x (cdr l)))))

define (is-prefix-of? x y) [is bit string x a prefix of bit string y?]
   if atom x  true
   if atom y  false
   if = car x car y (is-prefix-of? cdr x cdr y)
   false

define      is-prefix-of?
value       (lambda (x y) (if (atom x) true (if (atom y) false
             (if (= (car x) (car y)) (is-prefix-of? (cdr x) (c
            dr y)) false))))

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
   let (loop) [doubles all bits up to & including first 1]
     if = 1 read-bit '(1 1)
     cons 0 cons 0 (loop)
   (loop)

define      C
value       ((' (lambda (loop) (loop))) (' (lambda () (if (= 1
             (read-bit)) (' (1 1)) (cons 0 (cons 0 (loop))))))
            )

[Now let's do stage n of A_k = strings s with H(s) <= |s| - k.] 
[At stage n we look at programs p up to n bits in size for time up to n.]

define (compressible-by-k n k)
   (look-at nil)

define      compressible-by-k
value       (lambda (n k) (look-at nil))

[this routine has free parameters n, k, C]

define (look-at p) [produces strings compressible by k within time n]
   let v try n C ['eval read-exp] p
   if = success car v
      let w cadr v   
      if (is-bit-string? w)
         if >= length w + k length p
            cons w nil
         nil
      nil
   [otherwise failure]
   if = n length p nil [stop!]
   append (look-at append p cons 0 nil)
          (look-at append p cons 1 nil)

define      look-at
value       (lambda (p) ((' (lambda (v) (if (= success (car v)
            ) ((' (lambda (w) (if (is-bit-string? w) (if (>= (
            length w) (+ k (length p))) (cons w nil) nil) nil)
            )) (car (cdr v))) (if (= n (length p)) nil (append
             (look-at (append p (cons 0 nil))) (look-at (appen
            d p (cons 1 nil)))))))) (try n C p)))

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
      cons display interval nil 
   [get max granularity needed]
   let max (max-length holes) 
   [convert everything to same granularity]
   let holes (extend-all holes max)
   [and remove overlap]
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
define (subtract x y)
   if atom x   nil    
   if (is-in? car x y)
   [then]                          (subtract cdr x y)
   [else] cons debug display car x (subtract cdr x y)

define      subtract
value       (lambda (x y) (if (atom x) nil (if (is-in? (car x)
             y) (subtract (cdr x) y) (cons (debug (display (ca
            r x))) (subtract (cdr x) y)))))

[
 Put it all together---Here is cover A_k
 covering all reals r having any n-bit prefix r_n 
 with H(r_n) <= n - k.
 And we have measure \mu A_k <= 2^{-k+c}.
 Actual proof uses A_{k+c}
 so that measure \mu A_{k+c} <= 2^{-k}.
 Hence a real r with prefixes whose complexity
 dips arbitrarily far below their length will be
 in all the A_k and hence will not be M-L random.
]
define (A k)
   let intervals nil
   let (stage n)
      let compressible-strings (compressible-by-k n k)
      let intervals (process-all compressible-strings) 
      if = n 12 stop! [to stop test run---remove if real thing]
      (stage + 1 n)
   [go!!!!!]
   (stage 0)

define      A
value       (lambda (k) ((' (lambda (intervals) ((' (lambda (s
            tage) (stage 0))) (' (lambda (n) ((' (lambda (comp
            ressible-strings) ((' (lambda (intervals) (if (= n
             12) stop! (stage (+ 1 n))))) (process-all compres
            sible-strings)))) (compressible-by-k n k))))))) ni
            l))

[k = compression amount = 8 bits]
(A 8)

expression  (A 8)
display     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1)
display     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1)
display     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1)
display     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1)
value       stop!
