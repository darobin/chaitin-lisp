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

[First part: not M-L random ===> not Ch random] 

[We create the following set of requirements] 
[(output, size-of-program)]
[ (s, |s|-n) : s in A_{n^2}, n >= 2 ] 

[Stage k>=0, look at all A_{n^2} n = 2 to 2+k for time k.]
[Then have to combine stage 0, stage 1,...]
[and eliminate duplicates]

[infinite computation that displays strings] 
[in cover A_m with measure mu <= 1/2^m]
define (A m) 
   cdr cons
   [test case, A_m = string of m 1's]
   display base10-to-2 - ^ 2 m 1 
   nil

define      A
value       (lambda (m) (cdr (cons (display (base10-to-2 (- (^
             2 m) 1))) nil)))

define (is-in? x l) [is x in the list l?]
   if atom l    false
   if = x car l true
   (is-in? x cdr l)

define      is-in?
value       (lambda (x l) (if (atom l) false (if (= x (car l))
             true (is-in? x (cdr l)))))

define (convert-to-requirements cover n) [display requirements]
   if  atom cover requirements [finished?]
   let s          car cover [get first string]
   let cover      cdr cover [get rest of strings]
   let requirement 
       cons s cons - length s n nil [form (s, |s|-n)]
   if (is-in? requirement requirements) [duplicate?]
   [yes] (convert-to-requirements cover n)
   [no]  let requirements cons display requirement requirements
         (convert-to-requirements cover n)

define      convert-to-requirements
value       (lambda (cover n) (if (atom cover) requirements ((
            ' (lambda (s) ((' (lambda (cover) ((' (lambda (req
            uirement) (if (is-in? requirement requirements) (c
            onvert-to-requirements cover n) ((' (lambda (requi
            rements) (convert-to-requirements cover n))) (cons
             (display requirement) requirements))))) (cons s (
            cons (- (length s) n) nil))))) (cdr cover)))) (car
             cover))))

define (stage k)
   if = k 4 stop! [[[stop infinite computation!!!]]]
   let (loop i) [i = 0 to k]
      if  > i k (stage + k 1) [go to next stage]
      let n + 2 i [n = 2 + i]
      let expr cons cons "' cons A nil
                    cons * n n nil
      let cover caddr try k expr nil  [caddr = displays]
      let requirements (convert-to-requirements cover n)
      (loop + i 1) [bump i]
   [initialize i]
   (loop 0)

define      stage
value       (lambda (k) (if (= k 4) stop! ((' (lambda (loop) (
            loop 0))) (' (lambda (i) (if (> i k) (stage (+ k 1
            )) ((' (lambda (n) ((' (lambda (expr) ((' (lambda 
            (cover) ((' (lambda (requirements) (loop (+ i 1)))
            ) (convert-to-requirements cover n)))) (car (cdr (
            cdr (try k expr nil))))))) (cons (cons ' (cons A n
            il)) (cons (* n n) nil))))) (+ 2 i))))))))

[to remove duplicates]
define requirements ()

define      requirements
value       ()

[run it]
(stage 0)

expression  (stage 0)
display     ((1 1 1 1) 2)
display     ((1 1 1 1 1 1 1 1 1) 6)
display     ((1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1) 12)
display     ((1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 
            1) 20)
value       stop!
