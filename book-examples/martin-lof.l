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

define (is-in? x l) [is x in the list l?]
   if atom l    false
   if = x car l true
   (is-in? x cdr l)

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

[to remove duplicates]
define requirements ()

[run it]
(stage 0)
