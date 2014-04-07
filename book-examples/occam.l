[[[[[
   Occam's razor---Concentration process.  
   From computer C construct C' such that 
   if P_C(x) >= 1/2^k, then 
   then C' has a k+1 bit program for x.
   Hence H(x) <= -log_2 P_C(x) + c
   where c depends only on C, not on x.
]]]]]

define all-together

[this is used to avoid duplicate requirements for C']
let previous-requirements nil

[test case special-purpose computer C:]
[ignores odd bits, multiplies by ten until hits a 1]
[this C has many programs that do the same job!]
[[to put U here instead, let C be 'eval read-exp]]
let C '
   let (loop n) 
      let ignore-it [be] read-bit [skip bit]
      if = 1 read-bit [then return] n
         [else] (loop * 10 n)
   (loop 10)

[stage n = 0, 1, 2, ... of overall concentration process]
[look at all n-bit programs for C, run them for time n]
[merge (output,multiplicity) pairs, emit requirements for C']
let (stage n)
   let previous-requirements 
      (make-requirements debug (how-many? nil debug n))
   (stage + n 1)

[produce (output,multiplicity) pairs] 
[by running all n-bit programs on C for time n]
let (how-many? p n)
   if = n length p

      [run program p for time n]
      let v try n [U => 'eval read-exp] C p
      if = success car v

          [program ran to completion]
          [indicate that it produces] 
          [its output with multiplicity one]
          cons cons cadr v cons 1 nil
               nil                   

          [otherwise program failed]
          nil 
          [empty list of (output,multiplicity) pairs]                   

      [otherwise use recursion to combine multiplicities]
      (merge (how-many? cons 0 p n)
             (how-many? cons 1 p n)
      )

[add one (output,multiplicity) pair to a list of such pairs]
let (merge1 pair list)
   if  atom list     cons pair nil
   let first-in-list car  list
   let rest-of-list  cdr  list
   let output        car  pair
   let multiplicity  cadr pair
   let output2       car  first-in-list
   let multiplicity2 cadr first-in-list
   if = output output2
      [= -> combine multiplicities]
      cons cons output cons + multiplicity multiplicity2 nil
           rest-of-list
      [!= -> don't combine multiplicities]
      cons first-in-list 
           (merge1 pair rest-of-list)

[combine two lists of (output,multiplicity) pairs]
let (merge list list2)
   if atom list list2
   (merge1 car list (merge cdr list list2))

[exponent in highest power of 2 <= n, n != 0]
let (log2 n)
   let (loop power exponent)
      let new-power    + power power [double it]
      let new-exponent + 1 exponent  [add 1 to it]
      if > new-power n [then return] exponent
         [else] (loop new-power new-exponent)
   (loop [initial power of two] 1 [initial exponent of 2] 0)

let (make-requirements list-of-pairs)
   if  atom list-of-pairs  previous-requirements
   let first-pair     car  list-of-pairs
   let list-of-pairs  cdr  list-of-pairs
   let output         car  first-pair
   let multiplicity   cadr first-pair
   let kraft-requirement 
       cons output cons - + n 1 (log2 multiplicity) nil
   let previous-requirements (make-requirements list-of-pairs)
   [keep only first appearance of requirement]
   if (is-in? kraft-requirement previous-requirements)
      previous-requirements
   cons debug display kraft-requirement previous-requirements 

let (is-in? x list) [is x in list?]
   if atom list     false
   if = x car list  true
   (is-in? x cdr list)

[HERE GOES!]
(stage 0)

try 60 all-together nil
