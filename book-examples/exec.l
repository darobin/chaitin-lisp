[[[[[
   Given an expr to enumerate (program output) pairs,
   we simulate the Turing machine defined this way.
   We assume this r.e. set of programs is prefix free,
   i.e., no extension of a valid program is a valid
   program.  If so, we will carry out this simulation
   in a self-delimiting way, i.e., we won't read any
   unnecessary bits of the program.
]]]]]

define pi

[this is the prefix to put in front of the expr to
enumerate the infinite set of (program output) pairs]

    [graph is an unending expression for (p o) pairs]
    let graph read-exp 

    [program read so far; initialize to empty bit string]
    let p nil 

    let (look-for p [in] pairs)
       if atom pairs false
       [(add new macro caar -> car car to interpreter?)]
       if = p car car pairs [does first pair start with p?]
          car pairs   [if so, return first pair]
          [otherwise, keep looking]
          (look-for p [in] cdr pairs)

    let (look-for-extension-of p [in] pairs)
       if atom pairs false
       if (is-prefix? p car car pairs)
          true
          (look-for-extension-of p [in] cdr pairs)

    let (is-prefix? p q) [is p a prefix of q?]
       if atom p true
       if atom q false
       if = car p car q
          (is-prefix? cdr p cdr q)
          false

    let (loop t)
       [run for time t expr to generate (program output) pairs]
       [pairs are displayed by graph]
       let pairs debug caddr try debug t graph nil   
       let found-it? (look-for p pairs) [found pair with program p?]
       if found-it? cadr found-it? [if so, we have output for p!]
       [(if found-it? isn't false, then it's considered true)]
       [is an extension of p in there?]
       if (look-for-extension-of p [in] pairs) 
                  [if so, read another bit of p]
           [then] let p debug append p cons read-bit nil
                     (loop + t 1) [and generate more pairs]
                  [don't read more of p, just generate more pairs]
           [else] (loop + t 1) 

    [initialize time t to 0]
    (loop 0)

[graph = (1 0) (01 1) (001 2) (0001 3) (00001 4) etc.]
define graph 
    let (loop p n)
  [do!] cons display cons p cons n nil
             (loop  cons 0 p  + 1 n)
    (loop '(1) 0)

[test it!]

try 10 graph nil

run-utm-on

append

     bits pi

append

     bits graph

     '(0 0 0 1)
