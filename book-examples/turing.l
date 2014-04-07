[[[[[

 Proof that the halting problem is unsolvable by using
 it to construct a LISP expression that halts iff it doesn't.

]]]]]

define (turing x) 
[Insert supposed halting algorithm here.]
let (halts? S-exp) false [<=============]
[Form ('x)]
let y [be] cons "' cons x nil [in]
[Form (('x)('x))]
let z [be] display cons y cons y nil [in]
[If (('x)('x)) has a value, then loop forever, otherwise halt]
if (halts? z) [then] eval z [loop forever]
              [else] nil [halt]

[
 (turing turing) decides whether it itself has a value, 
 then does the opposite!

 Here we suppose it doesn't have a value, 
 so it turns out that it does:
]

(turing turing)

define (turing x) 
[Insert supposed halting algorithm here.]
let (halts? S-exp) true [<==============]
[Form ('x)]
let y [be] cons "' cons x nil [in]
[Form (('x)('x))]
let z [be] [[[[display]]]] cons y cons y nil [in]
[If (('x)('x)) has a value, then loop forever, otherwise halt]
if (halts? z) [then] eval z [loop forever]
              [else] nil [halt]

[
 And here we suppose it does have a value, 
 so it turns out that it doesn't.

 It loops forever evaluating itself again and again!
]

(turing turing) 
