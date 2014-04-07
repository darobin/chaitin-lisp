LISP Interpreter Run

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

define      turing
value       (lambda (x) ((' (lambda (halts?) ((' (lambda (y) (
            (' (lambda (z) (if (halts? z) (eval z) nil))) (dis
            play (cons y (cons y nil)))))) (cons ' (cons x nil
            ))))) (' (lambda (S-exp) false))))


[
 (turing turing) decides whether it itself has a value, 
 then does the opposite!

 Here we suppose it doesn't have a value, 
 so it turns out that it does:
]

(turing turing)

expression  (turing turing)
display     ((' (lambda (x) ((' (lambda (halts?) ((' (lambda (
            y) ((' (lambda (z) (if (halts? z) (eval z) nil))) 
            (display (cons y (cons y nil)))))) (cons ' (cons x
             nil))))) (' (lambda (S-exp) false))))) (' (lambda
             (x) ((' (lambda (halts?) ((' (lambda (y) ((' (lam
            bda (z) (if (halts? z) (eval z) nil))) (display (c
            ons y (cons y nil)))))) (cons ' (cons x nil))))) (
            ' (lambda (S-exp) false))))))
value       ()


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

define      turing
value       (lambda (x) ((' (lambda (halts?) ((' (lambda (y) (
            (' (lambda (z) (if (halts? z) (eval z) nil))) (con
            s y (cons y nil))))) (cons ' (cons x nil))))) (' (
            lambda (S-exp) true))))


[
 And here we suppose it does have a value, 
 so it turns out that it doesn't.

 It loops forever evaluating itself again and again!
]

(turing turing) 

expression  (turing turing)
Storage overflow!
