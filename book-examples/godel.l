[[[[[

 A LISP expression that asserts that it itself is unprovable!

 Let g(x): x -> (is-unprovable (value-of (('x)('x))))

 Then (is-unprovable (value-of (('g)('g))))
 asserts that it itself is not a theorem!

]]]]]

define (g x) 
   let (L x y) cons x cons y nil [Makes x and y into list.]
   (L is-unprovable (L value-of (L (L "' x) (L "' x))))

[Here we try g:]

(g x)

[
 Here we calculate the LISP expression 
 that asserts its own unprovability: 
]

(g g)

[Here we extract the part that it uses to name itself:]

cadr cadr (g g)

[Here we evaluate the name to get back the entire expression:] 

eval cadr cadr (g g)

[Here we check that it worked:]

= (g g) eval cadr cadr (g g)
