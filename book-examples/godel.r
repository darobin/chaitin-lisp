LISP Interpreter Run

[[[[[

 A LISP expression that asserts that it itself is unprovable!

 Let g(x): x -> (is-unprovable (value-of (('x)('x))))

 Then (is-unprovable (value-of (('g)('g))))
 asserts that it itself is not a theorem!

]]]]]

define (g x) 
   let (L x y) cons x cons y nil [Makes x and y into list.]
   (L is-unprovable (L value-of (L (L "' x) (L "' x))))

define      g
value       (lambda (x) ((' (lambda (L) (L is-unprovable (L va
            lue-of (L (L ' x) (L ' x)))))) (' (lambda (x y) (c
            ons x (cons y nil))))))


[Here we try g:]

(g x)

expression  (g x)
value       (is-unprovable (value-of ((' x) (' x))))


[
 Here we calculate the LISP expression 
 that asserts its own unprovability: 
]

(g g)

expression  (g g)
value       (is-unprovable (value-of ((' (lambda (x) ((' (lamb
            da (L) (L is-unprovable (L value-of (L (L ' x) (L 
            ' x)))))) (' (lambda (x y) (cons x (cons y nil))))
            ))) (' (lambda (x) ((' (lambda (L) (L is-unprovabl
            e (L value-of (L (L ' x) (L ' x)))))) (' (lambda (
            x y) (cons x (cons y nil))))))))))


[Here we extract the part that it uses to name itself:]

cadr cadr (g g)

expression  (car (cdr (car (cdr (g g)))))
value       ((' (lambda (x) ((' (lambda (L) (L is-unprovable (
            L value-of (L (L ' x) (L ' x)))))) (' (lambda (x y
            ) (cons x (cons y nil))))))) (' (lambda (x) ((' (l
            ambda (L) (L is-unprovable (L value-of (L (L ' x) 
            (L ' x)))))) (' (lambda (x y) (cons x (cons y nil)
            )))))))


[Here we evaluate the name to get back the entire expression:] 

eval cadr cadr (g g)

expression  (eval (car (cdr (car (cdr (g g))))))
value       (is-unprovable (value-of ((' (lambda (x) ((' (lamb
            da (L) (L is-unprovable (L value-of (L (L ' x) (L 
            ' x)))))) (' (lambda (x y) (cons x (cons y nil))))
            ))) (' (lambda (x) ((' (lambda (L) (L is-unprovabl
            e (L value-of (L (L ' x) (L ' x)))))) (' (lambda (
            x y) (cons x (cons y nil))))))))))


[Here we check that it worked:]

= (g g) eval cadr cadr (g g)

expression  (= (g g) (eval (car (cdr (car (cdr (g g)))))))
value       true

End of LISP Run

Elapsed time is 0 seconds.
