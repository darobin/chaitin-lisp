LISP Interpreter Run

[[[[[

 A LISP expression that evaluates to itself!

 Let f(x): x -> (('x)('x))

 Then (('f)('f)) is a fixed point.

]]]]]

[Here is the fixed point done by hand:]

(
'lambda(x) cons cons "' cons x nil
           cons cons "' cons x nil
                nil

'lambda(x) cons cons "' cons x nil
           cons cons "' cons x nil
                nil
)

expression  ((' (lambda (x) (cons (cons ' (cons x nil)) (cons 
            (cons ' (cons x nil)) nil)))) (' (lambda (x) (cons
             (cons ' (cons x nil)) (cons (cons ' (cons x nil))
             nil)))))
value       ((' (lambda (x) (cons (cons ' (cons x nil)) (cons 
            (cons ' (cons x nil)) nil)))) (' (lambda (x) (cons
             (cons ' (cons x nil)) (cons (cons ' (cons x nil))
             nil)))))


[Now let's construct the fixed point.]

define (f x) let y [be] cons "' cons x nil [y is ('x)        ]
             [return] cons y cons y nil    [return (('x)('x))]

define      f
value       (lambda (x) ((' (lambda (y) (cons y (cons y nil)))
            ) (cons ' (cons x nil))))


[Here we try f:]

(f x)

expression  (f x)
value       ((' x) (' x))


[Here we use f to calculate the fixed point:]

(f f)

expression  (f f)
value       ((' (lambda (x) ((' (lambda (y) (cons y (cons y ni
            l)))) (cons ' (cons x nil))))) (' (lambda (x) ((' 
            (lambda (y) (cons y (cons y nil)))) (cons ' (cons 
            x nil))))))


[Here we find the value of the fixed point:]

eval (f f)

expression  (eval (f f))
value       ((' (lambda (x) ((' (lambda (y) (cons y (cons y ni
            l)))) (cons ' (cons x nil))))) (' (lambda (x) ((' 
            (lambda (y) (cons y (cons y nil)))) (cons ' (cons 
            x nil))))))


[Here we check that it's a fixed point:]

= (f f) eval (f f)

expression  (= (f f) (eval (f f)))
value       true


[Just for emphasis:]

= (f f) eval eval eval eval eval eval (f f)

expression  (= (f f) (eval (eval (eval (eval (eval (eval (f f)
            )))))))
value       true

End of LISP Run

Elapsed time is 0 seconds.
