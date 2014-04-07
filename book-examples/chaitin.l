[[[[[

 Show that a formal axiomatic system (fas) can only prove 
 that finitely many LISP expressions are elegant.  
 (An expression is elegant if no smaller expression has 
 the same value.)

 More precisely, show that a fas of LISP complexity N can't 
 prove that a LISP expression X is elegant if X's size is 
 greater than N + 356.

 (fas N) returns the theorem proved by the Nth proof 
 (Nth S-expression) in the fas, or nil if the proof is 
 invalid, or stop to stop everything.

]]]]]

[
 This expression searches for an elegant expression 
 that is larger than it is and returns the value of 
 that expression as its own value.
]

define expression  [Formal Axiomatic System #1]
       let (fas n) if = n 1 '(is-elegant x)
                   if = n 2  nil
                   if = n 3 '(is-elegant yyy)
                   [else]    stop 

       let (loop n)
           let theorem [be] display (fas n)
           if = nil theorem [then] (loop + n 1)
           if = stop theorem [then] fas-has-stopped
           if = is-elegant car theorem
              if > display size cadr theorem 
                   display + 356 size fas
                 [return] eval cadr theorem
              [else] (loop + n 1)
           [else] (loop + n 1)

       (loop 1)

[Show that this expression knows its own size.]

size expression
  
[
 Run #1.

 Here it doesn't find an elegant expression 
 larger than it is:
]

eval expression

define expression  [Formal Axiomatic System #2]
       let (fas n) if = n 1 '(is-elegant x)
                   if = n 2  nil
                   if = n 3 '(is-elegant yyy)
                   if = n 4  cons is-elegant 
                             cons ^ 10 509     [<=====]
                                  nil
                   [else]    stop 

       let (loop n)
           let theorem [be] display (fas n)
           if = nil theorem [then] (loop + n 1)
           if = stop theorem [then] fas-has-stopped
           if = is-elegant car theorem
              if > display size cadr theorem 
                   display + 356 size fas
                 [return] eval cadr theorem
              [else] (loop + n 1)
           [else] (loop + n 1)

       (loop 1)

[Show that this expression knows its own size.]

size expression

[
 Run #2.

 Here it finds an elegant expression 
 exactly one character larger than it is: 
]

eval expression

define expression  [Formal Axiomatic System #3]
       let (fas n) if = n 1 '(is-elegant x)
                   if = n 2  nil
                   if = n 3 '(is-elegant yyy)
                   if = n 4  cons is-elegant  
                             cons ^ 10 508     [<=====]
                                  nil
                   [else]    stop 

       let (loop n)
           let theorem [be] display (fas n)
           if = nil theorem [then] (loop + n 1)
           if = stop theorem [then] fas-has-stopped
           if = is-elegant car theorem
              if > display size cadr theorem  
                   display + 356 size fas
                 [return] eval cadr theorem
              [else] (loop + n 1)
           [else] (loop + n 1)

       (loop 1)

[Show that this expression knows its own size.]

size expression

[
 Run #3.

 Here it finds an elegant expression 
 exactly the same size as it is: 
]

eval expression

define expression  [Formal Axiomatic System #4]
       let (fas n) if = n 1 '(is-elegant x)
                   if = n 2  nil
                   if = n 3 '(is-elegant yyy)
                   if = n 4  cons is-elegant 
                             cons cons "- 
                                  cons ^ 10 600  [<=====]
                                  cons 1 
                                       nil 
                                  nil
                   [else]    stop 

       let (loop n)
           let theorem [be] display (fas n)
           if = nil theorem [then] (loop + n 1)
           if = stop theorem [then] fas-has-stopped
           if = is-elegant car theorem
              if > display size cadr theorem 
                   display + 356 size fas
                 [return] eval cadr theorem
              [else] (loop + n 1)
           [else] (loop + n 1)

       (loop 1)

[Show that this expression knows its own size.]

size expression

[
 Run #4.

 Here it finds an elegant expression 
 much larger than it is, and evaluates it: 
]

eval expression
