[[[
 RELATIVE COMPLEXITY!
 Additional steps in my new construction for
 a self-delimiting universal Turing machine.

 We show that

    H(beta) <= n + H(n) + c for n-bit beta 
                                 
    H(x,y) <= H(x) + H(y) + c
      
    H(H(x)|x) <= c
                      
    H(x,y) <= H(x) + H(y|x) + c
]]]
 
[
 Here is the self-delimiting universal Turing machine
 with NO free data.  P is the program.
 [Run-utm-on p expands to this.]
]
define (U p)
   cadr try no-time-limit 'eval read-exp p

define      U
value       (lambda (p) (car (cdr (try no-time-limit (' (eval 
            (read-exp))) p))))

[Here is the version of U with one piece of free data:]

define (U2 p q) [q is a program for U for the free data]
   cadr try no-time-limit 
   display cons 'read-exp [run ((read-exp) (' q))]
           cons cons "' 
                cons q 
                nil 
           nil 
   p

define      U2
value       (lambda (p q) (car (cdr (try no-time-limit (displa
            y (cons (' (read-exp)) (cons (cons ' (cons q nil))
             nil))) p))))

[Here's the version given two things, not one:]

define (U3 p q r) [q, r are programs for U for the free data]
   cadr try no-time-limit 
   display cons 'read-exp [run ((read-exp) (' q) (' r))]
           cons cons "' 
                cons q 
                nil 
           cons cons "' 
                cons r 
                nil 
           nil 
   p

define      U3
value       (lambda (p q r) (car (cdr (try no-time-limit (disp
            lay (cons (' (read-exp)) (cons (cons ' (cons q nil
            )) (cons (cons ' (cons r nil)) nil)))) p))))

[
   Consider an n-bit string beta.
   We show that H(beta) <= n + H(n) + 912.
]
define pi
   let (loop k)
      if = k 0 nil
      cons read-bit (loop - k 1)
   (loop eval read-exp)

define      pi
value       ((' (lambda (loop) (loop (eval (read-exp))))) (' (
            lambda (k) (if (= k 0) nil (cons (read-bit) (loop 
            (- k 1)))))))

[Size it.]
length bits pi

expression  (length (bits pi))
value       912

[Use it.]
(U
   append bits pi   
   append bits 12
          '(0 0 1 1 1 1 1 1 0 0 0 1)
)

expression  (U (append (bits pi) (append (bits 12) (' (0 0 1 1
             1 1 1 1 0 0 0 1)))))
value       (0 0 1 1 1 1 1 1 0 0 0 1)

[
   Proof that H(x,y) <= H(x) + H(y) + 432.
]
define rho
   cons eval read-exp cons eval read-exp nil

define      rho
value       (cons (eval (read-exp)) (cons (eval (read-exp)) ni
            l))

[Size it.]
length bits rho

expression  (length (bits rho))
value       432

[Use it.]
(U
   append bits rho
   append bits pi
   append bits 5
   append '(1 1 1 1 1)
   append bits pi
   append bits 9
          '(0 0 0 0 0 0 0 0 0)
)

expression  (U (append (bits rho) (append (bits pi) (append (b
            its 5) (append (' (1 1 1 1 1)) (append (bits pi) (
            append (bits 9) (' (0 0 0 0 0 0 0 0 0)))))))))
value       ((1 1 1 1 1) (0 0 0 0 0 0 0 0 0))

[
   Proof that H(H(x)|x) <= 208.
]
define (alpha x*)     [x* = minimum-size program for x]
   length x* 

define      alpha
value       (lambda (x*) (length x*))

         [get H(x) from x*]
[Size it.]
length bits alpha

expression  (length (bits alpha))
value       208

[Use it.]

(U2 
 
[This is the program to calculate H(x):]

bits alpha  

[This is the program x* for x,]
[supposedly smallest possible:]

bits' + 1 1   

)

expression  (U2 (bits alpha) (bits (' (+ 1 1))))
display     ((read-exp) (' (0 0 1 0 1 0 0 0 0 0 1 0 1 0 1 1 0 
            0 1 0 0 0 0 0 0 0 1 1 0 0 0 1 0 0 1 0 0 0 0 0 0 0 
            1 1 0 0 0 1 0 0 1 0 1 0 0 1 0 0 0 0 1 0 1 0)))
value       64

[Check size of program is correct]
* 8 + 1 display size display '+ 1 1

expression  (* 8 (+ 1 (display (size (display (' (+ 1 1)))))))
display     (+ 1 1)
display     7
value       64

[
   Proof that H(x,y) <= H(x) + H(y|x) + 2872.

   The 2872-bit prefix gamma proves this.

   Gamma does the job, but it's slow.
   So below we will present delta, which is a greatly
   sped up version of gamma.  The speed up is
   achieved by introducing a new primitive function
   to do the job.  The was-read mechanism used below
   is much faster than our technique here using try
   to get the bits of the program p = x* as we run it.
]

define gamma

   [read program p bit by bit until we get it all]

   let (loop p)
      if = success car try no-time-limit 'eval read-exp p
      [then] p 
      [else] (loop append p cons read-bit nil)

   let x* (loop nil)         [get x* = program for x]
   let x run-utm-on x*       [get x from x*]
   let y                     [get y from x* by running]
       eval cons 'read-exp   [((read-exp) (' x*))]
            cons cons "' 
                 cons x*
                      nil 
                 nil 

   [form the pair x, y]
   cons x cons y nil

define      gamma
value       ((' (lambda (loop) ((' (lambda (x*) ((' (lambda (x
            ) ((' (lambda (y) (cons x (cons y nil)))) (eval (c
            ons (' (read-exp)) (cons (cons ' (cons x* nil)) ni
            l)))))) (car (cdr (try no-time-limit (' (eval (rea
            d-exp))) x*)))))) (loop nil)))) (' (lambda (p) (if
             (= success (car (try no-time-limit (' (eval (read
            -exp))) p))) p (loop (append p (cons (read-bit) ni
            l)))))))

[Size it.]
length bits gamma

expression  (length (bits gamma))
value       2872

[Use it.]

run-utm-on

[get pair x, y by combining                   ]
[a program for x and a program to get y from x]

append 

   bits gamma

append

   [x* = program to calculate x = 2]
   [[Supposedly x* is smallest possible,]] 
   [[but this works for ANY x* for x.]]

   bits' + 1 1 

   [program to calculate y = x+1 from x*]

   bits' lambda(x*) + 1 run-utm-on x*

expression  (car (cdr (try no-time-limit (' (eval (read-exp)))
             (append (bits gamma) (append (bits (' (+ 1 1))) (
            bits (' (lambda (x*) (+ 1 (car (cdr (try no-time-l
            imit (' (eval (read-exp))) x*))))))))))))
value       (2 3)

[
   This technique for getting a program as well as its output
   by inching along using try is slow.

   Now let's speed up gamma by adding a new primitive function.
   Was-read gives the binary data read so far in the current try. 
   With it we will prove that H(x,y) <= H(x) + H(y|x) + 2104.
]
define delta                 [knows that its own size is 2104 bits]
   let (skip n s)            [skip first n bits of bit string s]
       if = n 0 s (skip - n 1 cdr s) [used to erase delta from was-read]
   let x eval read-exp               [get x]
   let x* (skip 2104 was-read)       [get program for x]
   let y                     [calculate y from the program for x by]
       eval cons 'read-exp   [running ((read-exp) (' x*))]
            cons cons "' 
                 cons x*
                 nil 
            nil 
   [form the pair x, y]
   cons x cons y nil 

define      delta
value       ((' (lambda (skip) ((' (lambda (x) ((' (lambda (x*
            ) ((' (lambda (y) (cons x (cons y nil)))) (eval (c
            ons (' (read-exp)) (cons (cons ' (cons x* nil)) ni
            l)))))) (skip 2104 (was-read))))) (eval (read-exp)
            )))) (' (lambda (n s) (if (= n 0) s (skip (- n 1) 
            (cdr s))))))

        
[Size it.]
length bits delta

expression  (length (bits delta))
value       2104

[Use it.]

run-utm-on

[get pair x, y by combining                   ]
[a program for x and a program to get y from x]

append 

   bits delta

append

   [x* = program to calculate x = 2]
   [[Supposedly x* is smallest possible,]] 
   [[but this works for ANY x* for x.]]

   bits' + 1 1

   [program to calculate y = x+1 from x*]

   bits' lambda(x*) + 1 run-utm-on x*

expression  (car (cdr (try no-time-limit (' (eval (read-exp)))
             (append (bits delta) (append (bits (' (+ 1 1))) (
            bits (' (lambda (x*) (+ 1 (car (cdr (try no-time-l
            imit (' (eval (read-exp))) x*))))))))))))
value       (2 3)
