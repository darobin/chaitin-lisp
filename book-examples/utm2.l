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
[Here is the version of U with one piece of free data:]

define (U2 p q) [q is a program for U for the free data]
   cadr try no-time-limit 
   display cons 'read-exp [run ((read-exp) (' q))]
           cons cons "' 
                cons q 
                nil 
           nil 
   p
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
[
   Consider an n-bit string beta.
   We show that H(beta) <= n + H(n) + 912.
]
define pi
   let (loop k)
      if = k 0 nil
      cons read-bit (loop - k 1)
   (loop eval read-exp)
[Size it.]
length bits pi
[Use it.]
(U
   append bits pi   
   append bits 12
          '(0 0 1 1 1 1 1 1 0 0 0 1)
)
[
   Proof that H(x,y) <= H(x) + H(y) + 432.
]
define rho
   cons eval read-exp cons eval read-exp nil
[Size it.]
length bits rho
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
[
   Proof that H(H(x)|x) <= 208.
]
define (alpha x*)     [x* = minimum-size program for x]
   length x*          [get H(x) from x*]
[Size it.]
length bits alpha
[Use it.]

(U2 
 
[This is the program to calculate H(x):]

bits alpha  

[This is the program x* for x,]
[supposedly smallest possible:]

bits' + 1 1   

)
[Check size of program is correct]
* 8 + 1 display size display '+ 1 1
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
[Size it.]
length bits gamma
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
[Size it.]
length bits delta
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
