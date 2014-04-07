[[[[[
   FUNDAMENTAL DECOMPOSITION
   We prove here that 
      H(y|x) <= H_C(x,y) - H(x) + c
]]]]]

define (all-together x*)

let c debug 100 [constant to satisfy Kraft (see lemma)]

let x debug run-utm-on debug x*

let H-of-x debug length x*

[programs we've discovered that calculate pairs 
 starting with x]
let programs nil

let (stage n)
    [generate requirements for all new programs we've
     discovered that produce (x y) pairs]
    let programs 
        (add-to-set debug (halts? nil debug n) programs) 
    (stage + n 1)

[at stage n = 0, 1, 2, 3, ...]
[look at all programs with <=n bits that halt within time n]
[returns list of all of them that produce pairs (x y)]
let (halts? p bits-left)
   let v try n C p [C is eval read-exp if C = U]
   if = success car v (look-at cadr v)
   if = 0 bits-left nil
   append (halts? append p cons 0 nil - bits-left 1)
          (halts? append p cons 1 nil - bits-left 1)

[returns (p) if C(p) = (x y), otherwise ()]
let (look-at v)
   if (and (is-pair v) 
            = x car v ) cons p nil
      nil

[logical "and"]
let (and p q)
   if p q false

[is x a pair?]
let (is-pair? x)
   if atom x         false
   if atom cdr x     false
   if atom cdr cdr x true
                     false

[is an element in a set?]
let (is-in-set? element set)
   if atom set          false
   if = element car set true
   (is-in-set? element cdr set)

[forms set union avoiding duplicates, 
 and makes requirement for each new find]
let (add-to-set new old)
   if  atom new  old 
   let first-new car new
   let rest-new  cdr new
   if (is-in-set? first-new old) (add-to-set rest-new old)
   (do (make-requirement first-new)
       cons first-new (add-to-set rest-new old)
   )
       
[first argument discarded, done for side-effect only!]
let (do x y) y

[given new p such that C(p) = (x y), 
 we produce the requirement for C_x
 that there be a program for y that is |p|-H(x)+c bits long]
let (make-requirement p)
   display cons cadr cadr try no-time-limit C p 
           cons - + c length p H-of-x
                nil

let C ' [here eval read-exp gives U]
[test case special-purpose computer C here in place of U:] 
[C(00100001) with x-1 and y-1 0's gives pair (x xy)]
[loop function gives number of bits up to next 1 bit]
   let (loop n)
      if = 1 read-bit n
      (loop + n 1)
   let x (loop 1)
   let y (loop 1)
   cons x cons * x y nil

[HERE GOES!]
(stage 0)

define      all-together
value       (lambda (x*) ((' (lambda (c) ((' (lambda (x) ((' (
            lambda (H-of-x) ((' (lambda (programs) ((' (lambda
             (stage) ((' (lambda (halts?) ((' (lambda (look-at
            ) ((' (lambda (and) ((' (lambda (is-pair?) ((' (la
            mbda (is-in-set?) ((' (lambda (add-to-set) ((' (la
            mbda (do) ((' (lambda (make-requirement) ((' (lamb
            da (C) (stage 0))) (' ((' (lambda (loop) ((' (lamb
            da (x) ((' (lambda (y) (cons x (cons (* x y) nil))
            )) (loop 1)))) (loop 1)))) (' (lambda (n) (if (= 1
             (read-bit)) n (loop (+ n 1)))))))))) (' (lambda (
            p) (display (cons (car (cdr (car (cdr (try no-time
            -limit C p))))) (cons (- (+ c (length p)) H-of-x) 
            nil)))))))) (' (lambda (x y) y))))) (' (lambda (ne
            w old) (if (atom new) old ((' (lambda (first-new) 
            ((' (lambda (rest-new) (if (is-in-set? first-new o
            ld) (add-to-set rest-new old) (do (make-requiremen
            t first-new) (cons first-new (add-to-set rest-new 
            old)))))) (cdr new)))) (car new)))))))) (' (lambda
             (element set) (if (atom set) false (if (= element
             (car set)) true (is-in-set? element (cdr set)))))
            )))) (' (lambda (x) (if (atom x) false (if (atom (
            cdr x)) false (if (atom (cdr (cdr x))) true false)
            ))))))) (' (lambda (p q) (if p q false)))))) (' (l
            ambda (v) (if (and (is-pair v) (= x (car v))) (con
            s p nil) nil)))))) (' (lambda (p bits-left) ((' (l
            ambda (v) (if (= success (car v)) (look-at (car (c
            dr v))) (if (= 0 bits-left) nil (append (halts? (a
            ppend p (cons 0 nil)) (- bits-left 1)) (halts? (ap
            pend p (cons 1 nil)) (- bits-left 1))))))) (try n 
            C p))))))) (' (lambda (n) ((' (lambda (programs) (
            stage (+ n 1)))) (add-to-set (debug (halts? nil (d
            ebug n))) programs))))))) nil))) (debug (length x*
            ))))) (debug (car (cdr (try no-time-limit (' (eval
             (read-exp))) (debug x*)))))))) (debug 100)))

define x* 3

define      x*
value       3

length bits x* 

expression  (length (bits x*))
value       16

[give all-together x*]
try 60 cons cons "'
            cons all-together 
            nil                      
       cons cons "' 
            cons bits x* 
            nil 
       nil 
    nil

expression  (try 60 (cons (cons ' (cons all-together nil)) (co
            ns (cons ' (cons (bits x*) nil)) nil)) nil)
debug       100
debug       (0 0 1 1 0 0 1 1 0 0 0 0 1 0 1 0)
debug       3
debug       16
debug       0
debug       ()
debug       1
debug       ()
debug       2
debug       ()
debug       3
debug       ()
debug       4
debug       ((0 0 1 1))
debug       5
debug       ((0 0 1 0 1) (0 0 1 1))
debug       6
debug       ((0 0 1 0 0 1) (0 0 1 0 1) (0 0 1 1))
debug       7
debug       ((0 0 1 0 0 0 1) (0 0 1 0 0 1) (0 0 1 0 1) (0 0 1 
            1))
debug       8
debug       ((0 0 1 0 0 0 0 1) (0 0 1 0 0 0 1) (0 0 1 0 0 1) (
            0 0 1 0 1) (0 0 1 1))
debug       9
value       (failure out-of-time ((3 88) (6 89) (9 90) (12 91)
             (15 92)))

define x* 4

define      x*
value       4

length bits x* 

expression  (length (bits x*))
value       16

[give all-together x*]
try 60 cons cons "'
            cons all-together 
            nil                      
       cons cons "' 
            cons bits x* 
            nil 
       nil 
    nil

expression  (try 60 (cons (cons ' (cons all-together nil)) (co
            ns (cons ' (cons (bits x*) nil)) nil)) nil)
debug       100
debug       (0 0 1 1 0 1 0 0 0 0 0 0 1 0 1 0)
debug       4
debug       16
debug       0
debug       ()
debug       1
debug       ()
debug       2
debug       ()
debug       3
debug       ()
debug       4
debug       ()
debug       5
debug       ((0 0 0 1 1))
debug       6
debug       ((0 0 0 1 0 1) (0 0 0 1 1))
debug       7
debug       ((0 0 0 1 0 0 1) (0 0 0 1 0 1) (0 0 0 1 1))
debug       8
debug       ((0 0 0 1 0 0 0 1) (0 0 0 1 0 0 1) (0 0 0 1 0 1) (
            0 0 0 1 1))
debug       9
value       (failure out-of-time ((4 89) (8 90) (12 91) (16 92
            )))
