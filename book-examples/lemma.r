[[[[[
   Lemma for 
      H(y|x) <= H(x,y) - H(x) + c

   We show that 
      H(x) <= -log_2 Sum_y P((x y)) + c 
 
   Proof: From U construct U' such that
      if U(p) = (x y), then U'(p) = x.

   Then apply the previous chapter to get
      H(x) <= -log_2 P'(x) + c  
           <= -log_2 Sum_y P((x y)) + c 
]]]]]

define U-prime

let (is-pair? x)
   if atom x         false
   if atom cdr x     false
   if atom cdr cdr x true
                     false

[run original program for U]

let v eval read-exp 

[and if is a pair, return first element]

if (is-pair? v) car v 

[otherwise loop forever]

   let (loop) [be] (loop) [in] 
      (loop)

define      U-prime
value       ((' (lambda (is-pair?) ((' (lambda (v) (if (is-pai
            r? v) (car v) ((' (lambda (loop) (loop))) (' (lamb
            da () (loop))))))) (eval (read-exp))))) (' (lambda
             (x) (if (atom x) false (if (atom (cdr x)) false (
            if (atom (cdr (cdr x))) true false))))))

[Test it!]

run-utm-on bits' xyz

expression  (car (cdr (try no-time-limit (' (eval (read-exp)))
             (bits (' xyz)))))
value       xyz

run-utm-on bits' cons a nil

expression  (car (cdr (try no-time-limit (' (eval (read-exp)))
             (bits (' (cons a nil))))))
value       (a)

run-utm-on bits' cons a cons b nil

expression  (car (cdr (try no-time-limit (' (eval (read-exp)))
             (bits (' (cons a (cons b nil)))))))
value       (a b)

run-utm-on bits' cons a cons b cons c nil

expression  (car (cdr (try no-time-limit (' (eval (read-exp)))
             (bits (' (cons a (cons b (cons c nil))))))))
value       (a b c)

cadr try 99 U-prime bits' xyz

expression  (car (cdr (try 99 U-prime (bits (' xyz)))))
value       out-of-time

cadr try 99 U-prime bits' cons a nil

expression  (car (cdr (try 99 U-prime (bits (' (cons a nil))))
            ))
value       out-of-time

cadr try 99 U-prime bits' cons a cons b nil

expression  (car (cdr (try 99 U-prime (bits (' (cons a (cons b
             nil)))))))
value       a

cadr try 99 U-prime bits' cons a cons b cons c nil

expression  (car (cdr (try 99 U-prime (bits (' (cons a (cons b
             (cons c nil))))))))
value       out-of-time
