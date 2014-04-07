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

[Test it!]

run-utm-on bits' xyz
run-utm-on bits' cons a nil
run-utm-on bits' cons a cons b nil
run-utm-on bits' cons a cons b cons c nil

cadr try 99 U-prime bits' xyz
cadr try 99 U-prime bits' cons a nil
cadr try 99 U-prime bits' cons a cons b nil
cadr try 99 U-prime bits' cons a cons b cons c nil
