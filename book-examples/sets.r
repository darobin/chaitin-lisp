LISP Interpreter Run

[[[[[

 Elementary Set Theory in LISP (finite sets) 

]]]]]

[Set membership predicate:]

define (member? e[lement] set)
   [Is set empty?]
   if atom set [then] false [else] 
   [Is the element that we are looking for the first element?]
   if = e car set [then] true [else] 
   [recursion step!]
   [return] (member? e cdr set)

define      member?
value       (lambda (e set) (if (atom set) false (if (= e (car
             set)) true (member? e (cdr set)))))

 
(member? 1 '(1 2 3))

expression  (member? 1 (' (1 2 3)))
value       true

(member? 4 '(1 2 3))

expression  (member? 4 (' (1 2 3)))
value       false

 
[Subset predicate:]

define (subset? set1 set2)
   [Is the first set empty?]
   if atom set1 [then] true [else]
   [Is the first element of the first set in the second set?]
   if (member? car set1 set2) 
      [then] [recursion!] (subset? cdr set1 set2) 
      [else] false 

define      subset?
value       (lambda (set1 set2) (if (atom set1) true (if (memb
            er? (car set1) set2) (subset? (cdr set1) set2) fal
            se)))

 
(subset? '(1 2) '(1 2 3))

expression  (subset? (' (1 2)) (' (1 2 3)))
value       true

(subset? '(1 4) '(1 2 3))

expression  (subset? (' (1 4)) (' (1 2 3)))
value       false


[Set union:]

define (union x y)
   [Is the first set empty?]  
   if atom x [then] [return] y [else]
   [Is the first element of the first set in the second set?]
   if (member? car x y) 
      [then] [return] (union cdr x y)
      [else] [return] cons car x (union cdr x y)

define      union
value       (lambda (x y) (if (atom x) y (if (member? (car x) 
            y) (union (cdr x) y) (cons (car x) (union (cdr x) 
            y)))))


(union '(1 2 3) '(2 3 4))

expression  (union (' (1 2 3)) (' (2 3 4)))
value       (1 2 3 4)


[Union of a list of sets:]

define (unionl l) if atom l nil (union car l (unionl cdr l))

define      unionl
value       (lambda (l) (if (atom l) nil (union (car l) (union
            l (cdr l)))))


(unionl '((1 2) (2 3) (3 4)))

expression  (unionl (' ((1 2) (2 3) (3 4))))
value       (1 2 3 4)


[Set intersection:]

define (intersection x y)
   [Is the first set empty?]
   if atom x [then] [return] nil [empty set] [else]
   [Is the first element of the first set in the second set?]
   if (member? car x y) 
      [then] [return] cons car x (intersection cdr x y)
      [else] [return] (intersection cdr x y)

define      intersection
value       (lambda (x y) (if (atom x) nil (if (member? (car x
            ) y) (cons (car x) (intersection (cdr x) y)) (inte
            rsection (cdr x) y))))


(intersection '(1 2 3) '(2 3 4))

expression  (intersection (' (1 2 3)) (' (2 3 4)))
value       (2 3)


[Relative complement of two sets x and y = x - y:]

define (complement x y)
   [Is the first set empty?]
   if atom x [then] [return] nil [empty set] [else]
   [Is the first element of the first set in the second set?]
   if (member? car x y) 
      [then] [return] (complement cdr x y)
      [else] [return] cons car x (complement cdr x y)

define      complement
value       (lambda (x y) (if (atom x) nil (if (member? (car x
            ) y) (complement (cdr x) y) (cons (car x) (complem
            ent (cdr x) y)))))


(complement '(1 2 3) '(2 3 4))

expression  (complement (' (1 2 3)) (' (2 3 4)))
value       (1)



[Cartesian product of an element with a list:]

define (product1 e y) 
   if atom y 
      [then] nil 
      [else] cons cons e cons car y nil (product1 e cdr y)

define      product1
value       (lambda (e y) (if (atom y) nil (cons (cons e (cons
             (car y) nil)) (product1 e (cdr y)))))


(product1 3 '(4 5 6))

expression  (product1 3 (' (4 5 6)))
value       ((3 4) (3 5) (3 6))


[Cartesian product of two sets = set of ordered pairs:]

define (product x y)
   [Is the first set empty?]
   if atom x [then] [return] nil [empty set] [else]
   [return] (union (product1 car x y) (product cdr x y))

define      product
value       (lambda (x y) (if (atom x) nil (union (product1 (c
            ar x) y) (product (cdr x) y))))


(product '(1 2 3) '(x y z))

expression  (product (' (1 2 3)) (' (x y z)))
value       ((1 x) (1 y) (1 z) (2 x) (2 y) (2 z) (3 x) (3 y) (
            3 z))


[Product of an element with a list of sets:]

define (product2 e y)  
   if atom y 
      [then] nil 
      [else] cons cons e car y (product2 e cdr y)

define      product2
value       (lambda (e y) (if (atom y) nil (cons (cons e (car 
            y)) (product2 e (cdr y)))))


(product2 3 '((4 5) (5 6) (6 7)))

expression  (product2 3 (' ((4 5) (5 6) (6 7))))
value       ((3 4 5) (3 5 6) (3 6 7))


[Set of all subsets of a given set:]

define (subsets x)
   if atom x 
      [then] '(()) [else]
      let y [be] (subsets cdr x) [in]
      (union y (product2 car x y))

define      subsets
value       (lambda (x) (if (atom x) (' (())) ((' (lambda (y) 
            (union y (product2 (car x) y)))) (subsets (cdr x))
            )))


(subsets '(1 2 3))

expression  (subsets (' (1 2 3)))
value       (() (3) (2) (2 3) (1) (1 3) (1 2) (1 2 3))

length (subsets '(1 2 3))

expression  (length (subsets (' (1 2 3))))
value       8

(subsets '(1 2 3 4))

expression  (subsets (' (1 2 3 4)))
value       (() (4) (3) (3 4) (2) (2 4) (2 3) (2 3 4) (1) (1 4
            ) (1 3) (1 3 4) (1 2) (1 2 4) (1 2 3) (1 2 3 4))

length (subsets '(1 2 3 4))

expression  (length (subsets (' (1 2 3 4))))
value       16

End of LISP Run

Elapsed time is 0 seconds.
