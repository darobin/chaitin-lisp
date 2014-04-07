LISP Interpreter Run

[[[[ Omega in the limit from below! ]]]]
 
define (count-halt prefix bits-left-to-extend)
    let x try t 'eval read-exp prefix
    if = success car x    ^ 2 bits-left-to-extend
    if = out-of-time cadr x    0
    if = bits-left-to-extend 0    0
    + (count-halt append prefix '(0) - bits-left-to-extend 1)
      (count-halt append prefix '(1) - bits-left-to-extend 1)

define      count-halt
value       (lambda (prefix bits-left-to-extend) ((' (lambda (
            x) (if (= success (car x)) (^ 2 bits-left-to-exten
            d) (if (= out-of-time (car (cdr x))) 0 (if (= bits
            -left-to-extend 0) 0 (+ (count-halt (append prefix
             (' (0))) (- bits-left-to-extend 1)) (count-halt (
            append prefix (' (1))) (- bits-left-to-extend 1)))
            ))))) (try t (' (eval (read-exp))) prefix)))

define (omega t) cons (count-halt nil t)
                 cons /
                 cons ^ 2 t
                      nil

define      omega
value       (lambda (t) (cons (count-halt nil t) (cons / (cons
             (^ 2 t) nil))))

(omega 0)

expression  (omega 0)
value       (0 / 1)

(omega 1)

expression  (omega 1)
value       (0 / 2)

(omega 2)

expression  (omega 2)
value       (0 / 4)

(omega 3)

expression  (omega 3)
value       (0 / 8)

(omega 8)

expression  (omega 8)
value       (1 / 256)

End of LISP Run

Elapsed time is 0 seconds.
