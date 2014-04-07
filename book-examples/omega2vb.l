[[[[ Omega in the limit from below! ]]]]
 
define (count-halt prefix bits-left-to-extend)
    let x try t 'eval read-exp prefix
    if = success car x    ^ 2 bits-left-to-extend
    if = out-of-time cadr x    0
    if = bits-left-to-extend 0    0
    + (count-halt append prefix '(0) - bits-left-to-extend 1)
      (count-halt append prefix '(1) - bits-left-to-extend 1)
define (omega t) cons (count-halt nil t)
                 cons /
                 cons ^ 2 t
                      nil
(omega 0)
(omega 1)
(omega 2)
(omega 3)
(omega 8)
