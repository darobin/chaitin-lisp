[[[[[
   KRAFT INEQUALITY CRITERION FOR CONSTRUCTING COMPUTERS
   Take as input requirement pairs (output, size of program)
   and produce as output assignment pairs (program, output).
 
   We assume that the requirements are consistent.  
   I.e. the sum of 1/2 raised to each size is <= unity. 
   Then we can produce a set of assignments that meets
   the requirements and is prefex free, i.e. no extension
   of a valid program is a valid program.
  
   The basic data structure in this program is the free space pool.
   That's a list of prefixes all of whose extensions (by zero 
   or more bits) are unassigned programs.  Initially this is the 
   list consisting of the empty string because everything is free.

   The algorithm consists of assigning that program that meets
   each requirement that is available and that comes first in
   lexicographic order (0 before 1).

   The free space pool is kept in lexicographic order, to facilitate
   searching.  So the algorithm is to look for the first prefix in
   the pool that is <= the requested size in each requirement.

   If it has exactly the requested size, then that prefix is the
   program assigned to the output in the requirement.  If not,
   the prefix must be smaller than the requirement, and represents
   a piece of free storage that is a power of two larger than needed.
   So as program we assign the prefix extended by sufficiently many
   0's to reach the requested size, and then the prefix is replaced
   in the free space pool by prefix00001, prefix0001, prefix001,
   prefix01, prefix1, for all sizes up to the assigned size.
   This will always work if the Kraft inequality is satisfied.
   
   If this algorithm is given the requirements  
      (0 1) (1 2)  (2 3)   (3 4)...
   (i.e., a 1-bit p for 0, a 2-bit p for 1, a 3-bit p for 2, etc.)
   it will produce the assignments  
      (0 0) (10 1) (110 2) (1110 3)...  
   (i.e., p = 0 yields 0, p = 10 yields 1, p = 110 yields 2, etc.)
   In this case the free storage pool will always consist of a 
   single piece.

   Key fact: if you follow this first-fit algorithm, the free space
   will appear in blocks in the unit interval whose sizes are all
   distinct powers of two, and in order of increasing size.  So
   if an allocation cannot be made, the piece requested must be
   larger (at least twice as large) as the last & largest piece.
   But the total free storage is less than twice the size of the
   last & largest free piece, so allocating this would have violated
   the Kraft inequality.

   To actually run these programs, we have to feed the output of
   this program kraft.l into the previous one, exec.l.
   So there will in fact be an additional prefix in front of the
   assigned programs to tell U how to do kraft.l and how to do exec.l.
   
   Kraft is written as a function that is applied to a finite list
   of requirements and produces the corresponding finite list of
   assignments.  Exec.l will use try to run the requirement generator
   for more and more time to produce longer and longer lists of
   assignments.   It will then use the Kraft function to transform 
   these into longer and longer lists of assignments, which it will 
   use to actually run individual programs by reading them bit by 
   bit as required. The Kraft function has the property that applying 
   it to a longer list of requirements just produces a longer list 
   of assignments.  I.e., it's monotone, it never changes its mind. 
]]]]]

[used to assign a program to an output]

define (extend-with-0s bit-string [to] given-length) 
   if = length bit-string given-length  [then]
      bit-string  [else]
   append (extend-with-0s bit-string [to] - given-length 1) 
          cons 0 nil
[test it]
 
(extend-with-0s '(1 1 1) [to] 6)
(extend-with-0s '(1 1 1) [to] 5)
(extend-with-0s '(1 1 1) [to] 4)
(extend-with-0s '(1 1 1) [to] 3)
[used to subtract storage from a piece of free storage]

define (remove-piece free-prefix size-of-program)
   if = size-of-program length free-prefix
       nil  [then no storage left, else] 
   cons append (extend-with-0s free-prefix [to] - size-of-program 1) 
               cons 1 nil
        (remove-piece free-prefix - size-of-program 1)
[test it]

(remove-piece '(1 1 1) 6)
(remove-piece '(1 1 1) 5)
(remove-piece '(1 1 1) 4)
(remove-piece '(1 1 1) 3)
[ 
   Make-assignments uses debug to show us the 
   free-space-pool after making each assignment.
   If an assignment cannot be made because 
   there is not enough storage, we just skip it.
]
define (make-assignments free-space-pool requirements)

   let free-space-pool   debug free-space-pool   
                         [Done just to show pool!]

   if  atom requirements nil  [no requirements => no assignments]
                              [If so, we're finished!]

   let requirement       car  requirements
   let requirements      cdr  requirements
   let output-of-program car  requirement
   let size-of-program   cadr requirement
   let already-scanned   nil
   let not-yet-scanned   free-space-pool

   let (loop-thru-free-space-pool) [DEFINE IT!]

       if atom not-yet-scanned [cannot make this assignment!]
          [indicate problem and go to next requirement]
          cons not-enough-storage! 
               (make-assignments free-space-pool requirements)  

       let free-prefix      car not-yet-scanned
       let not-yet-scanned  cdr not-yet-scanned
       if < size-of-program length free-prefix

          [doesn't fit --- continue scanning]
          let already-scanned 
              append already-scanned 
                     cons free-prefix nil
          (loop-thru-free-space-pool)

       [fits! --- make assignment]
       [add to list of rest of assignments]
       let free-space-pool 
           append already-scanned 
           append (remove-piece free-prefix size-of-program)
                  not-yet-scanned

       let assignment  
           [make assignment - add to list of rest of assignments]
           [found free piece where it fits!] 
           [extend with zeros to correct size]
           cons (extend-with-0s free-prefix [to] size-of-program) 
           cons output-of-program 
                nil

       [return full list of assignments]
       cons assignment
            (make-assignments free-space-pool requirements)  

   [NOW DO IT!]
   (loop-thru-free-space-pool)
[put it all together]

define (kraft requirements)

   let free-space-pool '(()) [everything free]
   
   (make-assignments free-space-pool requirements)
[TEST KRAFT!]

(kraft '((x 0) (y 1))) 
(kraft '((a 1) (b 0) (c 1))) 
(kraft '((x 1) (y 2))) 
(kraft '((a 1) (b 2) (c 3) (d 4) (e 5))) 
(kraft '((e 5) (d 4) (c 3) (b 2) (a 1))) 
(kraft '((e 5) (c 3) (d 4) (a 1) (b 2))) 
