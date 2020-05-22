# (msg "### co/yield/stack tests ###")

### stack ###
(test  64
   (stack) )
(test 200
   (stack 200) )
(test 200
   (stack) )

### co ####
# create two coroutines
(de myinc ()
   (co 'inc (let N 0 (loop (yield (inc 'N))))) )
(de mydec ()
   (co 'dec (let N 0 (loop (yield (dec 'N))))) )

(test 1
   (myinc) )
(test -1
   (mydec) )
(test (stack)
   '(dec inc . 200) )

(test 2
   (myinc) )
(test -2
   (mydec) )
(test T
   (co 'inc) )
(test T
   (co 'dec) )
(test NIL
   (co 'abc) )

(de pythag (N)   # A generator function
   (if (=T N)
      (co 'rt)  # Stop
      (co 'rt
         (for X N
            (for Y (range X N)
               (for Z (range Y N)
                  (when (= (+ (* X X) (* Y Y)) (* Z Z))
                     (yield (list X Y Z)) ) ) ) ) ) ) )

(test '(3 4 5)
   (pythag 20) )
(test '(5 12 13)
   (pythag 20) )
(test (6 8 10)
   (pythag 20) )

(co "rt1"                              # Start first routine
   (msg (yield 1) " in rt1 from rt2")  # Return '1', wait for value from "rt2"
   7 )                                 # Then return '7'

(co "rt2"                              # Start second routine
   (yield 2 "rt1") )                   # Send '2' to "rt1"


# Start first routine
# Return '1', wait for value from "rt2"
# Then return '7'
(de myrt1 ()
   (co 'rt1
      (prinl "enter rt1")
      (yield (yield 1))
      (prinl "return rt1")
      7 ) )

# Start second routine
# Send '2' to "rt1"
(de myrt2 ()
   (co 'rt2
      (prinl "enter rt2")
      (yield 2 'rt1)
      (prinl "return rt2") ) )

(test 1
   (myrt1) )

(test 2
   (myrt2) )

(test 7
   (myrt1) )

(test "return rt2"
   (myrt2))

# (msg 'OK-test-co)
