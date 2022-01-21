# 18jan22 Software Lab. Alexander Burger
# Dining Philosophers
# pil @lib/simul.l --symbols simul dining2.l +

(de now (Str)
   (prinl (tim$ (* 60 *Time)) " " (co) " " Str) )

(de dining (Left Right)
   (loop
      (now "thinking")
      (pause (rand 180 240))
      (now "hungry")
      (until (nor (val Left) (val Right))
         (pause (rand 1 5)) )
      (set Left (set Right (co)))
      (now "eating")
      (pause 20)
      (set Left (set Right NIL)) ) )

'(de dining (Left Right)
   (loop
      (now "thinking")
      (pause (rand 180 240))
      (now "hungry")
      (until (nor (val Left) (val Right))
         (pause (rand 1 5)) )
      (set Left (set Right (co)))
      (now "eating")
      (pause 20)
      (set Left (set Right NIL))
      (now "sleeping")
      (pause 'morning)
      (now "get up") ) )

'(de dining (Left Right Co)
   (loop
      (now "thinking")
      (T (pause (rand 180 240)))
      (now "hungry")
      (and Co (wake Co T))
      (T
         (loop
            (NIL (or (val Left) (val Right)))
            (T (pause (rand 1 5)) T) ) )
      (set Left (set Right (co)))
      (now "eating")
      (T (pause 20))
      (set Left (set Right NIL)) )
   (now "EXIT") )

(co 'Aristotle
   (dining '*ForkA '*ForkB) )
(co 'Kant
   (dining '*ForkB '*ForkC) )
(co 'Spinoza
   (dining '*ForkC '*ForkD) )
(co 'Marx
   (dining '*ForkD '*ForkE) )
(co 'Russell
   (dining '*ForkE '*ForkA) )
