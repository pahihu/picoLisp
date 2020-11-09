(load "lib/native.l")

# (msg "### struct/lisp/native tests ###")

### lisp ###
(gcc "ltest" NIL
   (cbTest (Fun) cbTest 'N Fun)
   (lispTest (Fun A B C D E) lispTest 'N Fun A B C D E) )

#include <stdio.h>
long cbTest(long(*fun)(long,long,long,long,long)) {
   fprintf(stderr,"cbTest(%p)\n",fun);
   return fun(1,2,3,4,5);
}

extern long lisp(char*,long,long,long,long,long);
long lispTest(char *s,long a1,long a2,long a3,long a4,long a5) {
   fprintf(stderr,"lispTest(%s,%ld,%ld,%ld,%ld,%ld)\n",s,a1,a2,a3,a4,a5);
   return lisp(s,a1,a2,a3,a4,a5);
}
/**/

(test 120
   (cbTest
      (lisp 'cbTest
         '((A B C D E)
            (msg (list A B C D E))
            (* A B C D E) ) ) ) )


(de calc (A B C D E)
   (println 'calc A B C D E)
   (* A B C D E) )

(test 120
   (lispTest 'calc 1 2 3 4 5) )


### native ###
(test (sys "TERM")
   (%@ "getenv" 'S "TERM") )

(setq *Word (if 64bit? 8 4))

(test 8
   (%@ "printf" 'I "abc%d%s^J" T (+ 3 4) (pack "X" "Y" "Z")) )

(test 16
   (%@ "printf" 'I "This is %.3f^J" T (123456 . 1000)) )

(test 
   (129 254 139 254 135 87 108 62 203 34 66 111 142 87 132 115 130 145 122 207)
   (native `(shlib "libcrypto") "SHA1" '(B . 20) "abcd" 4 0) )

(use Tim
   # time_t 8   # Get time_t structure
   (%@ "time" NIL (list 'Tim (cons *Word 'B *Word)))  
   # Read local time
   (println (%@ "localtime" '(I . 9) (cons NIL (list *Word) Tim))) )

# (32 18 13 31 11 109 4 364 0)  # 13:18:32, Dec. 31st, 2009

### struct ###
(scl 2)

## /* We assume the following C structure */
## typedef struct value {
##    int x, y;         (* 2 *Word)
##    double a, b, c;   24bytes
##    long z;           *Word
##    char nm[4];
## } value;

# Allocate structure
(setq P (%@ "malloc" 'N (+ 24 4 (* 3 *Word))))

# Store two integers, three doubles, one long, and four characters
(test P
   (struct P 'N -7 -4 (1.0 0.11 0.22 0.33) (cons 7 *Word) 65 66 67 0) )

# Extract the structure
(test '((7 4) (11 22 33) 7 ("A" "B" "C"))
   (struct P '((I . 2) (1.0 . 3) N (C . 4))) )

# Do both in a single call (allowing conversions of data types)
(test '((7 4) (11 22 33) 7 ("A" "B" "C"))
   (struct P
      '((I . 2) (1.0 . 3) N (C . 4))
      -7 -4 (1.0 0.11 0.22 0.33) (cons 7 *Word) 65 66 67 0 ) )

# De-allocate structure
(%@ "free" NIL P)

(scl 0)

# (msg 'OK-test-cb)
