# 23mar16abu
# (c) Software Lab. Alexander Burger

(de gcc (Nm L . Lst)
   (out (tmp Nm ".c") (here "/**/"))
   ~(case *OS
      (("Linux" "FreeBSD" "OpenBSD")
         (quote
            (apply call L "gcc" "-o" (tmp Nm)
               "-fPIC" "-shared" "-export-dynamic"
               "-O" "-falign-functions" "-fomit-frame-pointer"
               "-W" "-Wimplicit" "-Wreturn-type" "-Wunused" "-Wformat"
               "-Wuninitialized" "-Wstrict-prototypes"
               "-pipe" "-D_GNU_SOURCE" (tmp Nm ".c") ) ) )
      ("Darwin"
         (quote
            (apply call L "gcc" "-o" (tmp Nm)
               "-dynamiclib" "-undefined" "dynamic_lookup"
               (if 64bit? "-m64" "-m32")
               "-O2" "-mllvm" "-align-all-functions=5" "-fomit-frame-pointer"
               "-W" "-Wimplicit" "-Wreturn-type" "-Wunused" "-Wformat"
               "-Wuninitialized" "-Wstrict-prototypes" "-Wno-parentheses"
               "-pipe" "-D_GNU_SOURCE" (tmp Nm ".c") ) ) )
      ("SunOS"
         (quote
            (apply call L "gcc" "-o" (tmp Nm)
               "-fPIC" "-shared" "-m64"
               "-O" "-falign-functions" "-fomit-frame-pointer"
               "-W" "-Wimplicit" "-Wreturn-type" "-Wunused" "-Wformat"
               "-Wuninitialized" "-Wstrict-prototypes"
               "-pipe" "-D_GNU_SOURCE" (tmp Nm ".c") ) ) ) )
   (for L Lst
      (def (car L)
         (list
            (cadr L)
            (cons 'native (tmp Nm) (name (caddr L)) (cdddr L)) ) )
      (when (== '@ (fin (cadr L)))
         (push (cdaar L) 'pass) ) ) )

(de unsigned (N)
   (& `(dec (** 2 32)) (+ N `(** 2 32))) )

# vi:et:ts=3:sw=3
