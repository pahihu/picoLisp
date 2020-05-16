# 14apr10abu
# (c) Software Lab. Alexander Burger

(load "@lib/misc.l" "@lib/btree.l" "@lib/db.l" "@lib/pilog.l")

(setq *BigNum (* 256 1024 1024))
(setq 64bit? `(== *BigNum (format (format *BigNum))))
(setq *Word   (if 64bit? 8 4))
(de shlib (nm)
   (pack nm (case *OS ("Darwin" ".dylib") (T ".so"))) )

# vi:et:ts=3:sw=3
