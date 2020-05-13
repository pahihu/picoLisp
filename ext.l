# 14apr10abu
# (c) Software Lab. Alexander Burger

(load "@lib/misc.l" "@lib/btree.l" "@lib/db.l" "@lib/pilog.l")

(setq *BigNum (* 256 1024 1024))
(setq 64bit? `(== *BigNum (format (format *BigNum))))

# vi:et:ts=3:sw=3
