/* 25feb15abu
 * (c) Software Lab. Alexander Burger
 */

#include "pico.h"

#define MAX    MASK                    // Max digit size    0xFFFF....
// #define OVFL   (num(1)<<(BITS-1))      // Carry/Overflow    0x8000....

// For Solaris 10
#ifdef __SVR4
#include <ieeefp.h>
static int isinf(double x) {return !finite(x) && x==x;}
#endif

void digAdd(any,word);
void digDiv2(any);
static void digSub1(any);
void bigAdd(any,any);
static any bigSub(any,any);
any bigCopy(any);
static inline any NEG(any);

static void divErr(any ex) {err(ex,NULL,"Div/0");}

/* Box double word */
any boxWord2(word2 t) {
#ifdef __LP64__
   if (hi(t))
      return consNum(num(t), BOX(hi(t)));
   return BOX(num(t));
#else
   word u;
   if (hi(t))
      return consNum(num(t<<1), consNum(hi(t<<1), hi(t) & OVFL? BOX(1) : Nil));
   u = num(t);
   return consNum(u << 1, u & OVFL? BOX(1) : Nil);
#endif
}

/* Box double word, then shorten */
any shortBoxWord2(word2 t) {
   return shorten(boxWord2(t));
}

word2 unBoxWord2(any x) {
   word2 n;

   ASSERT(isBig(x));

#ifndef __LP64__
   // shift right 1bit
   digDiv2(x);
#endif

   // this is the low-order word
   n = unDigBig(x);

   // cdr(x) is the high-order word
   if (isNum(x = cdr(numCell(x))))
      n = ((word2)unDigBig(x) << BITS) + n; 

   return n;
}

any shorten(any x) {
   ASSERT(isNum(x));

   if (!shortLike(x) && isNil(cdr(numCell(x)))) {
#ifdef __LP64__
      word u = unDigBig(x);
      if (u < (SHORTMAX / 2)) {
         u = SHORT(u) + isNeg(x);
         return mkShort(u);
      }
#else
      word u = unDigBig(x);
      if (u < SHORTMAX) {
         return mkShort(u);
      }
#endif
   }
   return x;
}

// Convert signed number to short/bigNum
any cvtSigned(any x) {
   int sign;

   ASSERT(isBig(x));

#ifdef __LP64__
   sign = unDigBig(x) & 1;
   digDiv2(x);
   if (isNil(nextDigBig(x))) {
      word u = unDigBig(x);
      if (u < (SHORTMAX / 2))
         return mkShort(SHORT(u) + sign);
   }
   return sign? neg(x) : x;
#else
   return shorten(x);
#endif
}

/* Bignum copy */
any bigCopy(any x) {
   any y;
   cell c1, c2;

   ASSERT(isBig(x));

#ifdef __LP64__
   int sign;
   sign = isNeg(x);
#endif

   Push(c1, x);
   Push(c2, y = BOX(unDigBig(x)));
   while (isNum(x = cdr(numCell(x))))
      y = cdr(numCell(y)) = BOX(unDigBig(x));
   drop(c1);

#ifdef __LP64__
   return sign? neg(data(c2)) : data(c2);
#else
   return data(c2);
#endif
}

/* Remove leading zero words */
void zapZero(any x) {
   any r = x;

   ASSERT(isBig(x));

   while (isNum(x = cdr(numCell(x))))
      if (unDigBig(x))
         r = x;
   cdr(numCell(r)) = x;
}

/* Multiply a (positive) bignum by 2 */
void digMul2(any x) {
   any y;
   word n, carry;

   ASSERT(isBig(x));

   n = unDigBig(x),  setDig(x, n + n),  carry = n & OVFL;
   while (isNum(x = cdr(numCell(y = x)))) {
      n = unDigBig(x);
      setDig(x, n + n + (carry? 1 : 0));
      carry = n & OVFL;
   }
   if (carry)
      cdr(numCell(y)) = BOX(1);
}

/* Shift right by one bit */
void digDiv2(any x) {
   any r, y;

   ASSERT(isBig(x));

   r = NULL;
   setDig(x, unDigBig(x) / num(2));
   while (isNum(x = cdr(numCell(y = x)))) {
      if (unDigBig(x) & 1)
         setDig(y, unDigBig(y) | OVFL);
      setDig(x, unDigBig(x) / num(2));
      r = y;
   }
   if (r  &&  unDigBig(y) == 0)
      cdr(numCell(r)) = x;
}

/* Add two (positive) bignums */
void bigAdd(any dst, any src) {
   any x;
   word n, carry;

   ASSERT(isBig(dst) && isBig(src));

   carry = (POSDIG(unDigBig(src)) > num(setDig(dst, POSDIG(unDigBig(src)) + POSDIG(unDigBig(dst)))));
   src = cdr(numCell(src));
   dst = cdr(numCell(x = dst));
   for (;;) {
      if (!isNum(src)) {
         while (isNum(dst)) {
            if (!carry)
               return;
            carry = 0 == num(setDig(dst, 1 + unDigBig(dst)));
            dst = cdr(numCell(x = dst));
         }
         break;
      }
      if (!isNum(dst)) {
         do {
            carry = unDigBig(src) > (n = carry + unDigBig(src));
            x = cdr(numCell(x)) = BOX(n);
         } while (isNum(src = cdr(numCell(src))));
         break;
      }
      if ((n = carry + unDigBig(src)) >= carry) {
         carry = unDigBig(dst) > (n += unDigBig(dst));
         setDig(dst,n);
      }
      src = cdr(numCell(src));
      dst = cdr(numCell(x = dst));
   }
   if (carry)
      cdr(numCell(x)) = BOX(1);
}

/* Add digit to a (positive) bignum */
void digAdd(any x, word n) {
   any y;
   word carry;

   ASSERT(isBig(x));

   carry = n > num(setDig(x, n + unDigBig(x)));
   while (carry) {
      if (isNum(x = cdr(numCell(y = x))))
         carry = 0 == num(setDig(x, 1 + unDigBig(x)));
      else {
         cdr(numCell(y)) = BOX(1);
         break;
      }
   }
}

static any DADD(any x, word n) {
   cell c1;
   ASSERT(isNum(x));

   // scale n to the actual type of x
   // 32bit short/big needs scaling
   // 64bit only short needs scaling

   if (shortLike(x)) {
      if (SHORT(n) < SHORTMAX)
         return box(unDigShort(x) + SHORT(n));
      Push(c1, big(x));
      digAdd(data(c1), BIG(n));
      return Pop(c1);
   }
   return digAdd(x, BIG(n)), x;
}

/* Add 1 to x, wrap around */
any DADDU1(any x) {
   ASSERT(isNum(x));

   if (shortLike(x)) {
#ifdef __LP64__
      return (any)(num(x) + ShortOne);
#else
      if ((num(x) & ~NORM) != ShortMax)
         return (any)(num(x) + ShortOne);
      return BOX((ShortMax >> NORMBITS) + SHORT(1));
#endif
   }
   setDig(x, unDigBig(x) + BIG(1));
   return shorten(x);
}

any DADDU(any x, word n) {
   ASSERT(isNum(x));

   if (shortLike(x)) {
#ifdef __LP64__
      return (any)(num(x) + SHORT(n));
#else
      word z;
      if (__builtin_uaddl_overflow(num(x), SHORT(n), &z))
         return BOX(unDigShort(x) + SHORT(n));
      return (any)z;
#endif
   }
   setDig(x, unDigBig(x) + BIG(n));
   return shorten(x);
}

/* Subtract two (positive) bignums */
static any bigSub(any dst, any src) {
   any x, y;
   word n, borrow;

   ASSERT(isBig(dst) && isBig(src));

#ifdef __LP64__
   dst = pos(dst);
#endif

   borrow = MAX - POSDIG(unDigBig(src)) < num(setDig(dst, POSDIG(unDigBig(dst)) - POSDIG(unDigBig(src))));
   y = dst;
   for (;;) {
      src = cdr(numCell(src));
      dst = cdr(numCell(x = dst));
      if (!isNum(src)) {
         while (isNum(dst)) {
            if (!borrow)
               goto Exit;
            borrow = MAX == num(setDig(dst, unDigBig(dst) - 1));
            dst = cdr(numCell(x = dst));
         }
         break;
      }
      if (!isNum(dst)) {
         do {
            if (borrow)
               n = MAX - unDigBig(src);
            else
               borrow = 0 != (n = -unDigBig(src));
            x = cdr(numCell(x)) = BOX(n);
         } while (isNum(src = cdr(numCell(src))));
         break;
      }
      if ((n = unDigBig(dst) - borrow) > MAX - borrow)
         setDig(dst, MAX - unDigBig(src));
      else
         borrow = num(setDig(dst, n - unDigBig(src))) > MAX - unDigBig(src);
   }
   if (borrow) {
      dst = y;
      borrow = 0 != (n = -unDigBig(dst));
      setDig(dst, n);
      y = neg(y);  /* Negate */
      while (dst != x) {
         dst = cdr(numCell(dst));
         if (borrow)
            setDig(dst, MAX - unDigBig(dst));
         else
            borrow = 0 != num(setDig(dst, -unDigBig(dst)));
      }
   }
Exit:
   if (unDigBig(x) == 0)
      zapZero(y);

   return y;
}

/* Subtract 1 from a (positive) bignum */
static void digSub1(any x) {
   any r, y;
   word borrow;

   ASSERT(isBig(x));

   r = NULL;
#ifdef __LP64__
   borrow = MAX   == num(setDig(x, unDigBig(x) - BIG(1)));
#else
   borrow = MAX-1 == num(setDig(x, unDigBig(x) - BIG(1)));
#endif
   while (isNum(x = cdr(numCell(y = x)))) {
      if (!borrow)
         return;
      borrow = MAX == num(setDig(x, unDigBig(x) - 1));
      r = y;
   }
   if (r  &&  unDigBig(y) == 0)
      cdr(numCell(r)) = x;
}

/* Multiply two (positive) bignums */
static any bigMul(any x1, any x2) {
   any x, y, z;
   word n, carry;
   word2 t;
   cell c1;

   ASSERT(isBig(x1) && isBig(x2));

   Push(c1, x = y = BOX(0));
   for (;;) {
#ifdef __LP64__
      n = unDigBig(x2);
      x2 = nextDigBig(x2);
#else
      n = unDigBig(x2) / num(2);
      if (isNum(x2 = cdr(numCell(x2)))  &&  unDigBig(x2) & 1)
         n |= OVFL;
#endif
      t = (word2)n * unDigBig(z = x1);  // x += n * x1
      carry = (lo(t) > num(setDig(y, unDigBig(y) + lo(t)))) + hi(t);
      while (isNum(z = cdr(numCell(z)))) {
         if (!isNum(cdr(numCell(y))))
            cdr(numCell(y)) = BOX(0);
         y = cdr(numCell(y));
         t = (word2)n * unDigBig(z);
         carry = carry > num(setDig(y, carry + unDigBig(y)));
         if (lo(t) > num(setDig(y, unDigBig(y) + lo(t))))
            ++carry;
         carry += hi(t);
      }
      if (carry)
         cdr(numCell(y)) = BOX(carry);
      if (!isNum(x2))
         break;
      if (!isNum(y = cdr(numCell(x))))
         y = cdr(numCell(x)) = BOX(0);
      x = y;
   } while (isNum(x2));
   zapZero(data(c1));
   return Pop(c1);
}

static inline any MULU(any x, any y) {
   cell c1;
   ASSERT(isNum(x) && isNum(y));

   if (shortLike(x)) {
      word u = unDigShortU(x);
      if (shortLike(y)) {
         word2 t = (word2)u * unDigShortU(y);
         return hi(t) ? boxWord2(t) : boxWord(num(t));
      }
      if (!u)
         return Zero;
      Push(c1, bigCopy(y));
      data(c1) = pos(data(c1));
      if (2 == u) {
         digMul2(data(c1));
         zapZero(data(c1));
      }
      else
         digMul(data(c1), u);
      return Pop(c1);
   }
   if (shortLike(y)) {
      word v = unDigShortU(y);
      if (!v)
         return Zero;
      if (2 == v) {
         digMul2(x);
         zapZero(x);
      }
      else
         digMul(x, v);
      return x;
   }
   return bigMul(x, y);
}

/* Multiply digit with a (positive) bignum */
void digMul(any x, word n) {
   word2 t;
   any y;

   ASSERT(isBig(x));

   t = (word2)n * unDigBig(x);
   for (;;) {
      setDig(x, num(t));
      t = hi(t);
      if (!isNum(x = cdr(numCell(y = x))))
         break;
      t += (word2)n * unDigBig(x);
   }
   if (t)
      cdr(numCell(y)) = BOX(num(t));
}

static any DMUL(any x, word n) {
   ASSERT(isNum(x));

   if (shortLike(x)) {
      word2 t = (word2) unDigShortU(x) * n;
      return hi(t) ? boxWord2(t) : boxWord(num(t));
   }
   return digMul(x, n), x;
}

/* (Positive) Bignum comparison */
static int bigCmp(any x, any y) {
   int res;
   any x1, y1, x2, y2;

   ASSERT(isBig(x) && isBig(y));

   x1 = y1 = Nil;
   for (;;) {
      if ((x2 = cdr(numCell(x))) == (y2 = cdr(numCell(y)))) {
         for (;;) {
            if (unDigBig(x) < unDigBig(y)) {
               res = -1;
               break;
            }
            if (unDigBig(x) > unDigBig(y)) {
               res = +1;
               break;
            }
            if (!isNum(x1))
               return 0;
            x2 = cdr(numCell(x1)),  cdr(numCell(x1)) = x,  x = x1,  x1 = x2;
            y2 = cdr(numCell(y1)),  cdr(numCell(y1)) = y,  y = y1,  y1 = y2;
         }
         break;
      }
      if (!isNum(x2)) {
         res = -1;
         break;
      }
      if (!isNum(y2)) {
         res = +1;
         break;
      }
      cdr(numCell(x)) = x1,  x1 = x,  x = x2;
      cdr(numCell(y)) = y1,  y1 = y,  y = y2;
   }
   while (isNum(x1)) {
      x2 = cdr(numCell(x1)),  cdr(numCell(x1)) = x,  x = x1,  x1 = x2;
      y2 = cdr(numCell(y1)),  cdr(numCell(y1)) = y,  y = y1,  y1 = y2;
   }
   return res;
}

/* Divide two (positive) bignums (Knuth Vol.2, p.257) */
static any bigDiv(any u, any v, bool rem) {
   int m, n, d, i;
   word q, v1, v2, u1, u2, u3, borrow;
   word2 t, r;
   any x, y, z;
   cell c1;

   ASSERT(isBig(u) && isBig(v));

#ifndef __LP64__
   digDiv2(u),  digDiv2(v);                                 // Normalize
#endif
   for (m = 0, z = u;  isNum(y = cdr(numCell(z)));  ++m, z = y);
   x = v,  y = NULL,  n = 1;
   while (isNum(cdr(numCell(x))))
      y = x,  x = cdr(numCell(x)),  ++n,  --m;
   if (m < 0) {
#ifndef __LP64__
      if (rem)
         digMul2(u);
#endif
      return BOX(0);
   }
   cdr(numCell(z)) = BOX(0);
   for (d = 0;  (unDigBig(x) & OVFL) == 0;  ++d)
      digMul2(u),  digMul2(v);
   v1 = unDigBig(x);
   v2 = y? unDigBig(y) : 0;
   Push(c1, Nil);
   do {
      for (i = m, x = u;  --i >= 0;  x = cdr(numCell(x)));  // Index x -> u
      i = n;
      y = x;
      u1 = u2 = 0;
      do
         u3 = u2,  u2 = u1,  u1 = unDigBig(y),  y = cdr(numCell(y));
      while (--i >= 0);

      t = ((word2)u1 << BITS) + u2;                         // Calculate q
      q = u1 == v1? MAX : t / v1;
      r = t - (word2)q*v1;
      while (r <= MAX  &&  (word2)q*v2 > (r << BITS) + u3)
         --q,  r += v1;

      z = x;                                                // x -= q*v
      t = (word2)q * unDigBig(y = v);
      borrow = (MAX - lo(t) < num(setDig(z, unDigBig(z) - lo(t)))) + hi(t);
      while (isNum(y = cdr(numCell(y)))) {
         z = cdr(numCell(z));
         t = (word2)q * unDigBig(y);
         borrow = MAX - borrow < num(setDig(z, unDigBig(z) - borrow));
         if (MAX - lo(t) < num(setDig(z, unDigBig(z) - lo(t))))
            ++borrow;
         borrow += hi(t);
      }
      if (borrow) {
         z = cdr(numCell(z));
         if (MAX - borrow < num(setDig(z, unDigBig(z) - borrow))) {
            word n, carry;                                  // x += v

            --q;
            if (m || rem) {
               y = v;
               carry = unDigBig(y) > num(setDig(x, unDigBig(y) + unDigBig(x)));
               while (x = cdr(numCell(x)),  isNum(y = cdr(numCell(y)))) {
                  if ((n = carry + unDigBig(y)) >= carry) {
                     carry = unDigBig(x) > (n += unDigBig(x));
                     setDig(x,n);
                  }
               }
               setDig(x, carry + unDigBig(x));
            }
         }
      }
      data(c1) = consNum(q, data(c1));                      // Store result
   } while (--m >= 0);
#ifdef __LP64__
   if (!rem)
      zapZero(data(c1));
   else {
      zapZero(u);
      if (d)
         while (d--)
            digDiv2(u);
   }
#else
   if (!rem)
      zapZero(data(c1)),  digMul2(data(c1));
   else {
      zapZero(u);
      if (!d)
         digMul2(u);
      else
         while (--d)
            digDiv2(u);
   }
#endif
   return Pop(c1);
}

/* Compare two numbers */
#if 0
static int bigCompare(any x, any y) {
   ASSERT(isBig(x) && isBig(y));

   if (isNeg(x)) {
      if (!isNeg(y))
         return -1;
      return bigCmp(y,x);
   }
   if (isNeg(y))
      return +1;
   return bigCmp(x,y);
}
#endif

static inline int CMPU(any x, any y) {
   if (shortLike(x)) {
      if (shortLike(y)) {
         word a = num(x) & ~SIGN, b = num(y) & ~SIGN;
         if (a < b)
            return -1;
         else if (b < a)
            return +1;
         return 0;
      }
      return -1;
   }
   if (shortLike(y))
      return +1;
   return bigCmp(x,y);
}

int CMP(any x, any y) {
   if (isNeg(x)) {
      if (!isNeg(y))
         return -1;
      return CMPU(y,x);
   }
   if (isNeg(y))
      return +1;
   return CMPU(x,y);
}

/* Make number from symbol */
any symToNum(any s, int scl, int sep, int ign) {
   unsigned c;
   bool sign, frac;
   cell c1, c2;

   if (!(c = symByte(s)))
      return NULL;
   while (c <= ' ')  /* Skip white space */
      if (!(c = symByte(NULL)))
         return NULL;
   sign = NO;
   if (c == '+'  ||  c == '-' && (sign = YES))
      if (!(c = symByte(NULL)))
         return NULL;
   if ((c -= '0') > 9)
      return NULL;
   frac = NO;
   Push(c1, s);
   Push(c2, BOX(BIG(c)));
   // Push(c2, mkShort(SHORT(c)));
   while ((c = symChar(NULL))  &&  (!frac || scl)) {
      if ((int)c == sep) {
         if (frac) {
            drop(c1);
            return NULL;
         }
         frac = YES;
      }
      else if ((int)c != ign) {
         if ((c -= '0') > 9) {
            drop(c1);
            return NULL;
         }
         data(c2) = DMUL(data(c2), 10);
         data(c2) = DADD(data(c2), c);
         if (frac)
            --scl;
      }
   }
   if (c) {
      if ((c -= '0') > 9) {
         drop(c1);
         return NULL;
      }
      if (c >= 5)
         data(c2) = DADD(data(c2), 1);
      while (c = symByte(NULL)) {
         if ((c -= '0') > 9) {
            drop(c1);
            return NULL;
         }
      }
   }
   if (frac)
      while (--scl >= 0)
         data(c2) = DMUL(data(c2), 10);
   if (sign && !IsZero(data(c2)))
      data(c2) = NEG(data(c2));
   drop(c1);
   return shorten(data(c2));
}

#ifdef __LP64__
#define NINES ((word)999999999999999999ULL)
#define NUM9S 18
#else
#define NINES ((word)999999999UL)
#define NUM9S  9
#endif

/* Buffer size calculation */
#ifdef __LP64__
static inline int numlen(any x) {
   int n = NUM9S+2;
   while (isNum(x = nextDig(x)))
      n += NUM9S+2;
   return (n + NUM9S-1) / NUM9S;
}
#else
static inline int numlen(any x) {
   int n = NUM9S+1;
   while (isNum(x = nextDig(x)))
      n += NUM9S+1;
   return (n + NUM9S-1) / NUM9S;
}
#endif

/* Make symbol from number */
any numToSym(any x, int scl, int sep, int ign) {
   int i;
   bool sign;
   cell c1;
   word n = numlen(x);
   word c, *p, *q, *ta, *ti, acc[n], inc[n];
   char *b, buf[NUM9S+1];

   sign = isNeg(x);
   *(ta = acc) = 0;
   *(ti = inc) = 1;
   n = shortLike(x)? SHORT(1) : BIG(1);
   for (;;) {
      do {
         if (unDig(x) & n) {
            c = 0,  p = acc,  q = inc;
            do {
               if (ta < p)
                  *++ta = 0;
               if (c = (*p += *q + c) > NINES)
                  *p -= (NINES + 1);
            } while (++p, ++q <= ti);
            if (c)
               *p = 1,  ++ta;
         }
         c = 0,  q = inc;
         do
            if (c = (*q += *q + c) > NINES)
               *q -= (NINES + 1);
         while (++q <= ti);
         if (c)
            *q = 1,  ++ti;
      } while (n <<= 1);
      if (!isNum(x = nextDig(x)))
         break;
      n = 1;
   }
   n = (ta - acc) * NUM9S;
   n += sprintf(b = buf, "%ld", *ta--);
   if (sep < 0)
      return boxCnt(n + sign);
   i = -8,  Push(c1, x = BOX(0));
   if (sign)
      byteSym('-', &i, &x);
   if ((scl = n - scl - 1) < 0) {
      byteSym('0', &i, &x);
      charSym(sep, &i, &x);
      while (scl < -1)
         byteSym('0', &i, &x),  ++scl;
   }
   for (;;) {
      byteSym(*b++, &i, &x);
      if (!*b) {
         if (ta < acc)
            return consStr(Pop(c1));
         sprintf(b = buf, "%0*ld", NUM9S, *ta--);
      }
      if (scl == 0)
         charSym(sep, &i, &x);
      else if (ign  &&  scl > 0  &&  scl % 3 == 0)
         charSym(ign, &i, &x);
      --scl;
   }
}

#define DMAX ((double)((word2)MASK+1))

/* Make number from double */
any doubleToNum(double d) {
   bool sign;
   any x;
   cell c1;

   if (isnan(d) || isinf(d) < 0)
      return Nil;
   if (isinf(d) > 0)
      return T;
   sign = NO;
   if (d < 0.0)
      sign = YES,  d = -d;
   d += 0.5;
   Push(c1, x = BOX((word)fmod(d,DMAX)));
   while (d > DMAX)
      x = cdr(numCell(x)) = BOX((word)fmod(d /= DMAX, DMAX));
#ifndef __LP64__
   digMul2(data(c1));
#endif
   if (sign && !IsZeroBig(data(c1)))
      data(c1) = neg(data(c1));
   return shorten(Pop(c1));
}

/* Make double from number */
double numToDouble(any x) {
   double d, m;
   bool sign;

   sign = isNeg(x);
   d = (double)(unDigU(x)),  m = DMAX/2.0;
   while (isNum(x = nextDig(x)))
      d += m * (double)unDig(x),  m *= DMAX;
   return sign? -d : d;
}

// (format 'num ['cnt ['sym1 ['sym2]]]) -> sym
// (format 'sym|lst ['cnt ['sym1 ['sym2]]]) -> num
any doFormat(any ex) {
   int scl, sep, ign;
   any x, y;
   cell c1;

   x = cdr(ex),  Push(c1, EVAL(car(x)));
   x = cdr(x),  y = EVAL(car(x));
   scl = isNil(y)? 0 : xCnt(ex, y);
   sep = '.';
   ign = 0;
   if (isCell(x = cdr(x))) {
      y = EVAL(car(x));
      NeedSym(ex,y);
      sep = symChar(name(y));
      if (isCell(x = cdr(x))) {
         y = EVAL(car(x));
         NeedSym(ex,y);
         ign = symChar(name(y));
      }
   }
   if (isNum(data(c1)))
      data(c1) = numToSym(data(c1), scl, sep, ign);
   else {
      int i;
      any nm;
      cell c2;

      if (isSym(data(c1)))
         nm = name(data(c1));
      else {
         nm = NULL,  pack(data(c1), &i, &nm, &c2);
         nm = nm? data(c2) : Nil;
      }
      data(c1) = symToNum(nm, scl, sep, ign) ?: Nil;
   }
   return Pop(c1);
}

static inline any INC(any x) {
   ASSERT(isNum(x));
   if (shortLike(x)) {
      if (isNeg(x)) {
         x = (any)(num(x) - ShortOne);
         // 00..01SN.r
         if (num(x) <= (NORM+1+T_SHORTNUM))
           x = (any)(num(x) ^ SIGN);
         return x;
      }
      if ((num(x) & ~NORM) == ShortMax)
         return BOX(BIG((ShortMax >> (1+NORMBITS)) + 1));
      return (any)(num(x) + ShortOne);
   }
   if (!isNeg(x))
      return digAdd(x, BIG(1)), x;
   x = pos(x), digSub1(x);
   if (!IsZeroBig(x)) {
      x = shorten(neg(x));
   }
   else
      x = Zero;
   return x;
}

any DEC(any x) {
   ASSERT(isNum(x));

   if (shortLike(x)) {
      if (num(x) & SIGN) {
         if ((num(x) & ~(SIGN+NORM)) == ShortMax)
            return neg(BOX(BIG((ShortMax >> (1+NORMBITS)) + 1)));
         return (any)(num(x) + ShortOne);
      }
      if (x == Zero)
         return mkShort(3);
      return (any)(num(x) - ShortOne);
   }
   if (isNeg(x))
      return digAdd(x, BIG(1)), x;
   else if (IsZero(x))
      return negShort(mkShort(SHORT(1)));
   return digSub1(x), shorten(x);
}

static inline any ABS(any x) {
   ASSERT(isNum(x));
   return shortLike(x)? posShort(x) : pos(x);
}

static inline any NEG(any x) {
   ASSERT(isNum(x));
   return shortLike(x)? negShort(x) : neg(x);
}

static inline any ADDU(any x, any y) {
   cell c1;

   ASSERT(isNum(x) && isNum(y));
   if (shortLike(x)) {
      if (shortLike(y)) {
         word a = num(x) & ~SIGN, b = num(y) & ~(SIGN+NORM), c;
#ifdef __LP64__
         if ((c = a + b) < a) {
#else
         if (__builtin_uaddl_overflow(a, b, &c)) {
#endif
            return BOX(BIG((a >> (1+NORMBITS)) + (b >> (1+NORMBITS))));
         }
         return (any)c;
      }
      Push(c1, bigCopy(y));
      data(c1) = pos(data(c1));
      digAdd(data(c1), BIG(unDigShortU(x)));
      return Pop(c1);
   }
   if (shortLike(y)) {
      // x may be negative
      x = pos(x);
      return digAdd(x, BIG(unDigShortU(y))), x;
   }
   return x = pos(x), bigAdd(x, y), x;
}

static inline any SUBU(any x, any y) {
   cell c1;

   ASSERT(isNum(x) && isNum(y));
   if (shortLike(x)) {
      if (shortLike(y)) {
         word a = num(x) & ~(SIGN+NORM), b = num(y) & ~(SIGN+NORM);
         if (a >= b)
            return (any)(a - b + T_SHORTNUM);
         return (any)(b - a + T_SHORTNUM + SIGN);
      }
      Push(c1, big(x));
      data(c1) = bigSub(data(c1), y);
      data(c1) = shorten(data(c1));
      return Pop(c1);
   }
   if (shortLike(y)) {
      Push(c1, big(posShort(y)));
      x = bigSub(x, data(c1));
      drop(c1);
      return shorten(x);
   }
   // x may be negative
   x = bigSub(x, y);
   return shorten(x);
}

static inline any DIVU2(any x) {
   ASSERT(isNum(x));

   if (shortLike(x)) {
      word a = unDigShort(x) / 4;
      return mkShort(2 * a);
   }
   return digDiv2(x), shorten(x);
}

static inline any MULU2(any x) {
   ASSERT(isNum(x));

   if (shortLike(x)) {
      word a = 2 * unDigShortU(x);
      return boxWord(a);
   }
   return digMul2(x), x;
}

static inline any DIVREMU(any x, any y, bool rem) {
   any z;
   cell c1;
   word a, b;
   ASSERT(isNum(x) && isNum(y));

   if (shortLike(x)) {
      a = unDigShortU(x);
      if (shortLike(y)) {
         b = unDigShortU(y);
         return mkShort(2 * (rem ? a % b : a / b));
      }
      if (isNum(nextDigBig(y))) {
         return rem ? x : Zero;
      }
      Push(c1, BOX(BIG(a)));
      z = bigDiv(data(c1), y, rem);
      drop(c1);
      return shorten(rem ? data(c1) : z);
   }
   if (shortLike(y)) {
      Push(c1, big(posShort(y)));
      z = bigDiv(x, data(c1), rem);
      drop(c1);
      return shorten(rem ? x : z);
   }
   z = bigDiv(x, y, rem);
   return shorten(rem ? x : z);
}

any ADD(any x, any y) {
   ASSERT(isNum(x) && isNum(y));

   if (isNeg(x)) {
      if (isNeg(y))
         x = ADDU(x,y);
      else
         x = SUBU(x,y);
      if (!IsZero(x))
         x = NEG(x);
   }
   else if (isNeg(y))
      x = SUBU(x,y);
   else
      x = ADDU(x,y);
   return x;
}

any SUB(any x, any y) {
   ASSERT(isNum(x) && isNum(y));

   if (isNeg(x)) {
      if (isNeg(y))
         x = SUBU(x,y);
      else
         x = ADDU(x,y);
      if (!IsZero(x))
         x = NEG(x);
   }
   else if (isNeg(y))
      x = ADDU(x,y);
   else
      x = SUBU(x,y);
   return x;
}

// (+ 'num ..) -> num
any doAdd(any ex) {
   any x;
   cell c1, c2;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   while (isCell(x = cdr(x))) {
      Push(c2, EVAL(car(x)));
      if (isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      data(c1) = ADD(data(c1),data(c2));
      drop(c2);
   }
   return Pop(c1);
}

// (- 'num ..) -> num
any doSub(any ex) {
   any x;
   cell c1, c2;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   if (!isCell(x = cdr(x))) {
      if (IsZero(data(c1)))
         return data(c1);
      if (shortLike(data(c1)))
         return negShort(data(c1));
      // share struct
#ifdef __LP64__
      return neg(data(c1));
#else
      return consNum(negDig(unDigBig(data(c1))), cdr(numCell(data(c1))));
#endif
   }
   Push(c1, CPY(data(c1)));
   do {
      Push(c2, EVAL(car(x)));
      if (isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      data(c1) = SUB(data(c1),data(c2));
      drop(c2);
   } while (isCell(x = cdr(x)));
   return Pop(c1);
}

// (inc 'num) -> num
// (inc 'var ['num]) -> num
any doInc(any ex) {
   any x;
   cell c1, c2;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   if (isNum(data(c1))) {
      Push(c1, CPY(data(c1)));
      data(c1) = INC(data(c1));
      return Pop(c1);
   }
   CheckVar(ex,data(c1));
   if (isSym(data(c1)))
      Touch(ex,data(c1));
   if (!isCell(x = cdr(x))) {
      if (isNil(val(data(c1))))
         return Nil;
      NeedNum(ex,val(data(c1)));
      Save(c1);
      val(data(c1)) = CPY(val(data(c1)));
      val(data(c1)) = INC(val(data(c1)));
   }
   else {
      Save(c1);
      Push(c2, EVAL(car(x)));
      if (isNil(val(data(c1))) || isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,val(data(c1)));
      NeedNum(ex,data(c2));
      val(data(c1)) = CPY(val(data(c1)));
      val(data(c1)) = ADD(val(data(c1)), data(c2));
   }
   return val(Pop(c1));
}

// (dec 'num) -> num
// (dec 'var ['num]) -> num
any doDec(any ex) {
   any x;
   cell c1, c2;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   if (isNum(data(c1))) {
      Push(c1, CPY(data(c1)));
      data(c1) = DEC(data(c1));
      return Pop(c1);
   }
   CheckVar(ex,data(c1));
   if (isSym(data(c1)))
      Touch(ex,data(c1));
   if (!isCell(x = cdr(x))) {
      if (isNil(val(data(c1))))
         return Nil;
      NeedNum(ex,val(data(c1)));
      Save(c1);
      val(data(c1)) = CPY(val(data(c1)));
      val(data(c1)) = DEC(val(data(c1)));
   }
   else {
      Save(c1);
      Push(c2, EVAL(car(x)));
      if (isNil(val(data(c1))) || isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,val(data(c1)));
      NeedNum(ex,data(c2));
      val(data(c1)) = CPY(val(data(c1)));
      val(data(c1)) = SUB(val(data(c1)),data(c2));
   }
   return val(Pop(c1));
}

// (* 'num ..) -> num
any doMul(any ex) {
   any x;
   bool sign;
   cell c1, c2;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   if ((sign = isNeg(data(c1))))
      data(c1) = ABS(data(c1));
   while (isCell(x = cdr(x))) {
      Push(c2, EVAL(car(x)));
      if (isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      sign ^= isNeg(data(c2));
      data(c1) = MULU(data(c1), data(c2));
      drop(c2);
   }
   if (sign && !IsZero(data(c1)))
      data(c1) = NEG(data(c1));
   return Pop(c1);
}

// (*/ 'num1 ['num2 ..] 'num3) -> num
any doMulDiv(any ex) {
   any x;
   bool sign;
   cell c1, c2, c3;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   if ((sign = isNeg(data(c1))))
      data(c1) = ABS(data(c1));
   Push(c2, Nil);
   for (;;) {
      x = cdr(x),  data(c2) = EVAL(car(x));
      if (isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      sign ^= isNeg(data(c2));
      if (!isCell(cdr(x)))
         break;
      data(c1) = MULU(data(c1), data(c2));
   }
   if (IsZero(data(c2)))
      divErr(ex);
   Push(c3, CPY(data(c2)));
   data(c3) = DIVU2(data(c3));
   data(c1) = ADDU(data(c1),data(c3));
   data(c2) = CPY(data(c2));
   data(c1) = DIVREMU(data(c1),data(c2),NO);
   if (sign && !IsZero(data(c1)))
      data(c1) = NEG(data(c1));
   return Pop(c1);
}

// (/ 'num ..) -> num
any doDiv(any ex) {
   any x;
   bool sign;
   cell c1, c2;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   if ((sign = isNeg(data(c1))))
      data(c1) = ABS(data(c1));
   while (isCell(x = cdr(x))) {
      Push(c2, EVAL(car(x)));
      if (isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      sign ^= isNeg(data(c2));
      if (IsZero(data(c2)))
         divErr(ex);
      data(c2) = CPY(data(c2)); 
      data(c1) = DIVREMU(data(c1),data(c2),NO);
      drop(c2);
   }
   if (sign && !IsZero(data(c1)))
      data(c1) = NEG(data(c1));
   return Pop(c1);
}

#ifdef __GNUC__
#define bitCount(x)   __builtin_popcount(x)
#endif

#ifndef bitCount
int bitCount(word x) {
   int result;

   result = 0;
   while (x) {
      if (x & 1) result++;
      x >>= 1;
   }
   return result;
}
#endif

// (% 'num ..) -> num
any doRem(any ex) {
   any x;
   bool sign;
   cell c1, c2;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   if ((sign = isNeg(data(c1))))
      data(c1) = ABS(data(c1));
   while (isCell(x = cdr(x))) {
      Push(c2, EVAL(car(x)));
      if (isNil(data(c2))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      if (IsZero(data(c2)))
         divErr(ex);
      data(c2) = CPY(data(c2));
      data(c1) = DIVREMU(data(c1),data(c2),YES);
      drop(c2);
   }
   if (sign && !IsZero(data(c1)))
      data(c1) = NEG(data(c1));
   return Pop(c1);
}

// (>> 'cnt 'num) -> num
any doShift(any ex) {
   any x;
   long n;
   bool sign;
   cell c1;

   x = cdr(ex),  n = evCnt(ex,x);
   x = cdr(x);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   sign = isNeg(data(c1));
   if (n > 0) {
      do
         data(c1) = DIVU2(data(c1));
      while (--n);
      if (shortLike(data(c1))) {
         data(c1) = ABS(data(c1));
      }
#ifndef __LP64__
      else // clear LSB
         setDig(data(c1), posDig(unDigBig(data(c1))));
#endif
   }
   else if (n < 0) {
      data(c1) = ABS(data(c1));
      do
         data(c1) = MULU2(data(c1));
      while (++n);
   }
   if (sign && !IsZero(data(c1)))
      data(c1) = NEG(data(c1));
   return Pop(c1);
}

// (lt0 'any) -> num | NIL
any doLt0(any x) {
   x = cdr(x);
   return isNum(x = EVAL(car(x))) && isNeg(x)? x : Nil;
}

// (le0 'any) -> num | NIL
any doLe0(any x) {
   x = cdr(x);
   return isNum(x = EVAL(car(x))) && (isNeg(x) || IsZero(x))? x : Nil;
}

// (ge0 'any) -> num | NIL
any doGe0(any x) {
   x = cdr(x);
   return isNum(x = EVAL(car(x))) && !isNeg(x)? x : Nil;
}

// (gt0 'any) -> num | NIL
any doGt0(any x) {
   x = cdr(x);
   return isNum(x = EVAL(car(x))) && !isNeg(x) && !IsZero(x)? x : Nil;
}

// (abs 'num) -> num
any doAbs(any ex) {
   any x;

   x = cdr(ex);
   if (isNil(x = EVAL(car(x))))
      return Nil;
   NeedNum(ex,x);
   if (!isNeg(x))
      return x;
   if (shortLike(x))
      return posShort(x);
#ifdef __LP64__
   return pos(x);
#else
   return consNum(posDig(unDigBig(x)), cdr(numCell(x))); // share struct
#endif
}

// (bit? 'num ..) -> num | NIL
any doBitQ(any ex) {
   any x, y, z;
   cell c1;
   int short1;
   word u1;

   x = cdr(ex),  Push(c1, EVAL(car(x)));
   NeedNum(ex,data(c1));
   if (isNeg(data(c1))) {
      if (shortLike(data(c1))) {
         data(c1) = posShort(data(c1));
      }
      else
#ifdef __LP64__
         data(c1) = pos(data(c1));
#else
         data(c1) = consNum(posDig(unDigBig(data(c1))), cdr(numCell(data(c1))));
#endif
   }
   if ((short1 = shortLike(data(c1))))
      u1 = unDigShortU(data(c1));
   while (isCell(x = cdr(x))) {
      if (isNil(z = EVAL(car(x)))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,z);
      y = data(c1);
      if (short1) {
         if ((u1 & unDigU(z)) != u1) {
            drop(c1);
            return Nil;
         }
      }
      else {
         z = big(z);
         if ((unDigBig(y) & POSDIG(unDigBig(z))) != unDigBig(y)) {
            drop(c1);
            return Nil;
         }
         for (;;) {
            if (!isNum(y = nextDigBig(y)))
               break;
            if (!isNum(z = nextDigBig(z))) {
               drop(c1);
               return Nil;
            }
            if ((unDigBig(y) & unDigBig(z)) != unDigBig(y)) {
               drop(c1);
               return Nil;
            }
         }
      }
   }
   return Pop(c1);
}

// (& 'num ..) -> num
any doBitAnd(any ex) {
   any x, y, z;
   cell c1;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   data(c1) = ABS(data(c1));
   while (isCell(x = cdr(x))) {
      if (isNil(z = EVAL(car(x)))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,z);
      y = data(c1);
      if (shortLike(y) && shortLike(z))
         data(c1) = y = (any)(num(y) & num(z));
      else {
         data(c1) = y = big(data(c1)); z = big(z);
         setDig(y, unDigBig(y) & unDigBig(z));
         for (;;) {
            if (!isNum(z = nextDigBig(z))) {
               cdr(numCell(y)) = Nil;
               break;
            }
            if (!isNum(y = nextDigBig(y)))
               break;
            setDig(y, unDigBig(y) & unDigBig(z));
         }
      }
   }
   if (isBig(data(c1))) {
      zapZero(data(c1));
      data(c1) = shorten(data(c1));
   }
   return Pop(c1);
}

// (| 'num ..) -> num
any doBitOr(any ex) {
   any x, y, z;
   cell c1, c2;
   int n;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   data(c1) = ABS(data(c1));
   n = length(x) - 1;
   while (isCell(x = cdr(x))) {
      if (isNil(data(c2) = EVAL(car(x)))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      y = data(c1);
      Save(c2);
      if (shortLike(data(c1)) && shortLike(data(c2)))
         data(c1) = y = (any)(num(y) | num(data(c2)) & ~SIGN);
      else {
         y = data(c1) = big(data(c1)), data(c2) = big(data(c2));
         setDig(y, unDigBig(y) | POSDIG(unDigBig(data(c2))));
         for (;;) {
            if (!isNum(data(c2) = nextDigBig(data(c2))))
               break;
            z = nextDigBig(y);
            if (!isNum(z)) {
               if (1 == n) { // share struct
                  cdr(numCell(y)) = data(c2);
                  break;
               }
               cdr(numCell(y)) = z = BOX(unDigBig(data(c2)));
               y = z;
            }
            else {
               y = z;
               setDig(y, unDigBig(y) | unDigBig(data(c2)));
            }
         }
      }
      drop(c2);
   }
   return Pop(c1);
}

// (x| 'num ..) -> num
any doBitXor(any ex) {
   any x, y, z;
   cell c1, c2;
   int n;

   x = cdr(ex);
   if (isNil(data(c1) = EVAL(car(x))))
      return Nil;
   NeedNum(ex,data(c1));
   Push(c1, CPY(data(c1)));
   data(c1) = ABS(data(c1));
   n = length(x) - 1;
   while (isCell(x = cdr(x))) {
      if (isNil(data(c2) = EVAL(car(x)))) {
         drop(c1);
         return Nil;
      }
      NeedNum(ex,data(c2));
      y = data(c1);
      Save(c2);
      if (shortLike(data(c1)) && shortLike(data(c2)))
         data(c1) = y = (any)((num(y) ^ num(data(c2)) & ~SIGN) + T_SHORTNUM);
      else {
         y = data(c1) = big(data(c1)), data(c2) = big(data(c2));
         setDig(y, unDigBig(y) ^ POSDIG(unDigBig(data(c2))));
         for (;;) {
            if (!isNum(data(c2) = nextDigBig(data(c2))))
               break;
            z = nextDigBig(y);
            if (!isNum(z)) {
               if (1 == n) { // share struct
                  cdr(numCell(y)) = data(c2);
                  break;
               }
               cdr(numCell(y)) = z = BOX(unDigBig(data(c2)));
               y = z;
            }
            else {
               y = z;
               setDig(y, unDigBig(y) ^ unDigBig(data(c2)));
            }
         }
      }
      drop(c2);
   }
   if (isBig(data(c1))) {
      zapZero(data(c1));
      data(c1) = shorten(data(c1));
   }
   return Pop(c1);
}

// (sqrt 'num ['flg|num]) -> num
any doSqrt(any ex) {
   any x, y, z;
   cell c1, c2, c3, c4, c5;

   x = cdr(ex);
   if (isNil(x = EVAL(car(x))))
      return Nil;
   NeedNum(ex,x);
   if (isNeg(x))
      argError(ex, x);

   Push(c1, x);  // num
   y = cddr(ex);
   Push(c2, y = EVAL(car(y)));  // flg|num
   if (isNum(y)) {
      // CPY is necessary, because MULU modifies the first arg
      data(c1) = CPY(x);
      x = data(c1) = MULU(data(c1), y);
   }

   if (shortLike(x)) {
      word u = unDigShortU(x);
#ifdef __LP64__
      if (BITS - __builtin_clz(u) < 53) {
         drop(c1);
         return boxWord(sqrt(u) + (isNil(y) ? 0.0 : 0.5));
      }
#else
      drop(c1);
      return boxWord(sqrt(u) + (isNil(y) ? 0.0 : 0.5));
#endif
   }
   x = data(c1) = big(x), y = data(c2) = isNum(y) ? big(y) : y;

   Push(c3, y = BOX(unDigBig(x)));  // Number copy
   Push(c4, z = BOX(BIG(1)));  // Mask
   while (isNum(x = cdr(numCell(x)))) {
      y = cdr(numCell(y)) = BOX(unDigBig(x));
      data(c4) = consNum(0, data(c4));
   }
   while (unDigBig(y) >= unDigBig(z))
      if (!setDig(z, unDigBig(z) << 2)) {
         z = cdr(numCell(z)) = BOX(BIG(1));
         break;
      }
   Push(c5, BOX(0));  // Result
   do {
      bigAdd(data(c5),data(c4));
      if (bigCmp(data(c5),data(c3)) > 0)
         data(c5) = bigSub(data(c5),data(c4));
      else
         data(c3) = bigSub(data(c3),data(c5)),  bigAdd(data(c5),data(c4));
      digDiv2(data(c5));
      digDiv2(data(c4)),  digDiv2(data(c4));
   } while (!IsZeroBig(data(c4)));
   if (!isNil(data(c2)) && bigCmp(data(c3),data(c5)) > 0)
      digAdd(data(c5), BIG(1));
   drop(c1);
   return shorten(data(c5));
}

/* Random numbers */
static word2 Seed;

static uint64_t initSeed(any x) {
   uint64_t n;

   for (n = 0; isCell(x); x = cdr(x))
      n += initSeed(car(x));
   if (!isNil(x)) {
      if (isSym(x))
         x = name(x);
      do
         n += unDig(x);
      while (isNum(x = nextDig(x)));
   }
   return n;
}

// (seed 'any) -> cnt
any doSeed(any ex) {
#ifdef __LP64__
   Seed = (word2)initSeed(EVAL(cadr(ex))) * 6364136223846793005ULL;
   return box(hi64(lo(Seed)));
#else
   return box(hi64(Seed = initSeed(EVAL(cadr(ex))) * 6364136223846793005ULL));
#endif
}

// (hash 'any) -> cnt
any doHash(any ex) {
   uint64_t n = initSeed(EVAL(cadr(ex)));
   int i = 64;
   int j = 0;

   do {
      if (((long)n ^ j) & 1)
         j ^= 0x14002;  /* CRC Polynom x**16 + x**15 + x**2 + 1 */
      n >>= 1,  j >>= 1;
   } while (--i);
   return box(2 * (j + 1));
}

// (rand ['cnt1 'cnt2] | ['T]) -> cnt | flg
any doRand(any ex) {
   any x;
   long n, m;

   x = cdr(ex);
#ifdef __LP64__
   Seed = (word2)lo(Seed) * 6364136223846793005ULL + 1;
   if (isNil(x = EVAL(car(x))))
      return box(hi64(lo(Seed)));
   if (x == T)
      return hi64(lo(Seed)) & 1 ? T : Nil;
   n = xCnt(ex,x);
   if (m = evCnt(ex, cddr(ex)) + 1 - n)
      n += ((hi(Seed)<<BITS32) | (lo(Seed)>>BITS32)) % m;
#else
   Seed = Seed * 6364136223846793005ULL + 1;
   if (isNil(x = EVAL(car(x))))
      return box(hi64(Seed));
   if (x == T)
      return hi64(Seed) & 1 ? T : Nil;
   n = xCnt(ex,x);
   if (m = evCnt(ex, cddr(ex)) + 1 - n)
      n += hi64(Seed) % m;
#endif
   return boxCnt(n);
}
