/* 01may14abu
 * (c) Software Lab. Alexander Burger
 */

#include "pico.h"

/* Mark data */
static void mark(any x) {
   cell *p;

   if (isShort(x)) // short number
      return;
   while (num((p = cellPtr(x))->cdr) & 1) {
      *(word*)&cdr(p) &= ~1;
      if (!isNum(x))
         mark(p->car);
      if (isNsp(x)) { // namespace
         any *q = ptrNsp(x);
         int i;
// fprintf(stderr,"*** mark ns %p\n",q);
         for (i = 0; i < IHASH; i++)
            mark(q[i]);
      }
      x = p->cdr;
      if (isShort(x))
         break;
   }
}

static inline void markEnv(stkEnv *env) {
   any p;
   int i;

   mark(env->nsp); // mark current ns
   for (p = (any)env->applyFrames;  p;  p = (any)((applyFrame*)p)->link) {
      applyFrame *f = (applyFrame*)p;
      mark(f->body);
      mark(f->args);
   }
   mark(env->exe);
   for (p = env->stack; p; p = cdr(p))
      mark(car(p));
   for (p = (any)env->bind;  p;  p = (any)((bindFrame*)p)->link) {
      bindFrame *f = (bindFrame*)p;
      mark(f->exe);
      for (i = f->cnt;  --i >= 0;) {
         mark(f->bnd[i].sym);
         mark(f->bnd[i].val);
      }
   }
}

static inline void markCatch(catchFrame *catchPtr) {
   any p;

   for (p = (any)catchPtr; p; p = (any)((catchFrame*)p)->link) {
      catchFrame *f = (catchFrame*)p;
      if (f->tag)
         mark(f->tag);
      mark(f->fin);
      mark(f->env.nsp); // mark saved ns
   }
}


static long GcCount = CELLS;
static long NumGc = 0;

/* Garbage collector */
void gc(long c) {
   any p, *pp, x;
   heap *h;
   int i;

// XXX outString("=== gc ==="); flushAll();

   NumGc++;
   val(DB) = Nil;
   h = Heaps;
   do {
      p = h->cells + CELLS-1;
      do
         *(word*)&cdr(p) |= 1;
      while (--p >= h->cells);
   } while (h = h->next);

// XXX outString("*** heaps "); flushAll(); outNum(mkShort(2*nheaps)); newline();
   /* Mark */
   mark(Nil+1);
   mark(Alarm),  mark(Sigio),  mark(Line),  mark(Zero),  mark(One);
   mark(TNsp);
   mark(Pico1); // mark initial ns
   for (i = 0; i < NCBL; i++) // mark callbacks
      mark(Lisp[i].tag), mark(Lisp[i].fun);
   for (i = 0; i < IHASH; ++i)
      mark(Transient[i]);
   markEnv(&Env); // mark current env
   markCatch(CatchPtr);
   for (i = 0; Stack1[i]; i++) {
      coFrame *f = Stack1[i];
      if (Env.coF != f) // skip running coro
         if (!isNil(f->tag)) { // used?
            mark(f->tag);
            mark(f->ret);
            mark(f->At);
            if (!f->active) { // not active?
               markEnv(&(f->env));
               markCatch(f->CatchPtr);
            }
         }
   }
   for (i = 0; i < EHASH; ++i)
      for (p = Extern[i];  isCell(p);  p = (any)(num(p->cdr) & ~1))
         if (num(val(p->car)) & 1) {
            for (x = tail1(p->car); !isSym(x); x = cdr(cellPtr(x)));
            if ((x = (any)(num(x) & ~1)) == At2  ||  x == At3)
               mark(p->car);  // Keep if dirty or deleted
         }
   if (num(val(val(DB) = DbVal)) & 1) {
      val(DbVal) = cdr(numCell(DbTail)) = Nil;
      tail(DbVal) = ext(DbTail);
   }
   for (i = 0; i < EHASH; ++i)
      for (pp = Extern + i;  isCell(p = *pp);)
         if (num(val(p->car)) & 1)
            *pp = (cell*)(num(p->cdr) & ~1);
         else
            *(word*)(pp = &cdr(p)) &= ~1;
   /* Clean up */
   for (i = 0; Stack1[i]; i++) {
      coFrame *f = Stack1[i];
      any tag = f->tag;
      if (!isNil(tag)) {
         if (num(tag) & 1)
            f->tag = Nil, Stacks--;
         else {
            // pil64: clear ApplyStack (builds the ApplyFrame on the stack)
            ;
         }
      }
   }
   // pil64: clear ApplyStack (builds the ApplyFrame on the stack)
   *(word*)&cdr(Pico1) &= ~1;
   /* Sweep */
   Avail = NULL;
   h = Heaps;
   if (c) {
      do {
         p = h->cells + CELLS-1;
         do
            if (num(p->cdr) & 1)
               FreeTyped(p),  --c;
         while (--p >= h->cells);
      } while (h = h->next);
      while (c >= 0)
         heapAlloc(),  c -= CELLS;
   }
   else {
      heap **hp = &Heaps;
      cell *av;

      do {
         c = GcCount? GcCount : CELLS;
         av = Avail;
         p = h->cells + CELLS-1;
         do
            if (num(p->cdr) & 1)
               FreeTyped(p),  --c;
         while (--p >= h->cells);
         if (c)
            hp = &h->next,  h = h->next;
         else
            Avail = av,  h = h->next,  free(*hp),  *hp = h;
      } while (h);
   }
}

// (gc ['cnt ['cnt2]]) -> cnt | NIL
any doGc(any ex) {
   any x, cnt, cnt2;

   x = cdr(ex),  cnt = EVAL(car(x));
   val(At) = val(At2) = Nil;
   gc(isNum(cnt)? CELLS*unBox(cnt) : GcCount);
   if (isCell(x = cdr(x))) {
      cnt2 = EVAL(car(x));
      NeedCnt(ex,cnt2);
      GcCount = CELLS*unBox(cnt2);
   }
   else
      GcCount = CELLS;
   return cnt;
}

// (gccount) -> cnt
any doGcCount(any x) {
   long val = NumGc;
   return NumGc = 0, boxCnt(val);
}

static long Consed = 0;

// (consed) -> cnt
any doConsed(any x) {
  long val = Consed;
  return Consed = 0, boxCnt(val);
}

/* Construct a cell */
any cons(any x, any y) {
   cell *p;

   Consed++;
   if (!(p = Avail)) {
      cell c1, c2;

      Push(c1,x);
      Push(c2,y);
      gc(GcCount);
      drop(c1);
      p = Avail;
   }
// XXX if (x == TNsp) fprintf(stderr,"*** cons\n");
   Avail = p->car;
   p->car = x;
   p->cdr = y;
   return p;
}

/* Construct a symbol */
any consSym(any v, any x) {
   cell *p;

   ASSERT(isNil(x) || isNum(x));
   Consed++;
   if (!(p = Avail)) {
      cell c1, c2;

      Push(c1,v);
      Push(c2,x);
      gc(GcCount);
      drop(c1);
      p = Avail;
   }
   Avail = p->car;
   p = symPtr(p);
   tail(p) = x;
   val(p) = v;
   return p;
}

/* Construct a string */
any consStr(any x) {
   cell *p;

   ASSERT(isNum(x));
   Consed++;
   if (!(p = Avail)) {
      cell c1;

      Push(c1,x);
      gc(GcCount);
      drop(c1);
      p = Avail;
   }
   Avail = p->car;
   p = symPtr(p);
   tail(p) = x;
   val(p) = p;
   return p;
}

/* Construct a number cell */
any consNum(word n, any x) {
   cell *p;

   Consed++;
   if (!(p = Avail)) {
      cell c1;

      Push(c1,x);
      gc(GcCount);
      drop(c1);
      p = Avail;
   }
   Avail = p->car;
   p->car = (any)n;
   p->cdr = x;
   return numPtr(p);
}

/* Construct a namespace */
any consNsp(void) {
   any x, *p = NULL;
   int i;
   word u;

   p = (any*)allocAligned(p,IHASH*sizeof(any),1<<NORMBITS);
   for (i = 0; i < IHASH; i++)
      p[i] = Nil;
   u = num(p);
#ifndef __LP64__
   u >>= NORMBITS;
#endif
   x = cons(TNsp, mkShort(u));
// XXX fprintf(stderr,"*** consNsp %p=(%p,%p) ptr=%p\n",x,TNsp,cdr(x),p);
   return x;
}

