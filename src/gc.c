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

/* Garbage collector */
void gc(long c) {
   any p, *pp, x;
   heap *h;
   int i;

// XXX outString("*** gc ***"); flushAll(); newline();

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
   mark(TNsp), mark(TCo7);
   mark(Pico1),  mark(Env.nsp); // mark initial/current ns
   for (i = 0; i < IHASH; ++i)
      mark(Transient[i]);
   mark(ApplyArgs),  mark(ApplyBody);
   for (p = Env.stack; p; p = cdr(p))
      mark(car(p));
   for (p = (any)Env.bind;  p;  p = (any)((bindFrame*)p)->link)
      for (i = ((bindFrame*)p)->cnt;  --i >= 0;) {
         mark(((bindFrame*)p)->bnd[i].sym);
         mark(((bindFrame*)p)->bnd[i].val);
      }
   for (p = (any)CatchPtr; p; p = (any)((catchFrame*)p)->link) {
      if (((catchFrame*)p)->tag)
         mark(((catchFrame*)p)->tag);
      mark(((catchFrame*)p)->fin);
      mark(((catchFrame*)p)->env.nsp); // mark saved ns
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
         c = CELLS;
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

// (gc ['cnt]) -> cnt | NIL
any doGc(any x) {
   x = cdr(x),  x = EVAL(car(x));
   val(At) = val(At2) = Nil;
   gc(isNum(x)? CELLS*unBox(x) : CELLS);
   return x;
}

/* Construct a cell */
any cons(any x, any y) {
   cell *p;

   if (!(p = Avail)) {
      cell c1, c2;

      Push(c1,x);
      Push(c2,y);
      gc(CELLS);
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
   if (!(p = Avail)) {
      cell c1, c2;

      Push(c1,v);
      Push(c2,x);
      gc(CELLS);
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
   if (!(p = Avail)) {
      cell c1;

      Push(c1,x);
      gc(CELLS);
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

   if (!(p = Avail)) {
      cell c1;

      Push(c1,x);
      gc(CELLS);
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

   p = (any*)alloc(p,IHASH*sizeof(any));
   for (i = 0; i < IHASH; i++)
      p[i] = Nil;
   x = cons(TNsp, box(num(p)));
// XXX fprintf(stderr,"*** consNsp %p=(%p,%p) ptr=%p\n",x,TNsp,cdr(x),p);
   return x;
}

