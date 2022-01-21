# 19jan22 Software Lab. Alexander Burger
# pil maze2.l -maze~main -go +

(load "@lib/simul.l")

(symbols 'maze 'simul 'pico)

(on *Rt)

(local) (*DX *DY *Grid crawl main go)

(setq *DX 10  *DY 22  *Grid (grid *DX *DY))

(de crawl (Start)
   (catch 'stop
      (while
         (with (get *Grid (rand 1 *DX) (rand 1 *DY))
            (unless (or (== Start This) (: co) (: goal))
               (=: goal (co))
               (finally (=: goal NIL)
                  (let Path NIL
                     (recur (This Path)
                        (cond
                           ((== This Start)
                              (=: co (co))
                              (pause 500)
                              This )
                           ((not (memq This Path))
                              (push 'Path This)
                              (when
                                 (or
                                    (and (: west) (recurse @ Path))
                                    (and (: east) (recurse @ Path))
                                    (and (: south) (recurse @ Path))
                                    (and (: north) (recurse @ Path)) )
                                 (put @ 'co NIL)
                                 (when (: co)
                                    (wake @ (throw 'stop)) )
                                 (=: co (co))
                                 (pause 500)
                                 This ) ) ) ) ) )
               (setq Start This) )
            *Next ) ) ) )

(de main ()
   (symbols '(maze simul pico))
   (let Fld (get *Grid (rand 1 *DX) (rand 1 *DY))
      (recur (Fld)
         (for Dir (shuffle '((west . east) (east . west) (south . north) (north . south)))
            (with ((car Dir) Fld)
               (unless (or (: west) (: east) (: south) (: north))
                  (put Fld (car Dir) This)
                  (put This (cdr Dir) Fld)
                  (recurse This) ) ) ) ) )
   (for Col *Grid
      (for This Col
         (set This
            (cons
               (cons (: west) (: east))
               (cons (: south) (: north)) ) ) ) ) )

(de go ()
   (co 'A (crawl 'a1))
   (co 'B (crawl (get *Grid 1 (/ *DY 2))))
   (co 'C (crawl (get *Grid 1 *DY)))
   (co 'D (crawl (get *Grid (/ *DX 2) *DY)))
   (co 'E (crawl (get *Grid *DX *DY)))
   (co 'F (crawl (get *Grid *DX (/ *DY 2))))
   (co 'G (crawl (get *Grid *DX 1)))
   (co 'H (crawl (get *Grid (/ *DX 2) 1)))
   (prin "^[[?1049h")  # Screen 2
   (prin "^[[?25l")  # Hide cursor
   (finally (prin "^[[?1049l" "^[[?25h")  # Screen 1, show cursor
      (while *Next
         (prin "^[[" 1 ";" 1 "H")  # cup
         (disp *Grid 0
            '((This)
               (cond
                  ((: co) (pack "<" @ ">"))
                  ((: goal) (pack " " @ " "))
                  (T "   ") ) ) )
         (des) )
      (key) ) )
