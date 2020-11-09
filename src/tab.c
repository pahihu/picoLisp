/* 21dec18abu
 * (c) Software Lab. Alexander Burger
 */

#include "pico.h"

typedef struct symInit {fun code; char *name;} symInit;

static symInit Symbols[] = {
   {doAbs, "abs"},
   {doAccept, "accept"},
   {doAdd, "+"},
   {doAdr, "adr"},
   {doAlarm, "alarm"},
   {doAll, "all"},
   {doAnd, "and"},
   {doAny, "any"},
   {doAppend, "append"},
   {doApply, "apply"},
   {doArg, "arg"},
   {doArgs, "args"},
   {doArgv, "argv"},
   {doArrow, "->"},
   {doAs, "as"},
   {doAsoq, "asoq"},
   {doAssoc, "assoc"},
   {doAt, "at"},
   {doAtom, "atom"},
   {doBind, "bind"},
   {doBitAnd, "&"},
   {doBitOr, "|"},
   {doBitQ, "bit?"},
   {doBitXor, "x|"},
   {doBlk, "blk"},
   {doBool, "bool"},
   {doBox, "box"},
   {doBoxQ, "box?"},
   {doBreak, "!"},
   {doBy, "by"},
   {doBye, "bye"},
   {doByte, "byte"},
   {doBytes, "bytes"},
   {doCaaaar, "caaaar"},
   {doCaaadr, "caaadr"},
   {doCaaar, "caaar"},
   {doCaadar, "caadar"},
   {doCaaddr, "caaddr"},
   {doCaadr, "caadr"},
   {doCaar, "caar"},
   {doCadaar, "cadaar"},
   {doCadadr, "cadadr"},
   {doCadar, "cadar"},
   {doCaddar, "caddar"},
   {doCadddr, "cadddr"},
   {doCaddr, "caddr"},
   {doCadr, "cadr"},
   {doCall, "call"},
   {doCar, "car"},
   {doCase, "case"},
   {doCasq, "casq"},
   {doCatch, "catch"},
   {doCdaaar, "cdaaar"},
   {doCdaadr, "cdaadr"},
   {doCdaar, "cdaar"},
   {doCdadar, "cdadar"},
   {doCdaddr, "cdaddr"},
   {doCdadr, "cdadr"},
   {doCd, "cd"},
   {doCdar, "cdar"},
   {doCddaar, "cddaar"},
   {doCddadr, "cddadr"},
   {doCddar, "cddar"},
   {doCdddar, "cdddar"},
   {doCddddr, "cddddr"},
   {doCdddr, "cdddr"},
   {doCddr, "cddr"},
   {doCdr, "cdr"},
   {doChar, "char"},
   {doChain, "chain"},
   {doChop, "chop"},
   {doCirc, "circ"},
   {doCircQ, "circ?"},
   {doClip, "clip"},
   {doClose, "close"},
   {doCmd, "cmd"},
   {doCnt, "cnt"},
   {doCo, "co"},
   {doCol, ":"},
   {doCommit, "commit"},
   {doCon, "con"},
   {doConc, "conc"},
   {doCond, "cond"},
   {doConnect, "connect"},
   {doCons, "cons"},
   {doConsed, "consed"},
   {doCopy, "copy"},
   {doCtl, "ctl"},
   {doCtty, "ctty"},
   {doCut, "cut"},
   {doDate, "date"},
   {doDbck, "dbck"},
   {doDe, "de"},
   {doDec, "dec"},
   {doDef, "def"},
   {doDefault, "default"},
   {doDel, "del"},
   {doDelete, "delete"},
   {doDelq, "delq"},
   {doDetach, "detach"},
   {doDiff, "diff"},
   {doDir, "dir"},
   {doDiv, "/"},
   {doDm, "dm"},
   {doDo, "do"},
   {doE, "e"},
   {doEcho, "echo"},
   {doEnv, "env"},
   {doEof, "eof"},
   {doEol, "eol"},
   {doEq, "=="},
   {doEq0, "=0"},
   {doEq1, "=1"},
   {doEqT, "=T"},
   {doEqual, "="},
   {doErr, "err"},
   {doErrno, "errno"},
   {doEval, "eval"},
   {doExec, "exec"},
   {doExt, "ext"},
   {doExtern, "extern"},
   {doExtQ, "ext?"},
   {doExtra, "extra"},
   {doExtract, "extract"},
   {doFd, "fd"},
   {doFifo, "fifo"},
   {doFile, "file"},
   {doFill, "fill"},
   {doFilter, "filter"},
   {doFin, "fin"},
   {doFinally, "finally"},
   {doFind, "find"},
   {doFish, "fish"},
   {doFlgQ, "flg?"},
   {doFlip, "flip"},
   {doFlush, "flush"},
   {doFold, "fold"},
   {doFor, "for"},
   {doFork, "fork"},
   {doFormat, "format"},
   {doFree, "free"},
   {doFrom, "from"},
   {doFull, "full"},
   {doFully, "fully"},
   {doFunQ, "fun?"},
   {doGc, "gc"},
   {doGcCount, "gccount"},
   {doGe, ">="},
   {doGe0, "ge0"},
   {doGet, "get"},
   {doGetd, "getd"},
   {doGetl, "getl"},
   {doGlue, "glue"},
   {doGroup, "group"},
   {doGt, ">"},
   {doGt0, "gt0"},
   {doHash, "hash"},
   {doHead, "head"},
   {doHeap, "heap"},
   {doHear, "hear"},
   {doHide, "===="},
   {doHost, "host"},
   {doId, "id"},
   {doIdx, "idx"},
   {doIf, "if"},
   {doIf2, "if2"},
   {doIfn, "ifn"},
   {doIn, "in"},
   {doInc, "inc"},
   {doIndex, "index"},
   {doInfo, "info"},
   {doInsert, "insert"},
   {doIntern, "intern"},
   {doIpid, "ipid"},
   {doIsa, "isa"},
   {doJob, "job"},
   {doJournal, "journal"},
   {doKey, "key"},
   {doKids, "kids"},
   {doKill, "kill"},
   {doLast, "last"},
   {doLe, "<="},
   {doLe0, "le0"},
   {doLength, "length"},
   {doLet, "let"},
   {doLetQ, "let?"},
   {doLieu, "lieu"},
   {doLine, "line"},
   {doLines, "lines"},
   {doLink, "link"},
   {doLisp, "lisp"},
   {doList, "list"},
   {doListen, "listen"},
   {doLit, "lit"},
   {doLstQ, "lst?"},
   {doLoad, "load"},
   {doLock, "lock"},
   {doLoop, "loop"},
   {doLowQ, "low?"},
   {doLowc, "lowc"},
   {doLt, "<"},
   {doLt0, "lt0"},
   {doLup, "lup"},
   {doMade, "made"},
   {doMake, "make"},
   {doMap, "map"},
   {doMapc, "mapc"},
   {doMapcan, "mapcan"},
   {doMapcar, "mapcar"},
   {doMapcon, "mapcon"},
   {doMaplist, "maplist"},
   {doMaps, "maps"},
   {doMark, "mark"},
   {doMatch, "match"},
   {doMax, "max"},
   {doMaxi, "maxi"},
   {doMember, "member"},
   {doMemq, "memq"},
   {doMeta, "meta"},
   {doMethod, "method"},
   {doMin, "min"},
   {doMini, "mini"},
   {doMix, "mix"},
   {doMmeq, "mmeq"},
   {doMul, "*"},
   {doMulDiv, "*/"},
   {doName, "name"},
   {doNand, "nand"},
   {doNat, "%@"},
   {doNative, "native"},
   {doNEq, "n=="},
   {doNEq0, "n0"},
   {doNEqT, "nT"},
   {doNEqual, "<>"},
   {doNeed, "need"},
   {doNew, "new"},
   {doNext, "next"},
   {doNil, "nil"},
   {doNond, "nond"},
   {doNor, "nor"},
   {doNot, "not"},
   {doNsp, "nsp"},
   {doNth, "nth"},
   {doNumQ, "num?"},
   {doOff, "off"},
   {doOffset, "offset"},
   {doOn, "on"},
   {doOne, "one"},
   {doOnOff, "onOff"},
   {doOpen, "open"},
   {doOpid, "opid"},
   {doOpt, "opt"},
   {doOr, "or"},
   {doOut, "out"},
   {doPack, "pack"},
   {doPair, "pair"},
   {doPass, "pass"},
   {doPath, "path"},
   {doPatQ, "pat?"},
   {doPeek, "peek"},
   {doPick, "pick"},
   {doPipe, "pipe"},
   {doPlace, "place"},
   {doPoll, "poll"},
   {doPool, "pool"},
   {doPool2, "pool2"},
   {doPop, "pop"},
   {doPopq, "++"},
   {doPort, "port"},
   {doPr, "pr"},
   {doPreQ, "pre?"},
   {doPrin, "prin"},
   {doPrinl, "prinl"},
   {doPrint, "print"},
   {doPrintln, "println"},
   {doPrintsp, "printsp"},
   {doPrior, "prior"},
   {doProg, "prog"},
   {doProg1, "prog1"},
   {doProg2, "prog2"},
   {doProp, "prop"},
   {doPropCol, "::"},
   {doProtect, "protect"},
   {doProve, "prove"},
   {doPush, "push"},
   {doPush1, "push1"},
   {doPush1q, "push1q"},
   {doPut, "put"},
   {doPutl, "putl"},
   {doPwd, "pwd"},
   {doQueue, "queue"},
   {doQuit, "quit"},
   {doRand, "rand"},
   {doRange, "range"},
   {doRank, "rank"},
   {doRassoc, "rassoc"},
   {doRaw, "raw"},
   {doRd, "rd"},
   {doRead, "read"},
   {doRemove, "remove"},
   {doRem, "%"},
   {doReplace, "replace"},
   {doRest, "rest"},
   {doReverse, "reverse"},
   {doRewind, "rewind"},
   {doRollback, "rollback"},
   {doRot, "rot"},
   {doRun, "run"},
   {doSect, "sect"},
   {doSeed, "seed"},
   {doSeek, "seek"},
   {doSemicol, ";"},
   {doSend, "send"},
   {doSeq, "seq"},
   {doSet, "set"},
   {doSetCol, "=:"},
   {doSetq, "setq"},
   {doShift, ">>"},
   {doSigio, "sigio"},
   {doSize, "size"},
   {doSkip, "skip"},
   {doSort, "sort"},
   {doSpace, "space"},
   {doSplit, "split"},
   {doSpQ, "sp?"},
   {doSqrt, "sqrt"},
   {doStack, "stack"},
   {doState, "state"},
   {doStem, "stem"},
   {doStr, "str"},
   {doStrip, "strip"},
   {doStrQ, "str?"},
   {doStruct, "struct"},
   {doSub, "-"},
   {doSubQ, "sub?"},
   {doSum, "sum"},
   {doSuper, "super"},
   {doSwap, "swap"},
   {doSym, "sym"},
   {doSymbols, "symbols"},
   {doSymQ, "sym?"},
   {doSync, "sync"},
   {doSys, "sys"},
   {doT, "t"},
   {doTail, "tail"},
   {doTell, "tell"},
   {doText, "text"},
   {doThrow, "throw"},
   {doTick, "tick"},
   {doTill, "till"},
   {doTime, "time"},
   {doTouch, "touch"},
   {doTrace, "$"},
   {doTrail, "trail"},
   {doTrim, "trim"},
   {doTry, "try"},
   {doType, "type"},
   {doTzo, "tzo"},
   {doUdp, "udp"},
   {doUnify, "unify"},
   {doUnless, "unless"},
   {doUntil, "until"},
   {doUp, "up"},
   {doUppQ, "upp?"},
   {doUppc, "uppc"},
   {doUse, "use"},
   {doUsec, "usec"},
   {doVal, "val"},
   {doVersion, "version"},
   {doWait, "wait"},
   {doWhen, "when"},
   {doWhile, "while"},
   {doWipe, "wipe"},
   {doWith, "with"},
   {doWr, "wr"},
   {doXchg, "xchg"},
   {doXor, "xor"},
   {doYield, "yield"},
   {doYoke, "yoke"},
   {doZap, "zap"},
   {doZero, "zero"},
};

static any *IniIntern;

static any initSym(any v, char *s) {
   any x, *h;

   h = IniIntern + ihash(x = mkName(s));
   ASSERT(isSym(car(*h)));
   x = consSym(v,x);
   *h = cons(x,*h);
   return x;
}

void initSymbols(void) {
   int i;
   any Pico;

   PicoNil = Nil = symPtr(Avail),  Avail = Avail->car->car;  // Allocate 2 cells for NIL
   val(Nil) = tail(Nil) = val(Nil+1) = tail(Nil+1) = Nil;
   Zero = box(0);
   One = boxCnt(1);
   TNsp = BOX(1383865);
// XXX fprintf(stderr,"*** TNsp = %p\n",TNsp);
   for (i = 0; i < IHASH; ++i)
      Transient[i] = Nil;
   for (i = 0; i < EHASH; ++i)
      Extern[i] = Nil;

   // construct initial namespace
   // set initial hash tab to value of pico ns
   IniIntern = ptrNsp(Pico = consNsp());
   // Env.nsp contains symbols !!!
   Env.nsp = Pico1 = cons(initSym(Pico,"pico"),Nil); // initial ns lst

   initSym(mkStr(_CPU), "*CPU");
   initSym(mkStr(_OS), "*OS");
   DB    = initSym(Nil, "*DB");
   Meth  = initSym(boxFun(doMeth), "meth");
   Quote = initSym(boxFun(doQuote), "quote");
   T     = initSym(Nil, "T"),  val(T) = T;  // Last protected symbol

   mkExt(val(DB) = DbVal = consStr(DbTail = BOX('1')));
   Extern['1'] = cons(DbVal, Nil);

   ISym   = initSym(Nil, "I");
   NSym   = initSym(Nil, "N");
   SSym   = initSym(Nil, "S");
   CSym   = initSym(Nil, "C");
   BSym   = initSym(Nil, "B");
   WSym   = initSym(Nil, "W");
   PSym   = initSym(Nil, "P");
   Solo   = initSym(Zero, "*Solo");
   PPid   = initSym(Nil, "*PPid");
   Pid    = initSym(boxCnt(getpid()), "*Pid");
   At     = initSym(Nil, "@");
   At2    = initSym(Nil, "@@");
   At3    = initSym(Nil, "@@@");
   This   = initSym(Nil, "This");
   Prompt = initSym(Nil, "*Prompt");
   Dbg    = initSym(Nil, "*Dbg");
   Zap    = initSym(Nil, "*Zap");
   Ext    = initSym(Nil, "*Ext");
   Scl    = initSym(Zero, "*Scl");
   Class  = initSym(Nil, "*Class");
   Run    = initSym(Nil, "*Run");
   Hup    = initSym(Nil, "*Hup");
   Sig1   = initSym(Nil, "*Sig1");
   Sig2   = initSym(Nil, "*Sig2");
   Tstp1  = initSym(Nil, "*Tstp1");
   Tstp2  = initSym(Nil, "*Tstp2");
   Winch  = initSym(Nil, "*Winch");
   Up     = initSym(Nil, "^");
   Err    = initSym(Nil, "*Err");
   Msg    = initSym(Nil, "*Msg");
   Uni    = initSym(Nil, "*Uni");
   Led    = initSym(Nil, "*Led");
   Adr    = initSym(Nil, "*Adr");
   Fork   = initSym(Nil, "*Fork");
   Bye    = initSym(Nil, "*Bye");  // Last unremovable symbol

   for (i = 0; i < (int)(sizeof(Symbols)/sizeof(symInit)); ++i) {
      any x = boxFun(Symbols[i].code);
      // if (isShort(x) || (Symbols[i].code == 0x0000001001ddc40c))
      //      fprintf(stderr,"short %s (%p)\n",Symbols[i].name,Symbols[i].code);
      initSym(x, Symbols[i].name);
   }
}
