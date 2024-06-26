# 30jan19abu
# (c) Software Lab. Alexander Burger

bin = ../bin
lib = ../lib

picoFiles = main.c gc.c apply.c flow.c sym.c subr.c big.c io.c net.c tab.c

CC = clang -flto
# CCLD is the cc (compiler frontend) to use for the link step.
CCLD = clang -flto
GCCLD = gcc-mp-12 -flto
CPU = $(shell uname -m)

ifeq ($(debug),yes)
	CC += -g #-fsanitize=address
	CCLD += -g #-fsanitize=address
	OPT = -DPICODEBUG=1
    STRIP = :
else
	OPT = -O3 -fomit-frame-pointer -DNDEBUG #-DPICODEBUG=1
    STRIP = strip
endif

ifeq ($(target),pil32)
        M32=-m32
endif

ALIGN_FUNCTIONS = -falign-functions=32

BFLAGS = -pipe \
	$(ALIGN_FUNCTIONS) \
	-fno-strict-aliasing \
	-W -Wimplicit -Wreturn-type -Wunused -Wformat \
	-Wuninitialized -Wstrict-prototypes \
	-D_GNU_SOURCE  -D_FILE_OFFSET_BITS=64

LIB-FLAGS = -lffi

CFLAGS = -c $(OPT) $(BFLAGS)

DYNAMIC-CC-FLAGS=

ifeq ($(shell uname), Linux)
ifeq ($(target), pil32)
	GCCLD = gcc
ifeq ($(CPU), x86_64)
    CPU = i386
endif
endif
	OS = Linux
	BFLAGS += ${M32} -fPIC
	PICOLISP-FLAGS = ${M32} -rdynamic
	LIB-FLAGS += -lm -ldl
	DYNAMIC-LIB-FLAGS = ${M32} -shared -export-dynamic
	LCRYPT = -lcrypt
else
ifeq ($(shell uname), OpenBSD)
	OS = OpenBSD
	BFLAGS += ${M32}
	PICOLISP-FLAGS = ${M32} -rdynamic -Wl,-E
	LIB-FLAGS += -lm
	DYNAMIC-LIB-FLAGS = -Wl,-E -Wl,-shared
	LCRYPT = -lcrypto
else
ifeq ($(shell uname), FreeBSD)
	OS = FreeBSD
	CC = gcc
	CCLD = clang
	BFLAGS += ${M32} -fPIC
	PICOLISP-FLAGS = ${M32} -rdynamic
	LIB-FLAGS += -lm
	DYNAMIC-LIB-FLAGS = ${M32} -shared
	LCRYPT = -lcrypt
else
ifeq ($(shell uname), NetBSD)
	OS = NetBSD
	BFLAGS += ${M32}
	PICOLISP-FLAGS = ${M32} -rdynamic
	LIB-FLAGS += -lm
	DYNAMIC-LIB-FLAGS = ${M32} -shared -export-dynamic
	LCRYPT = -lcrypto
else
ifeq ($(shell uname), Darwin)
ifeq ($(target), pil32)
	GCCLD = gcc
    CPU = i386
    # BFLAGS += -I$(HOME)/local32/include
    # LIB-FLAGS = $(HOME)/local32/lib/libffi.a
endif
	OS = Darwin
	# ALIGN_FUNCTIONS = -mllvm -align-all-functions=5
	ALIGN_FUNCTIONS = -falign-functions=32
	BFLAGS += ${M32} -mmacosx-version-min=10.6 \
		  -Wno-parentheses -D_DARWIN_UNLIMITED_SELECT \
		  -D_XOPEN_SOURCE -Wno-deprecated-declarations
	PICOLISP-FLAGS = ${M32}
	LIB-FLAGS += -lc -lm -ldl
	DYNAMIC-LIB-FLAGS = ${M32} -dynamiclib -undefined dynamic_lookup
    SYSDIRS = -I/usr/local/include -L/usr/local/lib
	LCRYPT = #-lcrypto
	STRIP-FLAGS = -x
else
ifeq ($(shell uname), SunOS)
	OS = SunOS
	BFLAGS += ${M32}
	PICOLISP-FLAGS =
	LIB-FLAGS += -lm -lnsl -lsocket
	DYNAMIC-LIB-FLAGS = -G
	LCRYPT = -lcrypt
else
ifeq ($(shell uname), AIX)
	OS = AIX
	BFLAGS += -maix32
	PICOLISP-FLAGS = -maix32 -Wl,-brtl -Wl,-bexpall
	LIB-FLAGS += -lm
	DYNAMIC-LIB-FLAGS = -maix32 -Wl,-G -shared -lm
	LCRYPT = -lcrypt
else
ifeq ($(shell uname), HP-UX)
	OS = HP-UX
	BFLAGS +=
	PICOLISP-FLAGS = ${M32} -rdynamic
	LIB-FLAGS += -lm -ldl
	DYNAMIC-LIB-FLAGS = ${M32} -shared
	LCRYPT =
else
ifeq ($(shell uname), IRIX64)
	OS = IRIX64
	BFLAGS += -std=gnu99
	DYNAMIC-LIB-FLAGS = -shared
	STRIP-FLAGS = -f
else
ifeq ($(shell uname -o | egrep -q "Cygwin|Msys" ; echo $$?), 0)
	OS = Cygwin
	BFLAGS += ${M32}
	DYNAMIC-LIB-FLAGS = -shared
	PICOLISP-FLAGS =
	DLL-DEFS = $(bin)/picolisp.dll
	LCRYPT = -lcrypt
	exe = .exe
	dll = .dll
endif
endif
endif
endif
endif
endif
endif
endif
endif
endif

BFLAGS += -D_OS='"$(OS)"' -D_CPU='"$(CPU)"'


picolisp: $(bin)/picolisp $(lib)/ext$(dll) $(lib)/ht$(dll)
picolisp: $(bin)/picolisp $(lib)/ext$(dll) $(lib)/ht$(dll)
tools: $(bin)/lat1 $(bin)/utf2 $(bin)/balance
gate: $(bin)/ssl $(bin)/httpGate

all: picolisp tools gate

.c.o:
	$(CC) $(CFLAGS) $*.c

ext.o ht.o: pico.h
	$(CC) $(CFLAGS) $*.c $(DYNAMIC-CC-FLAGS)

$(picoFiles:.c=.o) ext.o ht.o: pico.h
main.o: vers.h


ifeq ($(OS), Cygwin)

$(bin)/picolisp$(dll): $(picoFiles:.c=.o)
	$(CCLD) -o $(bin)/picolisp$(dll) $(DYNAMIC-LIB-FLAGS) $(picoFiles:.c=.o)
	$(STRIP) $(STRIP-FLAGS) $(bin)/picolisp$(dll)

$(bin)/picolisp: $(picoFiles:.c=.o) $(bin)/picolisp$(dll) start.o
	mkdir -p $(bin) $(lib)
	$(CCLD) -o $(bin)/picolisp$(exe) $(PICOLISP-FLAGS) start.o -L$(bin) -l$(bin)/picolisp
	$(STRIP) $(STRIP-FLAGS) $(bin)/picolisp$(exe)

else

$(bin)/picolispx: $(picoFiles)
	mkdir -p $(bin) $(lib)
	$(GCCLD) -O3 -fomit-frame-pointer $(BFLAGS) -o $(bin)/picolispx$(exe) $(PICOLISP-FLAGS) $(picoFiles) $(LIB-FLAGS)
	$(STRIP) $(STRIP-FLAGS) $(bin)/picolispx$(exe)

$(bin)/picolisp: $(picoFiles:.c=.o)
	mkdir -p $(bin) $(lib)
	$(CCLD) -o $(bin)/picolisp$(exe) $(PICOLISP-FLAGS) $(picoFiles:.c=.o) $(LIB-FLAGS)
	$(STRIP) $(STRIP-FLAGS) $(bin)/picolisp$(exe)

endif


$(lib)/ext$(dll): ext.o
	$(CCLD) -o $(lib)/ext$(dll) $(DYNAMIC-LIB-FLAGS) ext.o $(DLL-DEFS) $(LCRYPT)
	$(STRIP) $(STRIP-FLAGS) $(lib)/ext$(dll)

$(lib)/ht$(dll): ht.o
	$(CCLD) -o $(lib)/ht$(dll) $(DYNAMIC-LIB-FLAGS) ht.o $(DLL-DEFS)
	$(STRIP) $(STRIP-FLAGS) $(lib)/ht$(dll)


$(bin)/lat1: lat1.c
	$(CC) -o $(bin)/lat1$(exe) lat1.c
	$(STRIP) $(STRIP-FLAGS) $(bin)/lat1$(exe)

$(bin)/utf2: utf2.c
	$(CC) -o $(bin)/utf2$(exe) utf2.c
	$(STRIP) $(STRIP-FLAGS) $(bin)/utf2$(exe)

$(bin)/balance: balance.c
	$(CC) -o $(bin)/balance$(exe) balance.c
	$(STRIP) $(STRIP-FLAGS) $(bin)/balance$(exe)

$(bin)/ssl: ssl.c
	$(CC) $(SYSDIRS) -o $(bin)/ssl$(exe) ssl.c -lssl -lcrypto
	$(STRIP) $(STRIP-FLAGS) $(bin)/ssl$(exe)

$(bin)/httpGate: httpGate.c
	$(CC) $(SYSDIRS) -o $(bin)/httpGate$(exe) httpGate.c -lssl -lcrypto
	$(STRIP) $(STRIP-FLAGS) $(bin)/httpGate$(exe)


# Clean up
clean:
	rm -f *.o

# vim:noet:ts=4:sw=4
