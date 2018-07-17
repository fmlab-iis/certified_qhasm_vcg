LIBS=\
	lib/gbarith \
	lib/polyop \
	lib/coq-bits
COQMAKEFILE = Makefile.coq

.PHONY: default libs

default:
	make -f ${COQMAKEFILE}

libs:
	for lib in ${LIBS}; do \
		make -C $$lib; \
	done

all: libs default

clean:
	make -f ${COQMAKEFILE} clean

distclean:
	for lib in ${LIBS}; do \
		make -C $$lib clean; \
	done
	make -f ${COQMAKEFILE} clean
