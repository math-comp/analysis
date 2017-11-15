.PHONY: all clean

all: Makefile.coq
	make -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
