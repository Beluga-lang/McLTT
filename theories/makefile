.PHONY: all clean

-include makefile.coq

all: makefile.coq
	make -f "$?"

Parser.v: Parser.vy
	menhir --coq $?

makefile.coq: _CoqProject
	coq_makefile -f "$?" -o "$@"
