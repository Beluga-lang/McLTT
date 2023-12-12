COQMAKEFILE := makefile.coq

.PHONY: all
all: $(COQMAKEFILE)

-include $(COQMAKEFILE)

clean::
	rm -f $(COQMAKEFILE)
	rm -f $(COQMAKEFILE).conf

Parser.v: Parser.vy
	menhir --coq "$?"

$(COQMAKEFILE): _CoqProject
	coq_makefile -f "$?" -o "$@"
