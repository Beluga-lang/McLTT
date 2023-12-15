empty :=
space := $(empty) $(empty)

COQMAKEFILE := makefile.coq
COQFILES := $(sort $(shell find ./ -name '*.v') $(patsubst %.vy,%.v,$(shell find ./ -name '*.vy')))

.PHONY: all
all: $(COQMAKEFILE)

-include $(COQMAKEFILE)

clean::
	rm -f $(COQMAKEFILE)
	rm -f $(COQMAKEFILE).conf

Parser.v: Parser.vy
	menhir --coq "$?"

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o "$@"

.PHONY: update_CoqProject
update_CoqProject: cleanall
	(echo "-R . Mcltt"; \
        echo ""; \
        echo "-arg -w -arg -notation-overridden"; \
        echo ""; \
        echo -e "$(subst $(space),\n,$(COQFILES))") > _CoqProject
