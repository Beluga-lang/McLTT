empty :=
space := $(empty) $(empty)
COQMAKEFILE := makefile.coq
COQFILES := $(sort $(wildcard ./*.v) $(patsubst %.vy,%.v,$(wildcard ./*.vy)))

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
update_CoqProject:
	(echo "-Q . Mcltt"; \
        echo ""; \
        echo "-arg -w -arg -notation-overridden"; \
        echo ""; \
        echo -e "$(subst $(space),\n,$(COQFILES))") > _CoqProject
