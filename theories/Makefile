empty :=
space := $(empty) $(empty)

MENHIR := menhir

COQMAKEFILE := CoqMakefile.mk
COQPROJECTFILE := _CoqProject
PARSERBASE := parser.ml
PARSERFILE := ../driver/$(PARSERBASE)
PARSEREXTRACTIONDIR := Frontend
PARSEREXTRACTIONCOQFILE := $(PARSEREXTRACTIONDIR)/ParserExtraction.v
PARSEREXTRACTIONRESULTFILE := $(PARSEREXTRACTIONDIR)/$(PARSERBASE)
COQPARSERFILE := $(patsubst %.vy,%.v,$(shell find ./ -name '*.vy'))
COQFILES := $(sort $(shell find ./ -name '*.v') $(COQPARSERFILE))

.PHONY: all
all: $(COQMAKEFILE) $(COQPARSERFILE)
	@+$(MAKE) -f "$(COQMAKEFILE)" all
	@+$(MAKE) "$(PARSERFILE)"

.PHONY: clean
clean: $(COQMAKEFILE)
	@+$(MAKE) -f "$(COQMAKEFILE)" cleanall
	@echo "CLEAN $(COQPARSERFILE) $(PARSERBASE) $(patsubst %.ml,%.mli,$(PARSERBASE)) $(PARSERFILE) $(patsubst %.ml,%.mli,$(PARSERFILE)) $(COQMAKEFILE) $(COQMAKEFILE).conf"
	@rm -f "$(COQPARSERFILE)" "$(PARSERBASE)" "$(patsubst %.ml,%.mli,$(PARSERBASE))" "$(PARSERFILE)" "$(patsubst %.ml,%.mli,$(PARSERFILE))" "$(COQMAKEFILE)" "$(COQMAKEFILE).conf"

.PHONY: update_CoqProject
update_CoqProject: clean
	(echo "-R . Mcltt"; \
        echo ""; \
        echo "-arg -w -arg -notation-overridden"; \
        echo ""; \
        echo -e "$(subst $(space),\n,$(COQFILES))") > "$(COQPROJECTFILE)"

.PHONY: force
force: ;

$(COQMAKEFILE): $(COQPROJECTFILE)
	$(COQBIN)coq_makefile -f "$?" -o "$@"

$(COQPARSERFILE): %.v : %.vy
	$(MENHIR) --coq "$?"

$(COQPROJECTFILE): ;

$(PARSERBASE): $(PARSEREXTRACTIONCOQFILE)
	@+$(MAKE) -f "$(COQMAKEFILE)" -B "$(patsubst %.v,%.vo,$?)"

$(PARSERFILE): $(PARSEREXTRACTIONCOQFILE)
	@+$(MAKE) "$(PARSERBASE)"
	@echo "MOVE $(PARSERBASE) => $@"
	@mv "$(PARSERBASE)" "$@"
	@mv "$(patsubst %.ml,%.mli,$(PARSERBASE))" "$(patsubst %.ml,%.mli,$@)"

%: $(COQMAKEFILE) force
	@+$(MAKE) -f "$(COQMAKEFILE)" "$@"
