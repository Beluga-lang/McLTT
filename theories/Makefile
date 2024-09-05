empty :=
space := $(empty) $(empty)

MENHIR := menhir

COQMAKEFILE := CoqMakefile.mk
COQPROJECTFILE := _CoqProject
PARSERBASE := parser.ml
POSTPARSERBASE := type_checker.ml
PARSERFILE := ../driver/$(PARSERBASE)
POSTPARSERFILE := ../driver/$(POSTPARSERBASE)
FRONTENDDIR := Frontend
PARSEREXTRACTIONCOQFILE := $(FRONTENDDIR)/ParserExtraction.v
PARSEREXTRACTIONRESULTFILE := $(FRONTENDDIR)/$(PARSERBASE)
POSTPARSEREXTRACTIONCOQFILE := $(FRONTENDDIR)/PostParserExtraction.v
POSTPARSEREXTRACTIONRESULTFILE := $(FRONTENDDIR)/$(POSTPARSERBASE)
COQPARSERFILE := $(patsubst %.vy,%.v,$(shell find ./ -name '*.vy'))
COQFILES := $(sort $(shell find ./ -name '*.v') $(COQPARSERFILE))

.PHONY: all
all: $(COQMAKEFILE)
	@+$(MAKE) -f "$(COQMAKEFILE)" all

.PHONY: clean
clean: $(COQMAKEFILE)
	@+$(MAKE) -f "$(COQMAKEFILE)" cleanall
	@echo "CLEAN $(COQPARSERFILE) $(PARSERBASE) $(patsubst %.ml,%.mli,$(PARSERBASE)) $(PARSERFILE) $(patsubst %.ml,%.mli,$(PARSERFILE))"
	@rm -f "$(COQPARSERFILE)" "$(PARSERBASE)" "$(patsubst %.ml,%.mli,$(PARSERBASE))" "$(PARSERFILE)" "$(patsubst %.ml,%.mli,$(PARSERFILE))"
	@echo "CLEAN $(POSTPARSERBASE) $(patsubst %.ml,%.mli,$(POSTPARSERBASE)) $(POSTPARSERFILE) $(patsubst %.ml,%.mli,$(POSTPARSERFILE))"
	@rm -f "$(POSTPARSERBASE)" "$(patsubst %.ml,%.mli,$(POSTPARSERBASE))" "$(POSTPARSERFILE)" "$(patsubst %.ml,%.mli,$(POSTPARSERFILE))"
	@echo "CLEAN $(COQMAKEFILE) $(COQMAKEFILE).conf"
	@rm -f "$(COQMAKEFILE)" "$(COQMAKEFILE).conf"

.PHONY: update_CoqProject
update_CoqProject: clean
	(echo "-R . Mcltt"; \
        echo ""; \
        echo "-arg -w -arg -cast-in-pattern,-notation-overridden"; \
        echo ""; \
        echo -e "$(subst $(space),\n,$(COQFILES))") > "$(COQPROJECTFILE)"

.PHONY: force
force: ;

$(COQMAKEFILE): $(COQPROJECTFILE)
	$(COQBIN)coq_makefile -f "$?" -o "$@"

$(COQPROJECTFILE): ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f "$(COQMAKEFILE)" "$@"
