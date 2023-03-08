gen_parser:
	@echo "Generating parser..."
	cd lib/coq; \
		menhir --coq Parser.vy; \
		coqc -Q . McLtt Parser.v; \
		coqc -Q . McLtt Extract.v
