gen_parser:
	@echo "Generating parser..."
	cd lib; \
		menhir --coq Parser.vy; \
		coqc -Q . Mcltt Parser.v; \
		coqc -Q . Mcltt ParserExtraction.v
