gen_parser:
	@echo "Generating parser..."
	@cd lib; \
		coqc -Q . Mcltt Syntax.v; \
		menhir --coq Parser.vy; \
		coqc -Q . Mcltt Parser.v; \
		coqc -Q . Mcltt ParserExtraction.v
