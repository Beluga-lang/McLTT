.PHONY: all clean

all:
	@$(MAKE) -C theories
	@dune build

coqdoc: all
	@${MAKE} coqdoc -C theories

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
