.PHONY: all clean

all:
	@$(MAKE) -C theories
	@dune build

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
