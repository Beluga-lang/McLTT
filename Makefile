.PHONY: all clean

all:
	@make -C theories
	@dune build

clean:
	@make clean -C theories
	@dune clean
	@echo "Cleaning finished."
