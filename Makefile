EXECUTABLE:=_build/default/driver/mcltt.exe

.PHONY: all clean

all:
	@cd theories; make
	@dune build

clean:
	@cd theories; make clean
	@dune clean
	@echo "Cleaning finished."

${EXECUTABLE}: all
