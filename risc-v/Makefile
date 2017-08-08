
SAIL:=../src/sail.native

all: lem_ast shallow

lem_ast: riscv.sail $(SAIL)
	$(SAIL) -lem_ast $<

shallow: riscv.sail $(SAIL)
	$(SAIL) -lem_lib Riscv_extras_embed -lem $<

clean:
	rm -f riscv.lem riscv_embed*.lem
