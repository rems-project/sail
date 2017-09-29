
SAIL:=../src/sail.native
SOURCES:=riscv_types.sail riscv.sail ../etc/regfp.sail riscv_regfp.sail
all: lem_ast shallow

lem_ast: $(SOURCES) $(SAIL)
	$(SAIL) -lem_ast $(SOURCES) -o riscv

shallow: $(SOURCES) $(SAIL)
	$(SAIL) -lem_lib Riscv_extras_embed -lem $(SOURCES) -o riscv

clean:
	rm -f riscv.lem riscv_embed*.lem riscv_toFromInterp.lem
	rm -f riscv_type*.lem
