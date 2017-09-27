
SAIL:=../src/sail.native
SOURCES:=riscv_types.sail riscv.sail ../etc/regfp.sail riscv_regfp.sail
all: lem_ast shallow

lem_ast: $(SOURCES) $(SAIL)
	$(SAIL) -lem_ast $(SOURCES)

shallow: $(SOURCES) $(SAIL)
	$(SAIL) -lem_lib Riscv_extras_embed -lem $(SOURCES)

clean:
	rm -f riscv.lem riscv_embed*.lem
