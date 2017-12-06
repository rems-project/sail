SAIL:=../src/sail.native
LEM:=../../lem/lem

SOURCES:=riscv_types.sail riscv.sail ../etc/regfp.sail riscv_regfp.sail


all: riscv.lem riscv.ml riscv_embed.lem

riscv.lem: $(SOURCES)
	$(SAIL) -lem_ast -o riscv $(SOURCES)

riscv.ml: riscv.lem ../src/lem_interp/interp_ast.lem
	$(LEM) -ocaml -lib ../src/lem_interp/ $<


riscv_embed.lem: $(SOURCES)
# also generates riscv_embed_sequential.lem, riscv_embed_types.lem, riscv_toFromInterp.lem
	$(SAIL) -lem -lem_lib Riscv_extras_embed -o riscv $(SOURCES)

clean:
	rm -f riscv.lem riscv.ml
	rm -f riscv_embed*.lem riscv_toFromInterp.lem
