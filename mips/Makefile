SAIL:=../src/sail.native
LEM:=lem

# SOURCES:=mips_prelude.sail mips_tlb.sail mips_wrappers.sail mips_insts.sail mips_ri.sail mips_epilogue.sail ../etc/regfp.sail mips_regfp.sail
SOURCES:=mips_prelude.sail mips_tlb_stub.sail mips_wrappers.sail mips_insts.sail mips_epilogue.sail ../etc/regfp.sail mips_regfp.sail


all: mips.lem mips.ml mips_embed.lem

mips.lem: $(SOURCES)
	$(SAIL) -lem_ast -o $(BUILD)/mips $(SOURCES)

mips.ml: mips.lem ../src/lem_interp/interp_ast.lem
	$(LEM) -ocaml -lib ../src/lem_interp/ $<


mips_embed.lem: $(SOURCES)
# also generates mips_embed_sequential.lem, mips_embed_types.lem, mips_toFromInterp.lem
	$(SAIL) -lem -lem_lib Mips_extras_embed -o mips $(SOURCES)

clean:
	rm -f mips.lem mips.ml
	rm -f mips_embed*.lem mips_toFromInterp.lem
