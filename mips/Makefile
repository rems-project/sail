THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
export SAIL_DIR
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips

SAIL:=$(SAIL_DIR)/sail

MIPS_PRE:=$(SAIL_LIB_DIR)/flow.sail $(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail
MIPS_TLB:=$(MIPS_SAIL_DIR)/mips_tlb.sail
MIPS_TLB_STUB:=$(MIPS_SAIL_DIR)/mips_tlb_stub.sail
MIPS_SAILS:=$(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail
MIPS_MAIN:=$(MIPS_SAIL_DIR)/main.sail

mips: $(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS) $(MIPS_MAIN)
	$(SAIL) -ocaml -o mips $^

mips_no_tlb.lem: $(MIPS_PRE) $(MIPS_TLB_STUB) $(MIPS_SAILS)
	$(SAIL) -lem -o mips_no_tlb -lem_mwords -lem_lib Mips_extras -undefined_gen $^
mips_no_tlb_types.lem: mips_no_tlb.lem

# TODO: Use monomorphisation so that we can switch to machine words
mips.lem: $(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS)
	$(SAIL) -lem -o mips -lem_lib Mips_extras -undefined_gen $^
mips_types.lem: mips.lem

M%.thy: m%.lem m%_types.lem mips_extras.lem
	lem -isa -outdir . -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^

clean:
	rm -rf mips Mips.thy mips.lem _sbuild
