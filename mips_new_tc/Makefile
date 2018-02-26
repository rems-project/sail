THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
export SAIL_DIR
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips_new_tc

SAIL:=$(SAIL_DIR)/sail

MIPS_SAILS:=$(SAIL_LIB_DIR)/flow.sail $(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail $(MIPS_SAIL_DIR)/main.sail

mips: $(MIPS_SAILS)
	$(SAIL) -ocaml -o mips $(MIPS_SAILS)

clean:
	rm -rf _sbuild
