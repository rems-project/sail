THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
export SAIL_DIR
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips

SAIL:=$(SAIL_DIR)/sail

MIPS_PRE:=$(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail
MIPS_TLB:=$(MIPS_SAIL_DIR)/mips_tlb.sail
MIPS_TLB_STUB:=$(MIPS_SAIL_DIR)/mips_tlb_stub.sail
MIPS_SAILS:=$(MIPS_SAIL_DIR)/mips_wrappers.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail
MIPS_MAIN:=$(MIPS_SAIL_DIR)/main.sail

mips: $(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS) $(MIPS_MAIN)
	$(SAIL) -ocaml -o mips -memo_z3 $^

mips.c: $(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS) $(MIPS_MAIN)
	$(SAIL) -memo_z3 -c $^ 1> $@

mips_no_tlb.lem: $(MIPS_PRE) $(MIPS_TLB_STUB) $(MIPS_SAILS)
	$(SAIL) -lem -o mips_no_tlb -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
mips_no_tlb_types.lem: mips_no_tlb.lem

mips.lem: $(MIPS_PRE) $(SAIL_LIB_DIR)/mono_rewrites.sail $(MIPS_TLB) $(MIPS_SAILS)
	$(SAIL) -lem -o mips -auto_mono -mono_rewrites -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
mips_types.lem: mips.lem

M%.thy: m%.lem m%_types.lem mips_extras.lem
	lem -isa -outdir . -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' M$*_types.thy

%Script.sml: %.lem %_types.lem $(MIPS_SAIL_DIR)/mips_extras.lem
	lem -hol -outdir . -lib $(SAIL_DIR)/lib/hol -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^

%Theory.uo: %Script.sml
	Holmake $@

LOC_FILES:=$(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS) $(MIPS_MAIN)
include ../etc/loc.mk

clean:
	rm -rf mips Mips.thy mips.lem mips_types.lem _sbuild
	rm -f mipsScript.sml mips_typesScript.sml mips_extrasScript.sml
	-Holmake cleanAll
