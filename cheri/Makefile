THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
export SAIL_DIR
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips
CHERI_SAIL_DIR:=$(SAIL_DIR)/cheri
SAIL:=$(SAIL_DIR)/sail
SAIL_LIB_HEADERS:=$(SAIL_LIB_DIR)/flow.sail

MIPS_PRE:=$(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail
MIPS_TLB:=$(MIPS_SAIL_DIR)/mips_tlb.sail
MIPS_TLB_STUB:=$(MIPS_SAIL_DIR)/mips_tlb_stub.sail
MIPS_INSTS:=$(MIPS_SAIL_DIR)/mips_insts.sail
MIPS_EPILOGUE:=$(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail
CHERI_PRE:=$(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_256.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail
CHERI128_PRE:=$(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_128.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail
CHERI_INSTS:=$(CHERI_SAIL_DIR)/cheri_insts.sail

CHERI_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_NO_TLB_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB_STUB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI128_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB) $(CHERI128_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI128_NO_TLB_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB_STUB) $(CHERI128_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_MAIN:=$(MIPS_SAIL_DIR)/main.sail

cheri: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml -o $@ $^

cheri128: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml -o $@ $^

# TODO Using bit lists for now in Lem generation; for machine words,
# monomorphisation is needed due to some variable length bitvectors, e.g. in
# CLoad as of commit b34c3fb, in the TLB translation, and in compressed
# capability functions

cheri_no_tlb.lem: $(CHERI_NO_TLB_SAILS)
	$(SAIL) -lem -o cheri_no_tlb -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri_no_tlb_types.lem: cheri_no_tlb.lem

cheri.lem: $(CHERI_SAILS)
	$(SAIL) -lem -o cheri -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri_types.lem: cheri.lem

cheri128_no_tlb.lem: $(CHERI128_NO_TLB_SAILS)
	$(SAIL) -lem -o cheri128_no_tlb -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri128_no_tlb_types.lem: cheri128_no_tlb.lem

cheri128.lem: $(CHERI128_SAILS)
	$(SAIL) -lem -o cheri128 -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri128_types.lem: cheri128.lem

C%.thy: c%.lem c%_types.lem $(MIPS_SAIL_DIR)/mips_extras.lem
	lem -isa -outdir . -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' C$*_types.thy

clean:
	rm -rf cheri cheri128 _sbuild inst_*.sail

EXTRACT_INST=sed -n "/START_${1}\b/,/END_${1}\b/p" cheri_insts.sail | sed 's/^  //;1d;$$d' > inst_$1.sail
extract: cheri_insts.sail
	$(call EXTRACT_INST,CGetPerms)
	$(call EXTRACT_INST,CGetType)
	$(call EXTRACT_INST,CGetBase)
	$(call EXTRACT_INST,CGetOffset)
	$(call EXTRACT_INST,CGetLen)
	$(call EXTRACT_INST,CGetTag)
	$(call EXTRACT_INST,CGetSealed)
	$(call EXTRACT_INST,CGetPCC)
	$(call EXTRACT_INST,CGetPCCSetOffset)
	$(call EXTRACT_INST,CGetCause)
	$(call EXTRACT_INST,CSetCause)
	$(call EXTRACT_INST,CAndPerm)
	$(call EXTRACT_INST,CToPtr)
	$(call EXTRACT_INST,CSub)
	$(call EXTRACT_INST,CPtrCmp)
	$(call EXTRACT_INST,CIncOffset)
	$(call EXTRACT_INST,CIncOffsetImmediate)
	$(call EXTRACT_INST,CSetOffset)
	$(call EXTRACT_INST,CSetBounds)
	$(call EXTRACT_INST,CSetBoundsImmediate)
	$(call EXTRACT_INST,CSetBoundsExact)
	$(call EXTRACT_INST,CClearTag)
	$(call EXTRACT_INST,CMOVX)
	$(call EXTRACT_INST,ClearRegs)
	$(call EXTRACT_INST,CFromPtr)
	$(call EXTRACT_INST,CBuildCap)
	$(call EXTRACT_INST,CCopyType)
	$(call EXTRACT_INST,CCheckPerm)
	$(call EXTRACT_INST,CCheckType)
	$(call EXTRACT_INST,CTestSubset)
	$(call EXTRACT_INST,CSeal)
	$(call EXTRACT_INST,CCSeal)
	$(call EXTRACT_INST,CUnseal)
	$(call EXTRACT_INST,CCall)
	$(call EXTRACT_INST,CCall2)
	$(call EXTRACT_INST,CReturn)
	$(call EXTRACT_INST,CBtag)
	$(call EXTRACT_INST,CBz)
	$(call EXTRACT_INST,CJALR)
	$(call EXTRACT_INST,CLoad)
	$(call EXTRACT_INST,CStore)
	$(call EXTRACT_INST,CSC)
	$(call EXTRACT_INST,CLC)

