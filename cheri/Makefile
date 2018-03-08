THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
export SAIL_DIR
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips
CHERI_SAIL_DIR:=$(SAIL_DIR)/cheri
SAIL:=$(SAIL_DIR)/sail
SAIL_LIB_HEADERS:=$(SAIL_LIB_DIR)/flow.sail

CHERI_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_256.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(CHERI_SAIL_DIR)/cheri_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail $(MIPS_SAIL_DIR)/main.sail

CHERI128_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail $(MIPS_SAIL_DIR)/mips_tlb.sail $(CHERI_SAIL_DIR)/cheri_types.sail  $(CHERI_SAIL_DIR)/cheri_prelude_128.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail $(MIPS_SAIL_DIR)/mips_insts.sail $(CHERI_SAIL_DIR)/cheri_insts.sail $(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail $(MIPS_SAIL_DIR)/main.sail

cheri: $(CHERI_SAILS)
	$(SAIL) -ocaml -o $@ $^

cheri128: $(CHERI128_SAILS)
	$(SAIL) -ocaml -o $@ $^

clean:
	rm -rf cheri cheri128 _sbuild

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
	$(call EXTRACT_INST,CSetOffset)
	$(call EXTRACT_INST,CSetBounds)
	$(call EXTRACT_INST,CSetBoundsExact)
	$(call EXTRACT_INST,CClearTag)
	$(call EXTRACT_INST,ClearRegs)
	$(call EXTRACT_INST,CFromPtr)
	$(call EXTRACT_INST,CCheckPerm)
	$(call EXTRACT_INST,CCheckType)
	$(call EXTRACT_INST,CSeal)
	$(call EXTRACT_INST,CUnseal)
	$(call EXTRACT_INST,CCall)
	$(call EXTRACT_INST,CReturn)
	$(call EXTRACT_INST,CBx)
	$(call EXTRACT_INST,CJALR)
	$(call EXTRACT_INST,CLoad)
	$(call EXTRACT_INST,CStore)
	$(call EXTRACT_INST,CSC)
	$(call EXTRACT_INST,CLC)                 
