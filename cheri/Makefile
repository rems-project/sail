THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
export SAIL_DIR
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
MIPS_SAIL_DIR:=$(SAIL_DIR)/mips
CHERI_SAIL_DIR:=$(SAIL_DIR)/cheri
SAIL:=$(SAIL_DIR)/sail
SAIL_LIB_HEADERS:=

MIPS_PRE:=$(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail
MIPS_TLB:=$(MIPS_SAIL_DIR)/mips_tlb.sail
MIPS_TLB_STUB:=$(MIPS_SAIL_DIR)/mips_tlb_stub.sail
MIPS_INSTS:=$(MIPS_SAIL_DIR)/mips_insts.sail
MIPS_EPILOGUE:=$(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail
CHERI_PRE:=$(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_256.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail
CHERI128_PRE:=$(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_128.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail
CHERI_INSTS:=$(CHERI_SAIL_DIR)/cheri_insts.sail

CHERI_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_MONO_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(SAIL_LIB_DIR)/mono_rewrites.sail $(MIPS_TLB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_NO_TLB_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB_STUB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI128_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB) $(CHERI128_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI128_NO_TLB_SAILS:=$(SAIL_LIB_HEADERS) $(MIPS_PRE) $(MIPS_TLB_STUB) $(CHERI128_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_MAIN:=$(MIPS_SAIL_DIR)/main.sail

cheri: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml -o $@ $^

cheri_trace: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_trace -o $@ $^

cheri.c: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -memo_z3 -c $^ 1> $@

latex_128: $(MIPS_SAIL_DIR)/prelude.sail $(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_128.sail
	rm -rf sail_latexcc
	$(SAIL) -latex -latex_prefix sailcc -o sail_latexcc $^

latex_256: $(CHERI_SAILS)
	rm -rf sail_latex
	$(SAIL) -latex $^

latex: latex_128 latex_256

cheri128: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml -o $@ $^

cheri128_trace: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_trace -o $@ $^

LOC_FILES:=$(CHERI_SAILS) $(CHERI_MAIN)
include ../etc/loc.mk

# TODO Using bit lists for now in Lem generation; for machine words,
# monomorphisation is needed due to some variable length bitvectors, e.g. in
# CLoad as of commit b34c3fb, in the TLB translation, and in compressed
# capability functions

cheri_no_tlb.lem: $(CHERI_NO_TLB_SAILS)
	$(SAIL) -lem -o cheri_no_tlb -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri_no_tlb_types.lem: cheri_no_tlb.lem

cheri.lem: $(CHERI_MONO_SAILS) $(CHERI_MAIN)
	$(SAIL) -lem -o cheri -auto_mono -mono_rewrites -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
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

%Script.sml: %.lem %_types.lem $(MIPS_SAIL_DIR)/mips_extras.lem
	lem -hol -outdir . -lib $(SAIL_DIR)/lib/hol -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^

%Theory.uo: %Script.sml
	Holmake $@

clean:
	rm -rf cheri cheri_trace cheri128 cheri128_trace _sbuild inst_*.sail cheri.c sail_latex sail_latexcc
	rm -f cheriScript.sml cheri_typesScript.sml mips_extrasScript.sml
	-Holmake cleanAll
