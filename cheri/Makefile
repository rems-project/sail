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

cheri_coverage: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml-coverage -ocaml -o $@ $^

cheri_trace: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_trace -o $@ $^

coverage_report: bisect*.out
	bisect-ppx-report -I _sbuild/_build -html $@ $^

cheri.c: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -memo_z3 -O -c $^ 1> $@

C_OPT=-O2
GCOV_FLAGS=
cheri_c: cheri.c ../lib/sail.h Makefile
	gcc $(C_OPT) $(GCOV_FLAGS) $< ../lib/*.c -lgmp -lz -I ../lib/ -o $@

# Note that for coverage purposes O1 appears optimal. O0 means lots of obviously dead code but O2 risks reducing granularity too much.
cheri_c_gcov: C_OPT=-O1
cheri_c_gcov: GCOV_FLAGS=-fprofile-arcs -ftest-coverage
cheri_c_gcov: cheri_c

gcovr:
	gcovr -r . --html --html-detail -o index.html

latex_128: $(MIPS_SAIL_DIR)/prelude.sail $(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_128.sail
	rm -rf sail_latexcc
	$(SAIL) -latex -latex_prefix sailcc -o sail_latexcc $^

latex_256: $(CHERI_SAILS)
	rm -rf sail_latex
	$(SAIL) -latex $^

latex: latex_128 latex_256

# to install latex in the right place - specific to PS checkouts
CHERI_ARCH_PATH=/home/pes20/repos/ctsrd/reports/cheri-architecture
install_latex: 
	rm -rf $(CHERI_ARCH_PATH)/sail_latex/*.tex
	cp sail_latex/*.tex $(CHERI_ARCH_PATH)/sail_latex
	rm -rf $(CHERI_ARCH_PATH)/sail_latexcc/*.tex
	cp sail_latexcc/*.tex $(CHERI_ARCH_PATH)/sail_latexcc

cheri128: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml -o $@ $^

cheri128_trace: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_trace -o $@ $^

cheri128.c: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -memo_z3 -O -c $^ 1> $@

cheri128_c: cheri128.c ../lib/sail.h Makefile
	gcc $(C_OPT) $(GCOV_FLAGS) $< ../lib/*.c -lgmp -lz -I ../lib/ -o $@

# Note that for coverage purposes O1 appears optimal. O0 means lots of obviously dead code but O2 risks reducing granularity too much.
cheri128_c_gcov: C_OPT=-O1
cheri128_c_gcov: GCOV_FLAGS=-fprofile-arcs -ftest-coverage
cheri128_c_gcov: cheri128_c

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
	lem -isa -outdir . -lib Sail=$(SAIL_DIR)/src/gen_lib -lib Sail=$(SAIL_DIR)/src/lem_interp $^
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' C$*_types.thy

%Script.sml: %.lem %_types.lem $(MIPS_SAIL_DIR)/mips_extras.lem
	lem -hol -outdir . -lib $(SAIL_DIR)/lib/hol -i $(SAIL_DIR)/lib/hol/sail2_prompt_monad.lem -i $(SAIL_DIR)/lib/hol/sail2_prompt.lem -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^

%Theory.uo: %Script.sml
	Holmake $@

cheri.v cheri_types.v: $(CHERI_SAILS)
	$(SAIL) -coq -o cheri -coq_lib mips_extras -undefined_gen -memo_z3 -dcoq_undef_axioms $^

CHERI_COQ = cheri_types.v mips_extras.v cheri.v
COQ_LIBS = -R ../../bbv/theories bbv -R ../lib/coq Sail

%.vo: %.v
	coqc $(COQ_LIBS) $<
cheri.vo: cheri_types.vo mips_extras.vo

clean:
	rm -rf cheri cheri_trace cheri_coverage cheri128 cheri128_trace _sbuild inst_*.sail cheri.c sail_latex sail_latexcc coverage_report
	rm -f cheriScript.sml cheri_typesScript.sml mips_extrasScript.sml
	rm -f cheri.v cheri_types.v $(CHERI_COQ:%.v=%.vo) $(CHERI_COQ:%.v=%.glob) $(CHERI_COQ:%.v=.%.aux)
	-Holmake cleanAll
