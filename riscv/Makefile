SAIL_SRCS = prelude.sail riscv_types.sail riscv_sys.sail riscv_platform.sail riscv_mem.sail riscv_vmem.sail riscv.sail riscv_step.sail riscv_analysis.sail
PLATFORM_OCAML_SRCS = platform.ml platform_impl.ml platform_main.ml
SAIL_DIR ?= $(realpath ..)
SAIL ?= $(SAIL_DIR)/sail

export SAIL_DIR

all: platform Riscv.thy

check: $(SAIL_SRCS) main.sail Makefile
	$(SAIL) $(SAIL_FLAGS) $(SAIL_SRCS) main.sail

_sbuild/riscv.ml: $(SAIL_SRCS) Makefile main.sail
	$(SAIL) $(SAIL_FLAGS) -ocaml -ocaml-nobuild -o riscv $(SAIL_SRCS)

_sbuild/platform_main.native: _sbuild/riscv.ml _tags $(PLATFORM_OCAML_SRCS) Makefile
	cp _tags $(PLATFORM_OCAML_SRCS) _sbuild
	cd _sbuild && ocamlbuild -use-ocamlfind platform_main.native

_sbuild/coverage.native: _sbuild/riscv.ml _tags.bisect $(PLATFORM_OCAML_SRCS) Makefile
	cp $(PLATFORM_OCAML_SRCS) _sbuild
	cp _tags.bisect _sbuild/_tags
	cd _sbuild && ocamlbuild -use-ocamlfind platform_main.native && cp -L platform_main.native coverage.native

platform: _sbuild/platform_main.native
	rm -f $@ && ln -s $^ $@

coverage: _sbuild/coverage.native
	rm -f platform && ln -s $^ platform # since the test scripts runs this file
	rm -rf bisect*.out bisect coverage
	../test/riscv/run_tests.sh # this will generate bisect*.out files in this directory
	mkdir bisect && mv bisect*.out bisect/
	mkdir coverage && bisect-ppx-report -html coverage/ -I _sbuild/ bisect/bisect*.out

riscv.c: $(SAIL_SRCS) Makefile
	$(SAIL) -O -memo_z3 -c $(SAIL_SRCS) 1> $@

latex: $(SAIL_SRCS) Makefile
	$(SAIL) -latex -latex_prefix sail -o sail_ltx $(SAIL_SRCS)

tracecmp: tracecmp.ml
	ocamlfind ocamlopt -annot -linkpkg -package unix $^ -o $@

riscv_duopod_ocaml: prelude.sail riscv_duopod.sail
	$(SAIL) $(SAIL_FLAGS) -ocaml -o $@ $^

riscv_duopod.lem: prelude.sail riscv_duopod.sail
	$(SAIL) $(SAIL_FLAGS) -lem -lem_mwords -lem_lib Riscv_extras -o riscv_duopod $^
Riscv_duopod.thy: riscv_duopod.lem riscv_extras.lem
	lem -isa -outdir . -lib Sail=../src/lem_interp -lib Sail=../src/gen_lib \
		riscv_extras.lem \
		riscv_duopod_types.lem \
		riscv_duopod.lem

riscv_duopod: riscv_duopod_ocaml Riscv_duopod.thy

Riscv.thy: riscv.lem riscv_extras.lem
	lem -isa -outdir . -lib Sail=../src/lem_interp -lib Sail=../src/gen_lib \
		riscv_extras.lem \
		riscv_types.lem \
		riscv.lem
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' Riscv_types.thy

riscv.lem: $(SAIL_SRCS) Makefile
	$(SAIL) $(SAIL_FLAGS) -lem -o riscv -lem_mwords -lem_lib Riscv_extras $(SAIL_SRCS)

riscv_sequential.lem: $(SAIL_SRCS) Makefile
	$(SAIL_DIR)/sail -lem -lem_sequential -o riscv_sequential -lem_mwords -lem_lib Riscv_extras_sequential $(SAIL_SRCS)

riscvScript.sml : riscv.lem riscv_extras.lem
	lem -hol -outdir . -lib ../lib/hol -i ../lib/hol/sail2_prompt_monad.lem -i ../lib/hol/sail2_prompt.lem \
	    -lib ../src/lem_interp -lib ../src/gen_lib \
		riscv_extras.lem \
		riscv_types.lem \
		riscv.lem

riscvTheory.uo riscvTheory.ui: riscvScript.sml
	Holmake riscvTheory.uo

COQ_LIBS = -R ../../bbv/theories bbv -R ../lib/coq Sail

riscv.v riscv_types.v: $(SAIL_SRCS)
	$(SAIL) $(SAIL_FLAGS) -dcoq_undef_axioms -coq -o riscv -coq_lib riscv_extras $(SAIL_SRCS)
riscv_duopod.v riscv_duopod_types.v:  prelude.sail riscv_duopod.sail
	$(SAIL) $(SAIL_FLAGS) -dcoq_undef_axioms -coq -o riscv_duopod -coq_lib riscv_extras $^
%.vo: %.v
	coqc $(COQ_LIBS) $<
riscv.vo: riscv_types.vo riscv_extras.vo
riscv_duopod.vo: riscv_duopod_types.vo riscv_extras.vo

# we exclude prelude.sail here, most code there should move to sail lib
LOC_FILES:=$(SAIL_SRCS) main.sail
include ../etc/loc.mk

clean:
	-rm -rf riscv _sbuild
	-rm -f riscv.lem riscv_types.lem
	-rm -f Riscv.thy Riscv_types.thy \
		Riscv_extras.thy
	-rm -f Riscv_duopod.thy Riscv_duopod_types.thy riscv_duopod.lem riscv_duopod_types.lem
	-rm -f riscvScript.sml riscv_typesScript.sml riscv_extrasScript.sml
	-rm -f platform_main.native platform coverage.native
	-rm -f riscv.vo riscv_types.vo riscv_extras.vo riscv.v riscv_types.v
	-rm -f riscv_duopod.vo riscv_duopod_types.vo riscv_duopod.v riscv_duopod_types.v
	-Holmake cleanAll
	ocamlbuild -clean
