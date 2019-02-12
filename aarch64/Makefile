THIS_MAKEFILE := $(realpath $(lastword $(MAKEFILE_LIST)))
SAIL_DIR:=$(realpath $(dir $(THIS_MAKEFILE))..)
export SAIL_DIR
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
SAIL:=$(SAIL_DIR)/sail

aarch64.c: no_vector.sail
	$(SAIL) $(SAIL_FLAGS) $^ -c -O -undefined_gen -no_lexp_bounds_check -memo_z3 1> aarch64.c

aarch64_c: aarch64.c
	gcc -O2 $^ -o aarch64_c -lgmp -I $(SAIL_DIR)/lib

aarch64: no_vector.sail
	$(SAIL) $(SAIL_FLAGS) $^ -o aarch64 -ocaml -undefined_gen -no_lexp_bounds_check -memo_z3

aarch64_full: full.sail
	$(SAIL) $^ -o aarch64_full -ocaml -undefined_gen -no_lexp_bounds_check -memo_z3

aarch64.lem: no_vector.sail
	$(SAIL) $^ -o aarch64 -lem -lem_lib Aarch64_extras -memo_z3 -undefined_gen -no_lexp_bounds_check
aarch64_types.lem: aarch64.lem

Aarch64.thy: aarch64_extras.lem aarch64_types.lem aarch64.lem
	lem -isa -outdir . -lib Sail=$(SAIL_DIR)/src/gen_lib -lib Sail=$(SAIL_DIR)/src/lem_interp $^

clean:
	rm -rf _sbuild/
	rm -f aarch64
	rm -f aarch64.c
	rm -f aarch64.lem

LOC_FILES:=prelude.sail full/spec.sail decode_start.sail full/decode.sail decode_end.sail main.sail
include ../etc/loc.mk
