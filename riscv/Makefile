SAIL_SRCS = prelude.sail riscv_types.sail riscv_mem.sail riscv_sys.sail riscv_vmem.sail riscv.sail
SAIL_DIR ?= $(realpath ..)

export SAIL_DIR

all: riscv Riscv.thy

check: $(SAIL_SRCS) main.sail Makefile
	$(SAIL_DIR)/sail $(SAIL_SRCS) main.sail

riscv: $(SAIL_SRCS) main.sail Makefile
	$(SAIL_DIR)/sail -ocaml -o riscv $(SAIL_SRCS) main.sail

riscv_duopod_ocaml: prelude.sail riscv_duopod.sail
	$(SAIL_DIR)/sail -ocaml -o $@ $^

riscv_duopod.lem: prelude.sail riscv_duopod.sail
	$(SAIL_DIR)/sail -lem -lem_mwords -lem_lib Riscv_extras -o riscv_duopod $^
Riscv_duopod.thy: riscv_duopod.lem riscv_extras.lem
	lem -isa -outdir . -lib ../src/lem_interp -lib ../src/gen_lib \
		riscv_extras.lem \
		riscv_duopod_types.lem \
		riscv_duopod.lem

riscv_duopod: riscv_duopod_ocaml Riscv_duopod.thy

Riscv.thy: riscv.lem riscv_extras.lem
	lem -isa -outdir . -lib ../src/lem_interp -lib ../src/gen_lib \
		riscv_extras.lem \
		riscv_types.lem \
		riscv.lem
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' Riscv_types.thy

riscv.lem: $(SAIL_SRCS) Makefile
	$(SAIL_DIR)/sail -lem -o riscv -lem_mwords -lem_lib Riscv_extras $(SAIL_SRCS)

clean:
	-rm -rf riscv _sbuild
	-rm -f riscv.lem riscv_types.lem
	-rm -f Riscv.thy Riscv_types.thy \
		Riscv_extras.thy
	-rm -f Riscv_duopod.thy Riscv_duopod_types.thy riscv_duopod.lem riscv_duopod_types.lem
