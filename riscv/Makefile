SAIL_SRCS = prelude.sail riscv_types.sail riscv_sys.sail riscv.sail
SAIL_DIR ?= $(realpath ..)

export SAIL_DIR

all: riscv Riscv_embed_sequential.thy

check: $(SAIL_SRCS) main.sail
	$(SAIL_DIR)/sail $^

riscv: $(SAIL_SRCS) main.sail
	$(SAIL_DIR)/sail -ocaml -o riscv $^

riscv_duopod_ocaml: prelude.sail riscv_duopod.sail
	$(SAIL_DIR)/sail -ocaml -o $@ $^

riscv_duopod_embed_sequential.lem: prelude.sail riscv_duopod.sail
	$(SAIL_DIR)/sail -lem -lem_sequential -lem_mwords -lem_lib Riscv_extras_embed -o riscv_duopod $^
Riscv_duopod_embed_sequential.thy: riscv_duopod_embed_sequential.lem riscv_extras_embed_sequential.lem
	lem -isa -outdir . -lib ../src/lem_interp -lib ../src/gen_lib \
		riscv_extras_embed_sequential.lem \
		riscv_duopod_embed_types_sequential.lem \
		riscv_duopod_embed_sequential.lem

riscv_duopod: riscv_duopod_ocaml Riscv_duopod_embed_sequential.thy

Riscv_embed_sequential.thy: riscv_embed_sequential.lem riscv_extras_embed_sequential.lem
	lem -isa -outdir . -lib ../src/lem_interp -lib ../src/gen_lib \
		riscv_extras_embed_sequential.lem \
		riscv_embed_types_sequential.lem \
		riscv_embed_sequential.lem

riscv_embed_sequential.lem: $(SAIL_SRCS)
	$(SAIL_DIR)/sail -lem -o riscv -lem_sequential -lem_mwords -lem_lib Riscv_extras_embed $^

clean:
	-rm -rf riscv _sbuild
	-rm -f riscv_embed_sequential.lem riscv_embed_types_sequential.lem
	-rm -f Riscv_embed_sequential.thy Riscv_embed_types_sequential.thy \
		Riscv_extras_embed_sequential.thy
	-rm -f Riscv_duopod_embed_sequential.thy Riscv_duopod_embed_types_sequential.thy riscv_duopod_embed_sequential.lem riscv_duopod_embed_types_sequential.lem
