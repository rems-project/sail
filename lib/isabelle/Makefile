THYS = Sail_impl_base.thy Sail_values.thy Sail_operators.thy Sail_operators_mwords.thy State.thy Prompt.thy

.PHONY: all heap-img clean

all: heap-img

heap-img: $(THYS)
	@echo '*** To build a heap image with the Sail library, please'
	@echo '*** add the ROOT file in this directory to your ROOTS file'
	@echo '*** (e.g. $$HOME/.isabelle/Isabelle<version>/ROOTS)'
	@echo '*** and add the isabelle binary to your PATH.'
	isabelle build -b Sail

Sail_impl_base.thy: ../../src/lem_interp/sail_impl_base.lem
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail_values.thy: ../../src/gen_lib/sail_values.lem Sail_impl_base.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail_operators.thy: ../../src/gen_lib/sail_operators.lem Sail_values.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail_operators_mwords.thy: ../../src/gen_lib/sail_operators_mwords.lem Sail_values.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

State.thy: ../../src/gen_lib/state.lem Sail_values.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Prompt.thy: ../../src/gen_lib/prompt.lem Sail_values.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

clean:
	-rm $(THYS)
	-rm *Auxiliary.thy
