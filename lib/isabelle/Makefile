THYS = Sail_impl_base.thy Sail_values.thy Sail_operators.thy \
  State_monad.thy State.thy Prompt_monad.thy Prompt.thy
EXTRA_THYS = State_monad_extras.thy Prompt_monad_extras.thy

.PHONY: all heap-img clean

all: heap-img

heap-img: $(THYS) $(EXTRA_THYS) ROOT
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

State_monad.thy: ../../src/gen_lib/state_monad.lem Sail_values.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

State.thy: ../../src/gen_lib/state.lem State_monad.thy State_monad_extras.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Prompt_monad.thy: ../../src/gen_lib/prompt_monad.lem Sail_values.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Prompt.thy: ../../src/gen_lib/prompt.lem Prompt_monad.thy Prompt_monad_extras.thy
	lem -isa -outdir . -lib ../../src/lem_interp -lib ../../src/gen_lib $<

clean:
	-rm $(THYS)
	-rm *Auxiliary.thy
