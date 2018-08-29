THYS = Sail2_instr_kinds.thy Sail2_values.thy Sail2_operators.thy \
  Sail2_operators_mwords.thy Sail2_operators_bitlists.thy \
  Sail2_state_monad.thy Sail2_state.thy Sail2_state_lifting.thy \
  Sail2_prompt_monad.thy Sail2_prompt.thy \
  Sail2_string.thy
EXTRA_THYS = Sail2_state_monad_lemmas.thy Sail2_state_lemmas.thy \
  Sail2_prompt_monad_lemmas.thy \
  Sail2_operators_mwords_lemmas.thy Hoare.thy

RISCV_DIR = ../../riscv

.PHONY: all heap-img clean

all: thys

thys: $(THYS)

heap-img: thys $(EXTRA_THYS) ROOT
	@echo '*** To build a heap image with the Sail library, please'
	@echo '*** add this directory to your ROOTS file'
	@echo '*** (e.g. $$HOME/.isabelle/Isabelle<version>/ROOTS)'
	@echo '*** and add the isabelle binary to your PATH.'
	isabelle build -b Sail

manual: heap-img manual/Manual.thy manual/ROOT manual/document/root.tex
	cp output/document/session_graph.pdf manual/document/Sail_session_graph.pdf
	make -C $(RISCV_DIR) Riscv_duopod.thy
	isabelle build -d manual -d $(RISCV_DIR) Sail-Manual

Sail2_instr_kinds.thy: ../../src/lem_interp/sail2_instr_kinds.lem
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_values.thy: ../../src/gen_lib/sail2_values.lem Sail2_instr_kinds.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_operators.thy: ../../src/gen_lib/sail2_operators.lem Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_operators_mwords.thy: ../../src/gen_lib/sail2_operators_mwords.lem Sail2_operators.thy Sail2_prompt.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_operators_bitlists.thy: ../../src/gen_lib/sail2_operators_bitlists.lem Sail2_operators.thy Sail2_prompt.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_prompt_monad.thy: ../../src/gen_lib/sail2_prompt_monad.lem Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_prompt.thy: ../../src/gen_lib/sail2_prompt.lem Sail2_prompt_monad.thy Sail2_prompt_monad_lemmas.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_state_monad.thy: ../../src/gen_lib/sail2_state_monad.lem Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_state.thy: ../../src/gen_lib/sail2_state.lem Sail2_prompt.thy Sail2_state_monad.thy Sail2_state_monad_lemmas.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_state_lifting.thy: ../../src/gen_lib/sail2_state_lifting.lem Sail2_prompt.thy Sail2_state.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_string.thy: ../../src/gen_lib/sail2_string.lem Sail2_operators_mwords.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

clean:
	-rm $(THYS)
