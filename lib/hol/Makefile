LEM_DIR?=$(shell opam config var lem:share)

LEMLINKPRE = \
  sail2_instr_kinds.lem \
  sail2_values.lem \
  sail2_operators.lem \
  sail2_operators_mwords.lem \
  sail2_operators_bitlists.lem \
  sail2_state_monad.lem \
  sail2_state.lem \
  sail2_string.lem \
  sail2_monadic_combinators.lem

LEMLINKPOST = \
  sail2_monadic_combinators.lem

LEMSRC =  \
  $(LEMLINKPRE) \
  sail2_prompt_monad.lem \
  sail2_prompt.lem \
  sail2_undefined.lem \
  sail2_concurrency_interface.lem \
  sail2_concurrency_interface_mwords.lem \
  sail2_concurrency_interface_bitlists.lem \
  sail2_undefined_concurrency_interface.lem \
  $(LEMLINKPOST)

SCRIPTS = sail2_instr_kindsScript.sml sail2_valuesScript.sml sail2_operatorsScript.sml \
  sail2_operators_mwordsScript.sml sail2_operators_bitlistsScript.sml \
  sail2_state_monadScript.sml sail2_stateScript.sml \
  sail2_prompt_monadScript.sml sail2_promptScript.sml sail2_undefinedScript.sml \
  sail2_stringScript.sml sail2_concurrency_interfaceScript.sml \
  sail2_concurrency_interface_mwordsScript.sml sail2_concurrency_interface_bitlistsScript.sml \
  sail2_undefined_concurrency_interfaceScript.sml sail2_monadic_combinatorsScript.sml

THYS = $(patsubst %Script.sml,%Theory.uo,$(SCRIPTS))

all: sail-heap $(THYS)
all-scripts: $(SCRIPTS)

$(LEMLINKPRE): $(addprefix ../../src/gen_lib/,$(LEMLINKPRE))
	set -e; \
	for f in $(LEMLINKPRE); do \
	  ln -snf ../../src/gen_lib/$$f; \
	done

$(LEMLINKPOST): $(addprefix ../../src/gen_lib/,$(LEMLINKPOST))
	set -e; \
	for f in $(LEMLINKPOST); do \
	  ln -snf ../../src/gen_lib/$$f; \
	done

$(SCRIPTS): $(LEMSRC)
	set -e; \
	for f in $(LEMSRC); do \
	  lem -hol -outdir . -auxiliary_level none -lib . $$f; \
	done

$(THYS) sail-heap: $(SCRIPTS)
	LEM_DIR=$(LEM_DIR) Holmake

# Holmake will also clear out the generated $(SCRIPTS) files
clean:
	rm -f $(LEMLINKPRE) $(LEMLINKPOST)
	Holmake cleanAll

.PHONY: all all-scripts clean
