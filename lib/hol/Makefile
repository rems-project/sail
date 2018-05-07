LEMSRC =  \
  ../../src/lem_interp/sail_instr_kinds.lem \
  ../../src/gen_lib/sail_values.lem \
  ../../src/gen_lib/sail_operators.lem \
  ../../src/gen_lib/sail_operators_mwords.lem \
  ../../src/gen_lib/sail_operators_bitlists.lem \
  ../../src/gen_lib/state_monad.lem \
  ../../src/gen_lib/state.lem \
  prompt_monad.lem \
  prompt.lem

SCRIPTS = sail_instr_kindsScript.sml sail_valuesScript.sml sail_operatorsScript.sml \
  sail_operators_mwordsScript.sml sail_operators_bitlistsScript.sml \
  state_monadScript.sml stateScript.sml \
  prompt_monadScript.sml promptScript.sml

all: sail-heap

$(SCRIPTS): $(LEMSRC)
	lem -hol -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $(LEMSRC)

THYS = $(patsubst %Script.sml,%Theory.uo,$(SCRIPTS))

$(THYS) sail-heap: $(SCRIPTS)
	Holmake

# Holmake will also clear out the generated $(SCRIPTS) files
clean:
	Holmake cleanAll

.PHONY: all clean
