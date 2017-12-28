
# Disable built-in make madness
MAKEFLAGS=-r
.SUFFIXES:

TESTS=div.sail

BITBUCKET_DIR:=$(realpath ../../../../)
LEM_DIR:=$(BITBUCKET_DIR)/lem
LEM:=$(LEM_DIR)/lem
SAIL_DIR:=$(BITBUCKET_DIR)/sail/src
SAIL:=$(SAIL_DIR)/sail.native
SAIL_VALUES:=$(SAIL_DIR)/gen_lib/sail_values.ml

BUILD_DIR:=_build

TESTS:=$(wildcard tests/*.sail)
OCAML_RESULTS:=$(addsuffix _embed.out,$(addprefix $(BUILD_DIR)/,$(notdir $(basename $(TESTS)))))
INTERP_RESULTS:=$(addsuffix _interp.out,$(addprefix $(BUILD_DIR)/,$(notdir $(basename $(TESTS)))))

all: tests.xml

clean:
	rm -rf $(BUILD_DIR) tests.xml

$(BUILD_DIR):
	mkdir -p $@

$(BUILD_DIR)/run_test_embed.ml: | $(BUILD_DIR)
	cp run_test_embed.ml $(BUILD_DIR)

$(BUILD_DIR)/run_test_interp.ml: | $(BUILD_DIR)
	cp run_test_interp.ml $(BUILD_DIR)

$(BUILD_DIR)/sail_values.ml: | $(BUILD_DIR)
	cp $(SAIL_VALUES) $(BUILD_DIR)

$(BUILD_DIR)/%_embed.out : tests/%.sail $(BUILD_DIR)/run_test_embed.ml $(BUILD_DIR)/sail_values.ml
	cd $(BUILD_DIR) && \
	$(SAIL) -ocaml ../test_prelude.sail ../$< ../test_epilogue.sail -o test && \
	ocamlfind ocamlopt -package zarith -linkpkg sail_values.ml test.ml run_test_embed.ml -o test_embed.native && \
	./test_embed.native > $(notdir $@)

$(BUILD_DIR)/%_interp.out : tests/%.sail $(BUILD_DIR)/run_test_interp.ml
	cd $(BUILD_DIR) && \
	$(SAIL) -lem_ast ../test_prelude.sail ../$< ../test_epilogue.sail -o test_lem_ast && \
	$(LEM) -ocaml test_lem_ast.lem -lib $(SAIL_DIR)/lem_interp && \
	ocamlfind ocamlopt -g -package num -package zarith -package lem -linkpkg -I $(SAIL_DIR)/_build/lem_interp $(SAIL_DIR)/_build/lem_interp/extract.cmxa test_lem_ast.ml run_test_interp.ml -o test_interp.native && \
	./test_interp.native >$(notdir $@) 2>&1

tests.xml: $(OCAML_RESULTS) $(INTERP_RESULTS)
	./test_to_junit.sh $^
