
# Disable built-in make madness
MAKEFLAGS=-r
.SUFFIXES:

TESTS=div.sail

BITBUCKET_DIR:=$(realpath ../../../../)
LEM_DIR:=$(BITBUCKET_DIR)/lem
LEM:=$(LEM_DIR)/lem
LEMLIB = $(LEM_DIR)/ocaml-lib
SAIL_DIR:=$(BITBUCKET_DIR)/sail/src
SAIL:=$(SAIL_DIR)/sail.native
ZARITH_DIR:=$(LEM_DIR)/ocaml-lib/dependencies/zarith
ZARITH_LIB:=$(ZARITH_DIR)/zarith.cmxa
SAIL_VALUES:=$(SAIL_DIR)/gen_lib/sail_values.ml

BUILD_DIR:=_build

$(BUILD_DIR):
	mkdir -p $@

ocaml: | $(BUILD_DIR)
	cp test_lib.sail $(SAIL_VALUES) run_test_embed.ml $(BUILD_DIR)
	cd $(BUILD_DIR) && \
	$(SAIL) -ocaml test_lib.sail -o test && \
	ocamlopt -I $(ZARITH_DIR) $(ZARITH_LIB) sail_values.ml test.ml run_test_embed.ml -o test_embed.native && \
	./test_embed.native > test_embed.out && \
	../test_to_junit.sh < test_embed.out

interp: | $(BUILD_DIR)
	cp test_lib.sail $(BUILD_DIR) && \
	cp run_test_interp.ml $(BUILD_DIR) && \
	cd $(BUILD_DIR) && \
	$(SAIL) -lem_ast test_lib.sail -o test_lem_ast && \
	$(LEM) -ocaml test_lem_ast.lem -lib $(SAIL_DIR)/lem_interp && \
	ocamlfind ocamlopt -g -package num -I $(ZARITH_DIR)  -I $(SAIL_DIR)/_build/lem_interp -I $(LEMLIB) -linkpkg $(ZARITH_LIB) $(LEMLIB)/extract.cmxa  $(SAIL_DIR)/_build/lem_interp/extract.cmxa test_lem_ast.ml run_test_interp.ml -o test_interp.native && \
	./test_interp.native

all:
	true
