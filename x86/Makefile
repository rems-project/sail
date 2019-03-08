SAIL=../src/sail.native
LEM:=../../lem/lem

SOURCES=../lib/regfp.sail x64.sail

all: x86.lem x86.ml x86_embed.lem

x86.lem:
	$(SAIL) -lem_ast -o x86 $(SOURCES)

x86.ml: x86.lem ../src/lem_interp/interp_ast.lem
	$(LEM) -ocaml -lib ../src/lem_interp/ $<

x86_embed.lem: $(SOURCES)
# also generates x86_embed_sequential.lem, x86_embed_types.lem, x86_toFromInterp.lem
	$(SAIL) -lem -lem_lib X86_extras_embed -o x86 $(SOURCES)

clean:
	rm -f x86.lem x86.ml
	rm -f x86_embed*.lem x86_toFromInterp.lem
