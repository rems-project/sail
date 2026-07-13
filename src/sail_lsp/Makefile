.PHONY: sail_lsp install

# --release implies --root .
sail_lsp:
	dune build --release

install: sail_lsp
	dune install --root .
