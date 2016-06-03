all:
	cat preamble.tex ../mips_prelude.sail ../mips_wrappers.sail ../mips_insts.sail ../mips_epilogue.sail postamble.tex > mips_all.tex
	pdflatex mips_all.tex

clean:
	rm -rf *~
	rm -rf mips_all.*
