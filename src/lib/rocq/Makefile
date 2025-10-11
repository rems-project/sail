.PHONY: extraction

extraction: CoqMakefile
	$(MAKE) -f CoqMakefile -B

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile
