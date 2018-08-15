default_target: all

COQMAKEFILE=$(COQBIN)coq_makefile

all: Makefile.coq
	$(MAKE) -f Makefile.coq

doc: all
	$(MAKE) -f Makefile.coq html

html: doc

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf _CoqProject

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

_CoqProject::
	rm -f _CoqProject
	echo "-Q theories bbv" > _CoqProject
	find theories -type f -name '*.v' | sort >> _CoqProject
