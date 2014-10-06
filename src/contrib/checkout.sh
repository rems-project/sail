#!/bin/sh

test -d batteries-included || (git clone https://github.com/ocaml-batteries-team/batteries-included.git && \
    cd batteries-included && git checkout release-2.2.0)
(cd batteries-included && make all)

test -d bitstring || (git clone https://code.google.com/p/bitstring/ && \
	cd bitstring && git checkout master)
(cd bitstring && (test -e config.h || (aclocal && autoreconf && ./configure)) && make srcdir='$(top_srcdir)' )

# To fix "-fno-defer-pop" build problem on Mac OS, brew install gcc
# and make sure "gcc" runs the brew version (not clang). Or get ocaml
# 4.01.0 via opam, which avoids this problem.
test -d uint || (git clone https://github.com/andrenth/ocaml-uint.git && \
	cd ocaml-uint && git checkout 1.1.x)
(cd ocaml-uint && make configure && make)
