Installing Sail on Ubuntu
=========================

This note lists the commands needed to get Sail and all dependencies
working on a new Ubuntu install. I recently (2018-02-17) tested these
on Xubuntu 16.04 LTS in a virtual machine, so they should
work. Hopefully this will be useful as a reference.

Basics
------

First we need some basic packages if they're not already installed.
```
sudo apt-get install build-essential git
```

OCaml and sail expect some packages. m4 is for OPAM, libgmp-dev is for
zarith which most of our tools rely on. Sail uses Z3 as a constraint
solver.
```
sudo apt-get install m4 libgmp-dev z3
```

OCaml and OPAM
--------------

Install OPAM. Either directly from [https://opam.ocaml.org] or from
the package manager - both should work, but I used the install script
from the website. This should install OCaml 4.05.

We now need ocamlbuild, zarith, and menhir from OPAM.
```
opam install ocamlbuild
opam install zarith
opem install menhir
```

Ott
---

Before cloning the repositories you may need to set up ssh keys with
github or use https. Create a directory to install the various REMS
tools and cd into it.
```
git clone git@github.com:ott-lang/ott.git
cd ott
make
cd ..
```

Lem
---

```
git clone git@github.com:rems-project/lem.git
cd lem
make
cd ocaml-lib
make install
cd ../..
```

Linksem
-------

```
git clone git@github.com:rems-project/linksem.git
cd linksem
make && make install
```

Sail
----

Sail depends on lem and ott, so make sure lem and ott executables
exist in $PATH.
```
git clone git@github.com:rems-project/sail.git
cd sail
make
```
To build Sail with interactive support we need two more commands
```
opam install linenoise
make isail
```
To test Sail is installed correctly, execute the following from the
root directory of the sail repository. You may also need to set
$LEM_DIR to the root of the lem repository for the lem tests. Some of
the C backend tests will fail if valgrind isn't installed.
```
export SAIL_DIR=$PWD
test/run_tests.sh
```
