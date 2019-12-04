Building Sail on Ubuntu and macOS
=========================

This note lists the commands needed to get Sail and all dependencies
working and built from source on a new Ubuntu install or macOS. We
have recently (2018-02-17) tested these on Xubuntu 16.04 LTS in a
virtual machine and on macOS Sierra 10.12.6, so they should
work. Hopefully this will be useful as a reference.

For most users, installing and building the dependencies using OPAM is
likely easier than building everything manually, see [INSTALL.md].

Basics
------

First we need some basic packages if they're not already installed.

For Ubuntu:
```
sudo apt-get install build-essential git
```

For macOS: compilers and supporting utilities are called Xcode instead of build-essential. First, download Xcode from the Mac App Store, and then run the following in the terminal:
```
xcode-select --install
```
git can be installed using ```brew install git```

OCaml and sail expect some packages. m4 is for OPAM, libgmp-dev is for
zarith which most of our tools rely on. Sail uses Z3 as a constraint
solver.
```
sudo apt-get install m4 libgmp-dev z3
```
For macOS: ```brew install m4 gmp z3``` 

OCaml and OPAM
--------------

Install OPAM. Either directly from [https://opam.ocaml.org] or from
the package manager - both should work, but we used the install script
from the website. ```opam init``` must be run after installing OPAM.

Distributions often contain quite outdated OCaml packages, so we need to make sure that we use an up-to-date OCaml compiler with opam:
```
opam switch 4.06.1
```
For opam versions >=2.0 the command syntax for opam switch is slightly different:
```
opam switch create ocaml-base-compiler.4.06.1
```
After doing opam switch it is important to check that the ocaml tools in your $PATH point at the opam installed toolchain, rather than any installed by the distribution package manager.

The `opam` file in the Sail repository specifies the required dependencies:
```
depends: [
  "ocamlfind"
  "ocamlbuild"
  "zarith"
  "menhir"
  "linenoise" {>= "1.1.0"}
  "ott" {>= "0.28"}
  "lem" {>= "2018-12-14"}
  "linksem" {>= "0.3"}
  "omd"
  "conf-gmp"
  "conf-zlib"
  "base64" {< "3.0.0"}
  "yojson"
]
```
each of which can be installed using `opam install`. The `opam pin` command can be used to select a specific version of a dependency.

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
Sail depends on ott, so add the ott executable (``` path-to-ott/bin```) in the $PATH.


Lem
---

If you are using OCaml 4.06, you'll need to run `opam install num` before building lem.

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

Before installing linksem, we are required to set the LEMLIB environment variable and to put the lem executable in $PATH. LEMLIB should be the library directory within the checked-out lem directory (i.e. ```path-to-lem/library/```). Next, install linksem as

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