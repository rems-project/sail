These are instructions for installing Sail via opam, the ocaml package manager.
The most up-to-date version of this document can be found on the Sail wiki

https://github.com/rems-project/sail/wiki/OPAMInstall

To build everything from source, instructions can be found here:

https://github.com/rems-project/sail/wiki/Building-from-Source

# How to install Sail from opam

Install opam if you haven't already: https://opam.ocaml.org/doc/Install.html

Use opam to install a version of ocaml we know works for us:
```
opam switch 4.06.1
```
OR, if you are using opam >=2.0, the syntax of the switch command changed slightly:
```
opam switch create ocaml-base-compiler.4.06.1
```

Then set up the environment for the ocaml we just installed:
```
eval `opam config env` 
```
Add our local opam repo:
```
opam repository add rems https://github.com/rems-project/opam-repository.git
```
Install system dependencies, on Ubuntu:
```
sudo apt-get install build-essential libgmp-dev z3
```
or homebrew:
```
brew install gmp z3
```
Install sail and its dependencies:
```
opam install sail
```
If all goes well then you'll have sail in your path:
```
which sail
sail --help
```
Some source files that sail uses are found in at ``opam config var sail:share`` (e.g. for ``$include <foo.sail>``) but sail should find those when it needs them.

### Installing development versions of Sail
Released Sail packages lag behind the latest development in the repository. If you find you need a recently added feature or bug fix you can use opam pin to install the latest version of Sail from the repository. Assuming you have previously followed the above instructions (required to install dependencies):
```
git clone https://github.com/rems-project/sail.git
cd sail
opam pin add sail .
```
will install from a local checkout of the Sail sources.

You can update with new changes as they are committed by pulling and reinstalling:
```
git pull
opam reinstall sail
```

To remove the pin and revert to the latest released opam package type:
```
opam pin remove sail
```

Alternatively you could follow the instructions to [build Sail manually](https://github.com/rems-project/sail/wiki/Building-from-Source), optionally skipping the steps to install ott, lem and linksem if they were already installed via opam.
