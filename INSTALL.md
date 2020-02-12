# How to install Sail using opam

First, install opam (the OCaml package manager) if you haven't already. You can use your system's package
manager e.g. `sudo apt-get install opam` or follow the [instructions
from the opam website](https://opam.ocaml.org/doc/Install.html).
Depending on your system and how you installed opam you may get either
opam version 1 or 2. Opam 1 is no longer officially supported but our
packages should work with either.

Use `ocaml -version` to check your OCaml version. If you do not have OCaml 4.06.1 or newer then use `opam switch` to install it e.g.:
```
opam switch 4.06.1
```
OR, if you are using opam >=2.0, the syntax of the switch command changed slightly:
```
opam switch create 4.06.1
```

Then set up the environment for the OCaml we just installed (note that older versions of opam suggest backticks instead of `$(...)`, but it makes no difference):
```
eval $(opam config env)
```
Add our local opam repo:
```
opam repository add rems https://github.com/rems-project/opam-repository.git
```
Install system dependencies, on Ubuntu:
```
sudo apt-get install build-essential libgmp-dev z3
```
or [MacOS homebrew](https://brew.sh/):
```
xcode-select --install # if you haven't already
brew install gmp z3 pkg-config
```
Finally, install sail and its dependencies:
```
opam install sail
```
If all goes well then you'll have sail in your path:
```
which sail
sail --help
```
Some source files that sail uses are found at ``opam config var sail:share`` (e.g. for ``$include <foo.sail>``) but sail should find those when it needs them.

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

Alternatively you could follow the instructions to [build Sail manually](BUILDING.md), optionally skipping the steps to install ott, lem and linksem if they were already installed via opam.
