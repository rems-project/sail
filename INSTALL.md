# How to install Sail using opam

First, install opam (the OCaml package manager) if you haven't already. You can use your system's package
manager e.g. `sudo apt-get install opam` (on Ubuntu 20.04) or follow the [instructions
from the opam website](https://opam.ocaml.org/doc/Install.html).
The opam version must be >= 2.0; opam 1 versions are no longer supported. On older Ubuntu versions such as 18.04 you will not be able to use opam from the package manager, and will need to install it following the instructions on the opam website.

Use `ocaml -version` to check your OCaml version. If you have OCaml 4.08 or newer, that's fine, otherwise use `opam switch` to install 4.08:
```
opam switch create 4.06.1
```

and set up the environment for that OCaml version (note that older versions of opam suggest backticks instead of `$(...)`, but it makes no difference):
```
eval $(opam config env)
```
Install system dependencies, on Ubuntu (if using WSL see the note below):
```
sudo apt-get install build-essential libgmp-dev z3 pkg-config zlib1g-dev
```
or [MacOS homebrew](https://brew.sh/):
```
xcode-select --install # if you haven't already
brew install gmp z3 pkg-config
```
Finally, install sail from the opam package [https://opam.ocaml.org/packages/sail/](https://opam.ocaml.org/packages/sail/) and its dependencies:
```
opam install sail
```
If all goes well then you'll have sail in your path:
```
which sail
sail --help
```
Some source files that sail uses are found at ``opam config var sail:share`` (e.g. for ``$include <foo.sail>``) but sail should find those when it needs them.

### Note for WSL (Windows subsystem for Linux) users

The version of z3 that ships in the ubuntu repositories can be quite old, and we've had reports that this can cause issues when using Sail on WSL. On WSL we recommend downloading a recent z3 release from https://github.com/Z3Prover/z3/releases rather than installing it via apt-get.

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
