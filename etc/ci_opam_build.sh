#!/bin/sh

set -eu

opam init -y --no-setup --compiler=4.07 --shell=sh

eval `opam config env`

opam repository -y add rems https://github.com/rems-project/opam-repository.git
opam pin -y add sail .
opam install -y -v sail
sail -v
