#!/bin/sh

set -eu

export OPAMVERBOSE=2

opam init -y --no-setup --compiler=4.10.0 --shell=sh

eval `opam config env`

opam repository -y add rems https://github.com/rems-project/opam-repository.git
opam pin -y add .
opam install -y -v sail
sail -v
