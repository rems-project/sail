#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
exec dune exec --root="$DIR" --no-build --display=quiet --no-print-directory -- sail $*
