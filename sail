#!/bin/bash

SAIL_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export SAIL_DIR
# This would be nice, but concurrent tests are failing due to dune's global lock
#exec dune exec --root="$SAIL_DIR" --no-build --display=quiet --no-print-directory -- sail $*

# Where to find plugins
export DUNE_DIR_LOCATIONS="libsail:share:$SAIL_DIR/_build/install/default/share/libsail"
exec "$SAIL_DIR/_build/install/default/bin/sail" $*

