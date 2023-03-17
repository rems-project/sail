#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
# This would be nice, but concurrent tests are failing due to dune's global lock
#exec dune exec --root="$DIR" --no-build --display=quiet --no-print-directory -- sail $*

# Where to find plugins
export DUNE_DIR_LOCATIONS="libsail:share:$DIR/_build/install/default/share/libsail"
exec "$DIR/_build/install/default/bin/sail" $*

