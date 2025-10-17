#!/bin/sh

set -e

rm -f bad_cache.result sail_smt_cache
echo -n -e 7fcba3a13c51ab2786c5b710e80c5f88\\x05 > sail_smt_cache
sail --memo-z3 2> bad_cache.result || true
diff bad_cache.result bad_cache.expect
