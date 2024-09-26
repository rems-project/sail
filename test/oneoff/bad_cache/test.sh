#!/bin/sh

set -e

rm -f bad_cache.result z3_problems
echo -n -e 7fcba3a13c51ab2786c5b710e80c5f88\\x05 > z3_problems
sail --memo-z3 2> bad_cache.result || true
diff bad_cache.result bad_cache.expect
