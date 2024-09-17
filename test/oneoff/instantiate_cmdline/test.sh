#!/bin/sh

set -e

sail xlen.sail --abstract-types --instantiate "xlen = 3 2" 2> xlen.result || true
diff xlen.result xlen.expect
