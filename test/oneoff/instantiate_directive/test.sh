#!/bin/sh

set -e

sail xlen.sail --abstract-types 2> xlen.result || true
diff xlen.result xlen.expect
