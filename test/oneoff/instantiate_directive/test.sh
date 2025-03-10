#!/bin/sh

set -e

sail xlen.sail 2> xlen.result || true
diff xlen.result xlen.expect
