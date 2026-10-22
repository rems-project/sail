#!/bin/sh

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../../.." && pwd)
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/sail-rts-memory.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM

for source in rts sail sail_failure elf; do
  "${CC:-cc}" ${CFLAGS:-} -I"$root/lib" -c "$root/lib/$source.c" -o "$build_dir/$source.o"
done

"${CC:-cc}" ${CFLAGS:-} -I"$root/lib" "$here/test.c" "$build_dir/"*.o ${LDFLAGS:-} -lgmp -o "$build_dir/test"
(cd "$build_dir" && ./test)

# Also check that C++ consumers can use the public header and link to the C API.
"${CXX:-c++}" ${CXXFLAGS:-} -x c++ -I"$root/lib" -c "$here/test.c" -o "$build_dir/test-cxx.o"
"${CXX:-c++}" "$build_dir/test-cxx.o" "$build_dir/rts.o" "$build_dir/sail.o" \
  "$build_dir/sail_failure.o" "$build_dir/elf.o" ${LDFLAGS:-} -lgmp -o "$build_dir/test-cxx"
(cd "$build_dir" && ./test-cxx)
