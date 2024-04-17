#!/bin/sh

set -eu

# Verify `sail --version` matches `git describe`.
SAIL_VERSION="$(sail --version)"
GIT_DESCRIBE="Sail $(git describe --abbrev=0) ($(git rev-parse --abbrev-ref HEAD) @ $(git rev-parse HEAD))"

if [[ "$SAIL_VERSION" != "$GIT_DESCRIBE" ]]; then
    echo "Sail version not set correctly:"
    echo "sail --version: $SAIL_VERSION"
    echo "git describe: $GIT_DESCRIBE"
    exit 1
fi

export TEST_PAR=4

test/run_core_tests.sh
