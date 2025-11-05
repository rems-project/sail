#!/bin/sh

set -e

if sail --require-version 0.20.2; then
    exit 1;
else
    exit 0;
fi
