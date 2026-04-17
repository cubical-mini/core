#!/bin/sh

PR=${PR:-$PWD}

agda --forest --forest-dir="$PR/doc/trees/autogen" --fhtml-dir="$PR/output/core/html" --html-prefix='..' "$PR/src/Everything.agda"
