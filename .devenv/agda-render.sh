#!/bin/sh

agda --forest --forest-dir="$PROJECT_ROOT/doc/trees/autogen" --fhtml-dir="$PROJECT_ROOT/doc/html" "$PROJECT_ROOT/src/Everything.agda"
rm -rf "$PROJECT_ROOT/output/html"
cp -R "$PROJECT_ROOT/doc/html" "$PROJECT_ROOT/output/html"
