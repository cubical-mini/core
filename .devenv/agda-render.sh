#!/bin/sh

find "$PROJECT_ROOT/doc/html/" -type f -name '*.html' -delete || echo "No generated HTML found"
agda --forest --forest-dir="$PROJECT_ROOT/doc/trees/autogen" --fhtml-dir="$PROJECT_ROOT/doc/html" "$PROJECT_ROOT/src/Everything.agda"
