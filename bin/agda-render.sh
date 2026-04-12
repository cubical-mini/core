#!/bin/sh

mkdir -p doc/trees/autogen
mkdir -p output/html

agda --forest --forest-dir="doc/trees/autogen" --fhtml-dir="output/html" "src/Everything.agda"
