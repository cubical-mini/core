#!/bin/sh

PR=${PR:-$PWD}

mkdir -p "$PR/doc/assets"

rm -rf "$PR/doc/trees/autogen"
mkdir -p "$PR/doc/trees/autogen"

rm -rf "$PR/output"
mkdir -p "$PR/output/core/html"

cp -f "$PR/theme/Agda.css" "$PR/output/core/html/"
