#!/bin/sh

$PROJECT_ROOT/.devenv/agda-gen-everything.sh
echo "Regenerated Everything.agda"

cd $PROJECT_ROOT/doc; agda --forest --forest-dir=trees/autogen --fhtml-dir=output/html Everything.agda
