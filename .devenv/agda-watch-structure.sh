#!/bin/sh

$PROJECT_ROOT/.devenv/fswatch.sh --event Created --event Removed --event Renamed -or "$PROJECT_ROOT/src" | xargs -n1 "$PROJECT_ROOT/.devenv/agda-gen-everything.sh"
