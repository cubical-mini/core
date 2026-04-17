#!/bin/sh

PR=${PR:-$PWD}

$PR/.devenv/fswatch.sh --event Created --event Removed --event Renamed -or "$PR/src" "$PR/extra" | xargs -n1 agda-gen-everything.sh
