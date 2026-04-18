#!/bin/sh

PR=${PR:-$PWD}

$PR/.devenv/fswatch.sh --event Updated -or "$PR/src" "$PR/extra" | xargs -n1 agda-render.sh
