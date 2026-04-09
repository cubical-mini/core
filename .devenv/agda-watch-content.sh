#!/bin/sh

$PROJECT_ROOT/.devenv/fswatch.sh --event Updated -or "$PROJECT_ROOT/src" | xargs -n1 "$PROJECT_ROOT/.devenv/agda-render.sh"
