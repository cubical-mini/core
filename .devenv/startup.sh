#!/bin/sh

mkdir -p "$PROJECT_ROOT/doc/output/html"
mkdir -p "$PROJECT_ROOT/doc/trees/autogen"

$PROJECT_ROOT/.devenv/agda-render.sh

tmux -f "$PROJECT_ROOT/.devenv/tmux.conf" new-session -d -t cm-devenv
tmux new-window -d -t cm-devenv:7 -n 'agda watch' "$PROJECT_ROOT/.devenv/agda-watch.sh"
tmux new-window -d -t cm-devenv:8 -n 'forest watch' "$PROJECT_ROOT/.devenv/forest-watch.sh"
tmux new-window -d -t cm-devenv:9 -n 'http server' 'warp -d doc/output'

exec tmux attach -t cm-devenv
