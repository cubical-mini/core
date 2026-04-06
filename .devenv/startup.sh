#!/bin/sh

mkdir -p "$PROJECT_ROOT/doc/output"

tmux -f "$PROJECT_ROOT/.devenv/tmux.conf" new-session -d -t cm-devenv
tmux new-window -d -t cm-devenv:8 -n 'forest watch' "$PROJECT_ROOT/.devenv/forest-watch.sh"
tmux new-window -d -t cm-devenv:9 -n 'http server' 'warp -d doc/output'

exec tmux attach -t cm-devenv
