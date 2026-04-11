#!/bin/sh

rm -rf "$PROJECT_ROOT/doc/html"
mkdir -p "$PROJECT_ROOT/doc/html"
ln -s "$PROJECT_ROOT/theme/Agda.css" "$PROJECT_ROOT/doc/html/Agda.css"

rm -rf "$PROJECT_ROOT/output"
mkdir -p "$PROJECT_ROOT/output"
ln -s "$PROJECT_ROOT/doc/html/" "$PROJECT_ROOT/output/html"

rm -rf "$PROJECT_ROOT/doc/trees/autogen"
mkdir -p "$PROJECT_ROOT/doc/trees/autogen"

$PROJECT_ROOT/.devenv/agda-gen-everything.sh
$PROJECT_ROOT/.devenv/agda-render.sh
$PROJECT_ROOT/.devenv/forest-rebuild.sh

tmux -f "$PROJECT_ROOT/.devenv/tmux.conf" new-session -d -t cm-devenv
tmux new-window -d -t cm-devenv:6 -n 'agda watch str' "$PROJECT_ROOT/.devenv/agda-watch-structure.sh"
tmux new-window -d -t cm-devenv:7 -n 'agda watch con' "$PROJECT_ROOT/.devenv/agda-watch-content.sh"
tmux new-window -d -t cm-devenv:8 -n 'forest watch' "$PROJECT_ROOT/.devenv/forest-watch.sh"
tmux new-window -d -t cm-devenv:9 -n 'http server' "warp -d $PROJECT_ROOT/output"

exec tmux attach -t cm-devenv
