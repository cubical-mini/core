#!/bin/sh

PR=${PR:-$PWD}

prepare-output.sh
agda-gen-everything.sh
agda-render.sh
forest-rebuild.sh

tmux -f "$PR/.devenv/tmux.conf" new-session -d -t cm-devenv
tmux new-window -d -t cm-devenv:6 -n 'agda watch str' "$PR/.devenv/agda-watch-structure.sh"
tmux new-window -d -t cm-devenv:7 -n 'agda watch con' "$PR/.devenv/agda-watch-content.sh"
tmux new-window -d -t cm-devenv:8 -n 'forest watch' "$PR/.devenv/forest-watch.sh"
tmux new-window -d -t cm-devenv:9 -n 'http server' 'warp -d output'

exec tmux attach -t cm-devenv
