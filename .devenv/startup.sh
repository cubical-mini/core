#!/bin/sh

prepare-output.sh
agda-gen-everything.sh
agda-render.sh
forest-rebuild.sh

tmux -f ".devenv/tmux.conf" new-session -d -t cm-devenv
tmux new-window -d -t cm-devenv:6 -n 'agda watch str' ".devenv/agda-watch-structure.sh"
tmux new-window -d -t cm-devenv:7 -n 'agda watch con' ".devenv/agda-watch-content.sh"
tmux new-window -d -t cm-devenv:8 -n 'forest watch' ".devenv/forest-watch.sh"
tmux new-window -d -t cm-devenv:9 -n 'http server' "warp -d output"

exec tmux attach -t cm-devenv
