#!/bin/sh

mkdir -p $PWD/doc/output

tmux -f $PWD/.devenv/tmux.conf new-session -d -t cm-devenv
# tmux new-window -d -t cm-devenv:8 -n 'forester' 'TODO'
# tmux new-window -d -t cm-devenv:9 -n 'http server' 'warp -d doc/output'

exec tmux attach -t cm-devenv
