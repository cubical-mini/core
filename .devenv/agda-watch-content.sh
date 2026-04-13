#!/bin/sh

.devenv/fswatch.sh --event Updated -or 'src' 'extra' | xargs -n1 agda-render.sh
