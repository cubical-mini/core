#!/bin/sh

.devenv/fswatch.sh --event Updated -or "src" | xargs -n1 agda-render.sh
