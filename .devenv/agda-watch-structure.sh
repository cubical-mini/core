#!/bin/sh

.devenv/fswatch.sh --event Created --event Removed --event Renamed -or "src" | xargs -n1 agda-gen-everything.sh
