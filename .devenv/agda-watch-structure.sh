#!/bin/sh

.devenv/fswatch.sh --event Created --event Removed --event Renamed -or 'src' 'extra' | xargs -n1 agda-gen-everything.sh
