#!/bin/sh

PR=${PR:-$PWD}

fswatch --event Created --event Updated --event Removed --event Renamed -or "$PR/doc/trees" | xargs -n1 forest-rebuild.sh
