#!/bin/sh

fswatch --event Created --event Updated --event Removed --event Renamed -or "doc/trees" | xargs -n1 forest-rebuild.sh
