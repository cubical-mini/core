#!/bin/sh

fswatch -e 'swp$' -e '~$' --event Created --event Updated --event Removed --event Renamed -or "$PROJECT_ROOT/doc/trees" | xargs -n1 "$PROJECT_ROOT/.devenv/forest-rebuild.sh"
