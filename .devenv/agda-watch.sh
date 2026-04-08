#!/bin/sh

fswatch -l2 -e 'swp$' -e '~$' --event Created --event Updated --event Removed --event Renamed -or "$PROJECT_ROOT/src" "$PROJECT_ROOT/doc/README" | xargs -n1 "$PROJECT_ROOT/.devenv/agda-render.sh"
