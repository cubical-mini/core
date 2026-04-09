#!/bin/sh

fswatch -e '[0-9]+' -e 'swp$' -e 'swx$' -e '~$' -e '.#.*$' "$@"
