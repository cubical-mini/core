#!/bin/bash

set -euo pipefail

gather() {
  local dir=$1
  local ext=$2

  find "$dir" -type f -name "*.$ext" | \
    grep -v 'Everything' | sort | \
    sed -re "s@.*$dir/@@g;s@.$ext@@g;s@/@.@g;s@^@open import @g;s@\$@@g" \
    >> "$tmp_file" \
  || echo "No $ext files found in $dir"
}

tmp_file="$(mktemp)"
trap 'rm -f "$tmp_file"' EXIT

echo "module Everything where" > "$tmp_file"

ds=('src' 'extra')
es=('agda' 'lagda.tree')
for d in "${ds[@]}"; do
  for e in "${es[@]}"; do
    gather $d $e
  done
done

EFILE=src/Everything.agda

if [ ! -f "$EFILE" ] || ! cmp -s "$tmp_file" "$EFILE"; then
  mv "$tmp_file" "$EFILE"
else
  rm -f "$tmp_file"
fi

echo "Regenerated Everything.agda"
