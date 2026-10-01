#!/usr/bin/env bash
# Render README.md as the homepage, into DEST/index.html, with the list of
# ext/* branches filled in between the markers of its "Branches" section.
#
# Usage: build_homepage.sh DEST [REMOTE]
set -euo pipefail

dest="$1"
remote="${2:-origin}"
here="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$dest"

list="$(mktemp)"
"$here/ext_branches.sh" "$remote" > "$list"

# Splice the list between the markers, and make the Coqdoc link relative, since
# the README *is* the deployed index.
awk -v list="$list" '
  /<!-- ext-branches:begin -->/ { print; while ((getline line < list) > 0) print line; skip = 1; next }
  /<!-- ext-branches:end -->/   { skip = 0 }
  !skip { print }
' README.md |
  sed 's!\[Coqdoc\](https://[A-Za-z0-9.-]*\.github\.io/McTT/dep\.html)![Coqdoc](dep.html)!' > "$dest/README.md"

pandoc "$dest/README.md" -H assets/include.html --no-highlight \
  --metadata pagetitle='McTT: Building A Correct-By-Construction Proof Checkers For Type Theories' \
  -t html --css styling.css -o "$dest/index.html"
rm -f "$dest/README.md" "$list"
