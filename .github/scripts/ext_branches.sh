#!/usr/bin/env bash
# Print the ext/* branches of the repository as a Markdown list, newest first:
# each with a link to the branch, to its deployed Coqdoc (relative: the list is
# spliced into the homepage at the root of the GitHub Pages site), the date of
# its last commit, and a description — the one line of `.github/ext-description`
# on that branch if it has one, else the subject of its last commit.  Branches are read from the remote, so the
# checkout needs `fetch-depth: 0` (or any clone that has them).
#
# Usage: ext_branches.sh [REMOTE]   (default: origin)
set -euo pipefail

remote="${1:-origin}"
repo="${GITHUB_REPOSITORY:-$(git remote get-url "$remote" | sed -E 's#(git@github\.com:|https://github\.com/)##; s#\.git$##')}"

git fetch --quiet --no-tags "$remote" '+refs/heads/ext/*:refs/remotes/'"$remote"'/ext/*' || true

git for-each-ref --sort=-committerdate \
    --format='%(refname:lstrip=3)%09%(committerdate:short)%09%(contents:subject)' \
    "refs/remotes/$remote/ext/" |
while IFS=$'\t' read -r branch date subject; do
  desc="$(git show "refs/remotes/$remote/$branch:.github/ext-description" 2>/dev/null | head -n 1 || true)"
  printf -- '- [`%s`](https://github.com/%s/tree/%s) ([Coqdoc](%s/dep.html)), last updated %s: %s\n' \
    "$branch" "$repo" "$branch" "$branch" "$date" "${desc:-$subject}"
done
