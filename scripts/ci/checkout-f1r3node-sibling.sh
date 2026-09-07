#!/usr/bin/env bash
# Check out the exact f1r3node revision used by MeTTaIL's path dependencies.

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
revision_file="$repo_root/.github/f1r3node-revision"
revision="$(tr -d '[:space:]' < "$revision_file")"
sibling_dir="${F1R3NODE_SIBLING_DIR:-$(dirname "$(dirname "$repo_root")")/f1r3node-rust-f1r3lang}"
repository_url="${F1R3NODE_REPOSITORY_URL:-https://github.com/F1R3FLY-io/f1r3node-rust.git}"

if [[ ! "$revision" =~ ^[0-9a-f]{40}$ ]]; then
    echo "invalid f1r3node revision in $revision_file: expected a full commit ID" >&2
    exit 2
fi

if [[ -e "$sibling_dir" ]]; then
    if ! git -C "$sibling_dir" rev-parse --git-dir >/dev/null 2>&1; then
        echo "refusing to replace non-repository sibling path: $sibling_dir" >&2
        exit 2
    fi

    actual="$(git -C "$sibling_dir" rev-parse HEAD)"
    if [[ "$actual" != "$revision" ]]; then
        echo "f1r3node sibling is at $actual, but CI requires $revision" >&2
        echo "refusing to mutate an existing checkout: $sibling_dir" >&2
        exit 2
    fi

    echo "f1r3node sibling already pinned at $revision"
    exit 0
fi

git init --quiet "$sibling_dir"
git -C "$sibling_dir" remote add origin "$repository_url"
git -C "$sibling_dir" fetch --quiet --depth=1 origin "$revision"
git -C "$sibling_dir" checkout --quiet --detach FETCH_HEAD

actual="$(git -C "$sibling_dir" rev-parse HEAD)"
if [[ "$actual" != "$revision" ]]; then
    echo "f1r3node checkout resolved to $actual, expected $revision" >&2
    exit 2
fi

echo "checked out f1r3node sibling at $revision"
