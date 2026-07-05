#!/usr/bin/env bash
#
# publish-crates.sh - Publish workspace crates to crates.io in dependency order.
#
# Enumerates workspace members via `cargo metadata`, filters out those with
# `publish = false`, topologically sorts by intra-workspace dependencies, and
# publishes each with `cargo publish`.
#
# Requires CARGO_REGISTRY_TOKEN in the environment.
#
# Notes:
#   - Crates with `publish = false` are skipped (the current default for this
#     workspace). To publish a crate, remove `publish = false` from its
#     Cargo.toml AND ensure intra-workspace path deps carry explicit versions
#     (e.g. `mettail-runtime = { path = "../runtime", version = "0.1.0" }`).
#   - A short sleep between publishes gives the crates.io index time to pick
#     up newly published versions before publishing dependents.

set -euo pipefail

if [[ -z "${CARGO_REGISTRY_TOKEN:-}" ]]; then
    echo "::error::CARGO_REGISTRY_TOKEN not set"
    exit 1
fi

# Produce a newline-separated, topologically sorted list of publishable
# workspace member names. Exits 0 with empty output if none are publishable.
ordered_members() {
    local metadata
    metadata=$(cargo metadata --format-version 1 --no-deps)
    python3 <(cat <<'PY'
import json, sys
from collections import defaultdict, deque

m = json.load(sys.stdin)
members = {p["name"]: p for p in m["packages"] if p["id"] in m["workspace_members"]}

# Filter out publish = false. Cargo metadata reports `publish: null` when the
# crate is publishable (to any registry), and `publish: []` when publish=false.
publishable = {n for n, p in members.items() if p.get("publish") is None}

# Build intra-workspace dependency DAG, only among publishable members.
deps = defaultdict(set)
indeg = defaultdict(int)
for n in publishable:
    deps[n] = set()
    indeg[n] = 0
for n in publishable:
    for d in members[n].get("dependencies", []):
        if d.get("kind") in (None, "normal", "build") and d["name"] in publishable:
            if d["name"] not in deps[n]:
                deps[n].add(d["name"])
                indeg[n] += 1

# Kahn's algorithm.
ready = deque(sorted(n for n, c in indeg.items() if c == 0))
order = []
while ready:
    n = ready.popleft()
    order.append(n)
    for other in publishable:
        if n in deps[other]:
            deps[other].remove(n)
            indeg[other] -= 1
            if indeg[other] == 0:
                ready.append(other)

if len(order) != len(publishable):
    missing = set(publishable) - set(order)
    print(f"ERROR: dependency cycle among {missing}", file=sys.stderr)
    sys.exit(2)

for n in order:
    print(n)
PY
) <<<"$metadata"
}

members_output=$(ordered_members) || { echo "::error::Failed to determine publish order"; exit 1; }
mapfile -t TO_PUBLISH <<< "$members_output"
if [[ ${#TO_PUBLISH[@]} -eq 1 && -z "${TO_PUBLISH[0]}" ]]; then
    TO_PUBLISH=()
fi

if [[ ${#TO_PUBLISH[@]} -eq 0 ]]; then
    echo "[publish-crates] No publishable crates (all members have publish = false). Skipping."
    exit 0
fi

echo "[publish-crates] Will publish in order:"
for n in "${TO_PUBLISH[@]}"; do
    echo "  - $n"
done

for n in "${TO_PUBLISH[@]}"; do
    echo "[publish-crates] cargo publish -p $n"
    cargo publish -p "$n"
    # Give the index time to propagate before the next dependent publishes.
    sleep 15
done

echo "[publish-crates] Done."
