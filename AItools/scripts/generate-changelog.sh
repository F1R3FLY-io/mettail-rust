#!/usr/bin/env bash
#
# generate-changelog.sh - Generate CHANGELOG.md entries from git history.
#
# Parses conventional commit prefixes and groups into Keep a Changelog categories.
# Version comes from `workspace.package.version` in the root Cargo.toml (SemVer).
#
# Intended workflow: run locally on `dev` before opening a release PR. Bump the
# workspace version in Cargo.toml first, then run this to populate the matching
# changelog section. The release workflow on `main` reads the resulting section
# to build the GitHub Release body.
#
# Usage:
#   generate-changelog.sh                    # Update CHANGELOG.md for current workspace version
#   generate-changelog.sh --dry-run          # Print what would be generated (no file writes)
#   generate-changelog.sh --since <commit>   # Override the "previous release" commit
#   generate-changelog.sh --version X.Y.Z    # Override version (default: read from Cargo.toml)
#   generate-changelog.sh --verbose          # Show detailed progress
#   generate-changelog.sh --help / -h        # Usage
#
# Options:
#   --dry-run           Print output without writing files
#   --since COMMIT      Override the starting commit for the range
#   --version X.Y.Z     Override the target version
#   --verbose           Show detailed progress
#   --help, -h          Show this help message

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

CHANGELOG="$PROJECT_ROOT/CHANGELOG.md"
CARGO_TOML="$PROJECT_ROOT/Cargo.toml"

DRY_RUN=false
VERBOSE=false
SINCE=""
VERSION_OVERRIDE=""

if [[ -t 1 ]]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[0;33m'
    BLUE='\033[0;34m'
    NC='\033[0m'
else
    RED='' GREEN='' YELLOW='' BLUE='' NC=''
fi

log_info()    { echo -e "${BLUE}[INFO]${NC} $1"; }
log_ok()      { echo -e "${GREEN}[OK]${NC} $1"; }
log_warn()    { echo -e "${YELLOW}[WARN]${NC} $1" >&2; }
log_error()   { echo -e "${RED}[ERROR]${NC} $1" >&2; }
log_verbose() { [[ "$VERBOSE" == "true" ]] && echo -e "  $1" || true; }

usage() {
    sed -n '/^# Usage:/,/^#$/p' "$0" | sed 's/^# \?//'
    echo ""
    sed -n '/^# Options:/,/^[^#]/p' "$0" | sed '/^[^#]/d; s/^# \?//'
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run)    DRY_RUN=true; shift ;;
        --since)      SINCE="$2"; shift 2 ;;
        --version)    VERSION_OVERRIDE="$2"; shift 2 ;;
        --verbose)    VERBOSE=true; shift ;;
        --help|-h)    usage; exit 0 ;;
        *)            log_error "Unknown option: $1"; usage; exit 1 ;;
    esac
done

cd "$PROJECT_ROOT"

# Read workspace version from Cargo.toml [workspace.package] block.
read_workspace_version() {
    awk '
        /^\[workspace\.package\]/ { in_block=1; next }
        in_block && /^\[/         { in_block=0 }
        in_block && /^version[[:space:]]*=/ {
            # version = "X.Y.Z"
            match($0, /"[^"]+"/)
            if (RSTART > 0) {
                v = substr($0, RSTART+1, RLENGTH-2)
                print v
                exit
            }
        }
    ' "$CARGO_TOML"
}

if [[ -n "$VERSION_OVERRIDE" ]]; then
    VERSION="$VERSION_OVERRIDE"
else
    VERSION="$(read_workspace_version)"
fi

if [[ -z "$VERSION" ]]; then
    log_error "Could not read workspace.package.version from $CARGO_TOML"
    exit 1
fi

# Validate SemVer shape (allow pre-release / build metadata suffixes).
if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+([-+][0-9A-Za-z.-]+)?$ ]]; then
    log_error "Version '$VERSION' is not valid SemVer"
    exit 1
fi

TAG="v$VERSION"
log_info "Target version: $VERSION (tag: $TAG)"

# Determine commit range.
if [[ -n "$SINCE" ]]; then
    RANGE_START="$SINCE"
    log_info "Using --since override: $RANGE_START"
elif git describe --tags --abbrev=0 --match 'v*.*.*' HEAD 2>/dev/null 1>&2; then
    RANGE_START=$(git describe --tags --abbrev=0 --match 'v*.*.*' HEAD)
    log_info "Using latest SemVer tag: $RANGE_START"
else
    RANGE_START=$(git rev-list --max-parents=0 HEAD 2>/dev/null | head -1)
    log_info "No SemVer tags found; using root commit: ${RANGE_START:0:8}"
fi

COMMITS=$(git log --oneline "$RANGE_START"..HEAD 2>/dev/null || true)

if [[ -z "$COMMITS" ]]; then
    log_warn "No commits found in range ${RANGE_START:0:8}..HEAD"
    log_info "Nothing to generate"
    exit 0
fi

COMMIT_COUNT=$(echo "$COMMITS" | wc -l | tr -d ' ')
log_info "Found $COMMIT_COUNT commits since ${RANGE_START:0:8}"

# Categorize commits.
ADDED=""
CHANGED=""
FIXED=""
REMOVED=""

while IFS= read -r line; do
    msg="${line#* }"
    log_verbose "Processing: $msg"

    case "$msg" in
        feat\(*\):*|feat:*)
            entry="${msg#*: }"
            ADDED="${ADDED}${ADDED:+$'\n'}- ${entry}"
            ;;
        fix\(*\):*|fix:*)
            entry="${msg#*: }"
            FIXED="${FIXED}${FIXED:+$'\n'}- ${entry}"
            ;;
        docs\(*\):*|docs:*|chore\(*\):*|chore:*|refactor\(*\):*|refactor:*|test\(*\):*|test:*|ci\(*\):*|ci:*|style\(*\):*|style:*|perf\(*\):*|perf:*|build\(*\):*|build:*)
            entry="${msg#*: }"
            if echo "$entry" | grep -qi 'remov\|delet'; then
                REMOVED="${REMOVED}${REMOVED:+$'\n'}- ${entry}"
            else
                CHANGED="${CHANGED}${CHANGED:+$'\n'}- ${entry}"
            fi
            ;;
        *)
            # Non-conventional: tolerate and bucket under Changed (or Removed if keywords match).
            if echo "$msg" | grep -qi 'remov\|delet'; then
                REMOVED="${REMOVED}${REMOVED:+$'\n'}- ${msg}"
            else
                CHANGED="${CHANGED}${CHANGED:+$'\n'}- ${msg}"
            fi
            ;;
    esac
done <<< "$COMMITS"

# Build changelog block for the target version.
TODAY=$(date -u +%Y-%m-%d)
BLOCK="## [$VERSION] - $TODAY"$'\n'

if [[ -n "$ADDED" ]]; then
    BLOCK="$BLOCK"$'\n'"### Added"$'\n'"$ADDED"$'\n'
fi
if [[ -n "$CHANGED" ]]; then
    BLOCK="$BLOCK"$'\n'"### Changed"$'\n'"$CHANGED"$'\n'
fi
if [[ -n "$FIXED" ]]; then
    BLOCK="$BLOCK"$'\n'"### Fixed"$'\n'"$FIXED"$'\n'
fi
if [[ -n "$REMOVED" ]]; then
    BLOCK="$BLOCK"$'\n'"### Removed"$'\n'"$REMOVED"$'\n'
fi

if [[ "$DRY_RUN" == "true" ]]; then
    echo ""
    echo "=== CHANGELOG.md entry for [$VERSION] ==="
    echo "$BLOCK"
    exit 0
fi

CHANGELOG_HEADER="# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
"

if [[ -f "$CHANGELOG" ]]; then
    # Insert the new block after [Unreleased]. If an entry for this version
    # already exists, replace it (idempotent on re-run during the same release).
    TMPFILE=$(mktemp)
    trap "rm -f $TMPFILE" EXIT

    awk -v block="$BLOCK" -v target="## [$VERSION]" '
        BEGIN { in_old = 0 }
        # Emit new block right after [Unreleased] header.
        /^## \[Unreleased\]/ && !inserted {
            print
            printf "\n%s\n", block
            inserted = 1
            next
        }
        # If an old entry for this exact version exists, skip it until next ## heading.
        {
            if (index($0, target) == 1) { in_old = 1; next }
            if (in_old && $0 ~ /^## \[/) { in_old = 0 }
            if (!in_old) print
        }
    ' "$CHANGELOG" > "$TMPFILE"

    mv "$TMPFILE" "$CHANGELOG"
    trap - EXIT
else
    printf '%s\n%s\n' "$CHANGELOG_HEADER" "$BLOCK" > "$CHANGELOG"
fi

log_ok "Updated CHANGELOG.md [$VERSION] ($COMMIT_COUNT commits since ${RANGE_START:0:8})"
