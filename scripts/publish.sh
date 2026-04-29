#!/usr/bin/env bash
# Bump the workspace version, commit, tag, and push.
#
# Usage: scripts/publish.sh <patch|minor|major>
#
# The push of the `vX.Y.Z` tag triggers .github/workflows/publish.yml,
# which performs the actual `cargo publish` to crates.io. This script
# only handles the local version bump + git tag/push.
#
# Preconditions:
#   - clean working tree
#   - on branch `main`
#   - local `main` not behind `origin/main`
#   - tag `vX.Y.Z` does not already exist

set -euo pipefail

usage() {
    cat >&2 <<EOF
Usage: $0 <patch|minor|major>

  patch   X.Y.Z -> X.Y.(Z+1)
  minor   X.Y.Z -> X.(Y+1).0
  major   X.Y.Z -> (X+1).0.0
EOF
    exit 2
}

[[ $# -eq 1 ]] || usage
bump="$1"
case "$bump" in
    patch | minor | major) ;;
    *) usage ;;
esac

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$script_dir/.."

# --- rollback trap -----------------------------------------------------------
# Snapshot HEAD before any mutations. The trap restores both git state and
# working-tree files (Cargo.toml, Cargo.lock) to the pre-script state if
# anything fails between arming and disarming.

original_head="$(git rev-parse HEAD)"
rollback_armed=0
tag=""

rollback() {
    local rc=$?
    trap - EXIT
    if [[ $rollback_armed -eq 1 && $rc -ne 0 ]]; then
        echo "" >&2
        echo "error: aborting; rolling back local changes" >&2
        if [[ -n "$tag" ]]; then
            git tag -d "$tag" >/dev/null 2>&1 || true
        fi
        git reset --hard "$original_head" >/dev/null 2>&1 || true
    fi
    exit $rc
}
trap rollback EXIT

# --- safety checks -----------------------------------------------------------

if [[ -n "$(git status --porcelain)" ]]; then
    echo "error: working tree is dirty; commit or stash first" >&2
    exit 1
fi

branch="$(git rev-parse --abbrev-ref HEAD)"
if [[ "$branch" != "main" ]]; then
    echo "error: must be on 'main' (currently on '$branch')" >&2
    exit 1
fi

git fetch --quiet origin main || true
if [[ -n "$(git log HEAD..origin/main --oneline 2>/dev/null || true)" ]]; then
    echo "error: local 'main' is behind 'origin/main'; run 'git pull --ff-only' first" >&2
    exit 1
fi

# --- compute new version -----------------------------------------------------

current="$(grep -E '^version = "[0-9]+\.[0-9]+\.[0-9]+"' Cargo.toml | head -n 1 | sed -E 's/.*"([^"]+)".*/\1/')"
if [[ -z "${current:-}" ]]; then
    echo "error: could not parse current version from Cargo.toml" >&2
    exit 1
fi

IFS='.' read -r maj min pat <<< "$current"
case "$bump" in
    patch) pat=$((pat + 1)) ;;
    minor) min=$((min + 1)); pat=0 ;;
    major) maj=$((maj + 1)); min=0; pat=0 ;;
esac
new="${maj}.${min}.${pat}"
tag="v${new}"

if git rev-parse -q --verify "refs/tags/${tag}" >/dev/null; then
    echo "error: tag ${tag} already exists" >&2
    exit 1
fi

echo "current: ${current}"
echo "new:     ${new}"
echo "tag:     ${tag}"
read -r -p "proceed? [y/N] " ans
[[ "$ans" =~ ^[Yy]$ ]] || { echo "aborted"; exit 0; }

# --- bump version in Cargo.toml ----------------------------------------------
# The literal `version = "${current}"` appears in [workspace.package] and in
# the soroban-ret path dependency under [workspace.dependencies]. Replace both.
# From here on, the trap will roll back on any failure.

rollback_armed=1

sed -i.bak "s|version = \"${current}\"|version = \"${new}\"|g" Cargo.toml
rm -f Cargo.toml.bak

if grep -q "version = \"${current}\"" Cargo.toml; then
    echo "error: stale version still present in Cargo.toml after substitution" >&2
    exit 1
fi

# Refresh Cargo.lock for the bumped versions and verify the build.
cargo build --workspace
cargo test --workspace

# --- commit, tag, push -------------------------------------------------------

git add Cargo.toml Cargo.lock
git commit -m "chore: release ${tag}"
git tag -a "${tag}" -m "Release ${tag}"

# Atomic push: the remote either accepts both the bump commit on `main` and
# the new tag, or rejects both. Prevents a half-pushed state where the tag
# lands without the commit (or vice versa).
git push --atomic origin "main:main" "refs/tags/${tag}"

# Success — disarm rollback so the trap doesn't undo our committed work.
rollback_armed=0

cat <<EOF

Pushed ${tag} to origin.
The 'publish' workflow will release to crates.io:
  https://github.com/Inferara/soroban-ret/actions/workflows/publish.yml
EOF
