#!/usr/bin/env bash
set -euo pipefail
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SHARED_LEAN_PROJECT="${SHARED_LEAN_PROJECT:-$PROJECT_ROOT/../Single-copySTABLEARNING}"
LEAN_BINARY="$SHARED_LEAN_PROJECT/.elan/toolchains/leanprover--lean4---v4.24.0/bin/lean"
if [[ ! -x "$LEAN_BINARY" ]]; then
  printf 'Lean 4.24.0 was not found at %s\n' "$LEAN_BINARY" >&2
  printf 'Set SHARED_LEAN_PROJECT to an existing installation, or use scripts/check.sh.\n' >&2
  exit 1
fi
export LEAN_PATH="$PROJECT_ROOT"
for package_dir in "$SHARED_LEAN_PROJECT"/.lake/packages/*; do
  if [[ -d "$package_dir/.lake/build/lib/lean" ]]; then
    LEAN_PATH="$LEAN_PATH:$package_dir/.lake/build/lib/lean"
  fi
done
cd "$PROJECT_ROOT"
exec "$LEAN_BINARY" "$@"
