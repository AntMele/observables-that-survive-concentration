#!/usr/bin/env bash
# Portable verification using the versions pinned in lean-toolchain and lake-manifest.json.
set -euo pipefail
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"

for dependency in lake python3; do
  if ! command -v "$dependency" >/dev/null 2>&1; then
    printf 'Required command not found: %s\n' "$dependency" >&2
    exit 1
  fi
done

lake env lean --version
lake build
audit_log="$(mktemp)"
trap 'rm -f "$audit_log"' EXIT
lake env lean scripts/Audit.lean 2>&1 | tee "$audit_log"
python3 scripts/check-axioms.py "$audit_log"
