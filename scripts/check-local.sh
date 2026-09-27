#!/usr/bin/env bash
# Check against an existing read-only Lean/mathlib installation, without downloads.
set -euo pipefail
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"
module_order="$(python3 scripts/module-order.py)"
while IFS= read -r module; do
  bash scripts/lean-local.sh -o "Fluctuations/$module.olean" "Fluctuations/$module.lean"
done <<< "$module_order"
bash scripts/lean-local.sh -o Fluctuations.olean Fluctuations.lean
audit_log="$(mktemp)"
trap 'rm -f "$audit_log"' EXIT
bash scripts/lean-local.sh scripts/Audit.lean 2>&1 | tee "$audit_log"
python3 scripts/check-axioms.py "$audit_log"
