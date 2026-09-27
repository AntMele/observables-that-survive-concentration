#!/usr/bin/env bash
# Check against an existing read-only Lean/mathlib installation, without downloads.
set -euo pipefail
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"
for module in Probability WeightedVariance Window Main FiniteDimensionalVariance HaarSU4 \
  LocalPolynomial ProductVariance HaarProcess QubitEmbedding HaarLocalVariance HaarCircuit \
  SpatialSupport MeanChange ActiveHaarCircuit; do
  bash scripts/lean-local.sh -o "Fluctuations/$module.olean" "Fluctuations/$module.lean"
done
bash scripts/lean-local.sh -o Fluctuations.olean Fluctuations.lean
audit_log="$(mktemp)"
trap 'rm -f "$audit_log"' EXIT
bash scripts/lean-local.sh scripts/Audit.lean 2>&1 | tee "$audit_log"
python3 scripts/check-axioms.py "$audit_log"
