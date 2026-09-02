#!/usr/bin/env bash
#
# Program-health regression ratchet.
#
# Rebuilds the program-health synthesis, reads its diffable metrics line, and
# fails if any hard hygiene invariant has regressed versus the committed
# baseline (analysis/health-baseline.json). The guarded metrics are the ones
# that must never grow: undisclosed risky claims, out-of-vocabulary statuses,
# and untested numerical predictions.
#
# Run from the repository root (e.g. in CI):
#
#   ./scripts/physlib-health-ratchet.sh
#
# After a legitimate, reviewed change to the baseline, regenerate it with:
#
#   lake build Physlib.Meta.ProgramHealth 2>&1 \
#     | grep -oE '\{"edges":.*"hidden_debt":[0-9]+\}' | head -1 > analysis/health-baseline.json
#
set -eo pipefail

module="Physlib.Meta.ProgramHealth"
source="Physlib/Meta/ProgramHealth.lean"
baseline="analysis/health-baseline.json"
guarded="undisclosed out_of_vocab untested_numerical"

[ -f "$baseline" ] || { echo "error: missing $baseline" >&2; exit 1; }

echo "Rebuilding $module"
touch "$source"
cur="$(lake build "$module" 2>&1 | grep -oE '\{"edges":.*"hidden_debt":[0-9]+\}' | head -1)"
[ -z "$cur" ] && { echo "error: no metrics captured — build may have failed" >&2; exit 1; }
base="$(cat "$baseline")"

get() { printf '%s' "$1" | grep -oE "\"$2\":[0-9]+" | grep -oE '[0-9]+' | head -1; }

fail=0
for m in $guarded; do
  c="$(get "$cur" "$m")"; b="$(get "$base" "$m")"
  if [ "${c:-0}" -gt "${b:-0}" ]; then
    echo "  REGRESSION  $m: $b -> $c"; fail=1
  else
    echo "  ok          $m: ${c:-?}  (baseline ${b:-?})"
  fi
done

echo "current:  $cur"
echo "baseline: $base"
if [ "$fail" != 0 ]; then
  echo "health ratchet FAILED — a hygiene invariant regressed"
  exit 1
fi
echo "health ratchet passed — no hygiene regression"
