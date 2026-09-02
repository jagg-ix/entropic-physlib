#!/usr/bin/env bash
# scripts/consolidate/run.sh — one consolidation round, end to end.
#
#   ./scripts/consolidate/run.sh              # discover + plan only (writes nothing)
#   ./scripts/consolidate/run.sh --apply      # plan, apply, verify
#
# Stage 1 needs the closure built, because the candidates come from the elaborated ZIL
# graph rather than from file names. Re-run after each round: merging one pair routinely
# reveals a third member of the same arc that the first pair was masking.

set -u

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"
cd "$ROOT" || exit 1

CANDIDATES="$DIR/candidates.out"
PLAN="$DIR/plan.json"
APPLY="${1:-}"

echo "== stage 0: build the closure the query reads =="
# The candidates come from the elaborated graph, so a stale build yields an EMPTY
# candidate list -- which would otherwise read as "nothing to consolidate".
if ! lake build Physlib 2>&1 | tail -1 | grep -q "Build completed successfully"; then
  echo "   closure build failed; fix that before consolidating" >&2
  exit 1
fi

echo "== stage 1: candidates from the ZIL graph =="
lake env lean "$DIR/candidates.lean" 2>&1 | grep -E "^(PAIR|FRAG|SUBJ)\b" > "$CANDIDATES"
if [ ! -s "$CANDIDATES" ]; then
  echo "   no candidates emitted -- the query returned nothing, which means it could not" >&2
  echo "   read the graph, not that the repository is fully consolidated." >&2
  exit 1
fi
echo "   $(grep -c '^PAIR' "$CANDIDATES") mutual pair(s), $(grep -c '^FRAG' "$CANDIDATES") fragment(s), $(grep -c '^SUBJ' "$CANDIDATES") split subject(s)"

echo "== stage 2: plan =="
python3 "$DIR/consolidate.py" plan --candidates "$CANDIDATES" --out "$PLAN" "${@:2}" || exit 1

if [ "$APPLY" != "--apply" ]; then
  echo
  echo "dry run. review $PLAN, then re-run with --apply"
  exit 0
fi

echo "== stage 3: apply =="
python3 "$DIR/consolidate.py" apply "$PLAN" --apply || exit 1

echo "== stage 4: verify =="
python3 "$DIR/consolidate.py" verify "$PLAN"
