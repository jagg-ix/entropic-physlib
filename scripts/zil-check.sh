#!/usr/bin/env bash
# Validate the ZIL formalization graphs under formalization/zil.
#
# ZIL evaluates each .zc graph with Datalog/Horn semantics. A graph that fails
# to evaluate, or whose CI query profile reports a failure, fails this script.
#
# Requires a checkout of jagg-ix/zil-lean at the revision pinned in
# formalization/zil/ZIL_REVISION. Point ZIL_LEAN_DIR at that checkout; the
# native CLI dispatches to `lake exe zil`, so lake must be on PATH (elan).
#
#   ZIL_LEAN_DIR=/path/to/zil-lean ./scripts/zil-check.sh

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
graph_dir="$repo_root/formalization/zil"
revision_file="$graph_dir/ZIL_REVISION"
zil_lean_dir="${ZIL_LEAN_DIR:-$repo_root/../zil-lean}"
out_dir="${ZIL_CHECK_OUT_DIR:-$repo_root/.zil-check}"

fail() { echo "[zil-check] ERROR: $*" >&2; exit 1; }

[ -d "$graph_dir" ] || fail "no formalization/zil directory under $repo_root"
[ -f "$revision_file" ] || fail "missing $revision_file"
[ -x "$zil_lean_dir/bin/zil" ] || fail "ZIL_LEAN_DIR=$zil_lean_dir has no executable bin/zil"
command -v lake >/dev/null 2>&1 || fail "lake is required for the native ZIL CLI (install elan)"

pinned="$(tr -d '[:space:]' < "$revision_file")"
[[ "$pinned" =~ ^[0-9a-f]{40}$ ]] || fail "ZIL_REVISION is not a 40-character commit sha: '$pinned'"

# The Lake dependency and the graph pin must name the same zil-lean revision, so
# the graphs are validated by the engine the Lean build actually links against.
if [ -f "$repo_root/lakefile.toml" ]; then
  lake_rev="$(awk '/^name = "«zil-lean»"/ { in_zil = 1; next }
                   in_zil && /^rev = / { gsub(/[^0-9a-f]/, "", $3); print $3; exit }
                   /^\[\[require\]\]/ { in_zil = 0 }' "$repo_root/lakefile.toml")"
  if [ -n "$lake_rev" ] && [ "$lake_rev" != "$pinned" ]; then
    fail "pin drift: ZIL_REVISION is $pinned but lakefile.toml requires $lake_rev"
  fi
fi

# In CI the checkout is made at the pinned revision; catch a stale local one.
if head_rev="$(git -C "$zil_lean_dir" rev-parse HEAD 2>/dev/null)"; then
  if [ "$head_rev" != "$pinned" ]; then
    fail "zil-lean checkout is at $head_rev but ZIL_REVISION pins $pinned"
  fi
fi

shopt -s nullglob
graphs=("$graph_dir"/*.zc)
[ "${#graphs[@]}" -gt 0 ] || fail "no .zc graphs found in $graph_dir"

mkdir -p "$out_dir"
echo "[zil-check] zil-lean $pinned, ${#graphs[@]} graph(s)"

failed=0
for graph in "${graphs[@]}"; do
  name="$(basename "$graph" .zc)"
  log="$out_dir/$name.txt"
  # bin/zil resolves its Lake workspace relative to its own root, so run it there
  # and hand it the absolute graph path.
  if (cd "$zil_lean_dir" && ./bin/zil query-ci "$graph" - -) >"$log" 2>&1; then
    echo "[zil-check] ok      $name"
  else
    echo "[zil-check] FAILED  $name"
    sed -n '1,40p' "$log" | sed 's/^/               /'
    failed=$((failed + 1))
  fi
done

if [ "$failed" -gt 0 ]; then
  echo "[zil-check] $failed of ${#graphs[@]} graph(s) failed; logs in $out_dir" >&2
  exit 1
fi

echo "[zil-check] all ${#graphs[@]} graph(s) validated"
