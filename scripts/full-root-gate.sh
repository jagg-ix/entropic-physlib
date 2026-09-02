#!/usr/bin/env bash
# Authoritative full-root merge gate.
#
# Builds Physlib.Meta.FullRootGate, which forces the entire Physlib root plus the fast build-time
# honesty gates (axiom-clean, non-vacuity, ZIL contracts, ZilGraph decide-proofs) to build. A module
# that fails to compile or trips a gate — including one reachable only through EntropicSpine or an
# orphaned Meta leaf — fails here. A scoped `lake build <one module>` does NOT do this.
#
# Run this before merging. It is the check that would have caught the M9 modules merged without a build.
set -euo pipefail

cd "$(dirname "$0")/.."

target="Physlib.Meta.FullRootGate"
echo "==> full-root gate: lake build ${target}"
if env LEAN_ABORT_ON_PANIC=1 lake build "${target}"; then
  echo "==> PASS: full root compiles and every gated declaration is axiom-clean, non-vacuous, and contract-satisfied."
  exit 0
else
  status=$?
  echo "==> FAIL (exit ${status}): a module failed to compile or tripped a build-time honesty gate above."
  exit "${status}"
fi
