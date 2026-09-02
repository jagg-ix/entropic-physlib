# The `analysis/` audit trail

This directory is the program's open lab notebook: machine-generated audit reports, the
triage records that drove them to their current state, and the working plans. It is
published deliberately — the honesty claims in the [program guide](../docs/EntropicGravityProgram.md)
are checkable here.

## Generated reports (do not edit by hand)

- [`zil-graph-report.md`](zil-graph-report.md) — the current knowledge-graph audit, regenerated
  by `./scripts/zil-graph-report.sh`: unsupported claims, buried conditionality, the
  primitive-premise ledger, per-sector certificates.
- [`zil-graph-report-fullroot.md`](zil-graph-report-fullroot.md) — the whole-library sweep.
- [`health-baseline.json`](health-baseline.json) — machine-readable headline metrics.

## Standing records

- [`unsupported-claims-worklist.md`](unsupported-claims-worklist.md) — the remediation record
  (850 → 269) and the open queue of claims awaiting **human** bibliographic grounding.
- [`buried-conditionality-triage.md`](buried-conditionality-triage.md) — case-by-case triage of
  every exact claim that ever rested on an undisclosed weaker premise (now 0).
- [`gold-corpus.md`](gold-corpus.md) — the reviewed tier above the raw graph; statement-level
  sign-off is human work and still open.
- [`empirical-discrimination-plan.md`](empirical-discrimination-plan.md) — what the program
  attempts to test, and what it refuses to claim.
- [`program-health.md`](program-health.md), [`uncovered-modules.md`](uncovered-modules.md),
  [`zil-graph-gap-status.md`](zil-graph-gap-status.md), [`AUDIT.md`](AUDIT.md) — synthesis and
  coverage notes.
- [`de-broglie-thesis-evaluation.md`](de-broglie-thesis-evaluation.md) — a source evaluation
  under the program's information-dimension lens.

## Historical records (completed work, kept for provenance)

- [`port-verification.md`](port-verification.md), [`upstream-master-integration.md`](upstream-master-integration.md),
  [`defeq-transparency-removal.md`](defeq-transparency-removal.md),
  [`zil-engine-modularization-plan.md`](zil-engine-modularization-plan.md) — records of the
  v4.33 port and engine extraction. Descriptive of past states, not the current tree.
