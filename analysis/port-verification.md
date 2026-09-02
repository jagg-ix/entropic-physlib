# Port verification: `port/v433` vs the fork branch

Run 2026-08-28 on `port/v433` (115c4d9ae). The reference line is the fork branch
`recovery/entropic-physlib-linear-full-v433` (2aaa690b5, pushed as
`claude/entropic-physlib-workflows-f9vasr`).

## Passes

| check | port | fork | verdict |
|---|---|---|---|
| `lake build` (all three libraries) | **green, 11236 jobs** | green, 11086 jobs | both green; port roots 104 more modules |
| global `backward.isDefEq` flags | **0** | 2 (Physlib, PhyslibAlpha) | port |
| per-declaration escapes | 832 | 445 (+2 library-wide blankets) | port — see below |
| `#guard` evaluator-equivalence checks | **42/42 pass** (in default build) | 40/40 pass | both |
| ZIL repo-wide audit | **runs, 9761 edges** | runs, 9761 edges | identical graph — nothing lost in the port |
| ZIL gap profile | 82 / 850 / 114 / 20 / 0 cycles | same | identical |
| real `sorry`s introduced | **0** (all matches are upstream `@[sorryful]` or `no_sorry` lint markers) | 0 | both |
| build warnings | **1199** | 1276 | port |
| style linter | 43793 (exit 1) | 43739 (exit 1) | both fail on legacy debt; +54 (~0.1%) from shim/compat files |
| `lake exe check_file_imports` | fails (leaf-module policy) | fails (same policy) | pre-existing on both |

### On the escape counts

The raw numbers mislead. The fork's 445 sat **under two library-wide
`-Dbackward.isDefEq.respectTransparency=false` blankets**, so every one of Physlib's
~2400 files was compiled with weakened definitional-equality checking whether it needed
it or not. The port's 832 are all per-declaration and visible — each one names exactly
which proof needs the old transparency — and upstream itself carries 721 in the same
style. The port's 111 above upstream is the honest per-declaration price of the fork's
research corpus; the fork's configuration hid that price behind the blankets.

## What the port is, structurally

* Base: `upstream/master` (9c33f2ca2), Lean v4.33 — 9 commits ahead, each a reviewable
  stage; merging future upstream is a routine pull, not an archaeology project.
* The fork's research corpus (~498k lines, 1947 fork-only modules) carried over intact:
  identical ZIL knowledge graph, zero declarations lost except the four `WithDim`-typed
  lemmas and two LRL helpers explicitly recorded as deferred (all with zero consumers).
* The information dimension is upstream's own design (a basis instance), no rival
  `Dimension` type.
* 27 re-export shims keep every old module path resolving.

## The fork branch's remaining liabilities

* Two global defeq blankets whose removal was measured at 97+ errors and shown to
  require an atomic all-at-once conversion (`analysis/defeq-transparency-removal.md`).
* Five upstream tree relocations unresolved, 48-file merge conflict per upstream sync
  (`analysis/upstream-master-integration.md`).
* A rival six-field `Dimension` structure diverging from upstream's parameterised one.

## Recommendation

Make **`port/v433` the mainline**. It is everything the fork branch is — same research
content, same knowledge graph, same green build — minus the three structural
liabilities, plus a clean upstream base. The fork branch stays as the archival record
of the pre-port line (tagged `pre-port-checkpoint`); its 21 commits of migration and
tooling work are either already incorporated (ZIL fast evaluator, audit script fix,
analysis notes travelled with the graft) or superseded by the port.

Residual work, none of it blocking:
* the 82 out-of-vocabulary `epistemic_status` values (a vocabulary decision, unchanged
  by the port — `analysis/zil-graph-gap-status.md`);
* the deferred `WithDim` lemmas, pending a basis-generic `HasDim` upstream;
* legacy style debt (43k, predating everything);
* ~~`scripts/zil-check.sh` still needs an external `zil-lean` checkout to validate the
  `.zc` graphs.~~ **Done (2026-08-28):** run against the local checkout at
  a local `zil-lean` checkout, whose HEAD is exactly the
  pinned revision `abfddd3d…` — **all 21 graphs validated**, exit 0. Invocation:
  `ZIL_LEAN_DIR=/path/to/zil-lean ./scripts/zil-check.sh`.
