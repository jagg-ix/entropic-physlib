# ZIL knowledge-graph gaps: current state

> **RESOLVED (2026-08-28, port/v433).** The status-vocabulary gap this note analysed is closed.
> `allowedEpistemicStatuses` now carries a **mathematical tier** (`analytic-theorem`,
> `mathematical-identity`, `classification-theorem`, …, eleven values of exact-theorem strength),
> conditional/loaded variants (`conditional-analysis`, `conditional-model-theorem`,
> `model-representation` demand grounding; `data-loaded` demands disclosure) and the meta value
> `repository-extension`; the weakest-link strength order is generated as the product of the exact and
> weak tiers. No declaration's `epistemic_status` was changed — with one exception: seven attachments in
> `SecondBianchiDilationCartanQCDTQFT` spelled `consistency_identity` with an underscore, a typo of an
> in-vocabulary value, corrected to `"consistency-identity"`.
>
> The audit now reports **0** out-of-vocabulary values. Two counts moved as a consequence of the audit
> *gaining coverage*, not of any content change: adaptive conformance 1 → 18 (the newly policied
> conditional/loaded variants hold their claims to grounding/disclosure they do not yet provide — a
> genuine to-do list), and buried conditionality 20 → 21 (one mathematical-tier claim rests on a
> weaker-status dependency). The honesty gate (`exactIdentityStatusFacts`) still fires only on
> `consistency-identity`; widening it to the mathematical tier is a deliberate tightening left open.


## The audit had stopped running

`scripts/zil-graph-report.sh` builds `Physlib.Meta.ZilGraphAuditFull` and captures the audit it logs.
It had stopped completing:

* `lake build Physlib.Meta.ZilGraphAuditFull` reached job 11067/11071 and then sat in a single `lean`
  process at ~99.5% CPU. Killed after **5h32m** with no audit emitted.
* The wrapper failed silently: under `set -e` it aborted on the build before reaching its own
  "no audit output captured" branch, so it exited 1 with no diagnostic.

Because the audit could not run, `analysis/zil-graph-report.md` had been frozen at its 2026-07-28
contents while the graph kept growing — and its numbers were not merely old but wrong.

## Cause: three compounding costs in the reference evaluator

`Zil.Datalog.deriveProgram` (in the pinned `zil-lean` package) is the reference implementation:
small, obviously correct, and quadratic in several places at once.

1. **No saturation check.** `deriveRuleSet` recurses on `fuel` unconditionally. A rule set that reaches
   its fixpoint after two rounds still pays for all eight, each a full pass over every fact.
2. **Quadratic dedup.** Every round rebuilds the whole accumulated set with `List.eraseDups` — `O(n²)`
   structural comparisons over atoms containing strings — re-deduplicating facts that were already
   unique the round before.
3. **Unindexed joins.** `matchPattern` scans *every* fact for every pattern and every candidate
   substitution. For the transitive-closure rules — `dependsOnDecl(D,F) :- dependsOnDecl(D,E),
   dependsOnDecl(E,F)` — that is `O(m²)` per round in the size of the derived relation. This is where
   the audit actually disappeared: `dependsOnDecl` now has 3944 members.

## Fix

`Physlib/Meta/ZilDatalogFast.lean` adds `deriveProgramFast`, a drop-in replacement that keeps the
reference semantics and removes all three costs: it stops as soon as a round adds nothing, deduplicates
through a `Std.HashSet` in first-occurrence order, and indexes facts by relation and by
(relation, endpoint) so a join probes only atoms that can possibly unify.

The indexing is exactly semantics-preserving because `Zil.Datalog.unify` rejects immediately when
`pattern.relation != atom.relation`, and because each index bucket preserves the fact list's order — so
probing a bucket yields the same subsequence, in the same order, that scanning every fact would have.

`Physlib/Meta/ZilDatalogFastCheck.lean` pins this down: 40 `#guard`s assert
`deriveProgramFast p n == deriveProgram p n` — **list** equality, so same atoms in the same order — on
every sample program in `Physlib.Meta.ZilGraph`, at fuels 0 through 8. It includes the fuel-exhaustion
cases (0, 1, 2), where the closure is genuinely truncated, so the early exit cannot derive more than the
reference engine would at the same budget. The module is imported from `Physlib.lean`, so the guards run
on every build and the optimisation cannot silently drift from the reference.

`Physlib.Meta.ZilGraphReport` now calls `deriveProgramFast` at all three of its call sites.

### Result

**5h32m without finishing → 2m03s.** Reruns in ~71s once the library is cached. `lake build` is green
at 11086 jobs.

## Two scopes, two sets of numbers

A recurring source of confusion, worth stating plainly. There are **two** audits, and both are correct:

* **Default scope** — `Physlib.Meta.ZilGraphReport` ends in `#zil_graph_report`, so an ordinary
  `lake build` logs a demonstration-scope audit over that module's own imports (2378 edges). This is
  where figures like "13 unclassified, 23 out-of-vocabulary, 220 unsupported" come from. They are
  current and accurate *for that scope*.
* **Full root** — `Physlib.Meta.ZilGraphAuditFull` imports all of `Physlib` (9761 edges) and is what
  `scripts/zil-graph-report.sh` writes to `analysis/zil-graph-report.md`. Its numbers are several times
  larger.

Quoting one scope's figure against the other's makes the graph look like it changed when it did not.
The table below is **full root**.

## What the audit now reports

The first successful run since 2026-07-28. Drift the frozen report was hiding:

| gap | stale report | now |
|---|---|---|
| untested predictions (no `experimental_bound`) | 16 | **113** |
| unclassified predictions (no `prediction_class`) | 17 | **114** |
| unstatused predictions (no `epistemic_status`) | 3 | **12** |
| **out-of-vocabulary `epistemic_status`** | **0** | **82** |
| unsupported claims (no `supported_by`) | 542 | **850** |
| buried conditionality (weakest-link) | 9 | **21** |
| distinct primitive premises | 143 | **293** |
| declaration dependencies | 1568 | **3944** |
| fully documented predictions | 21 | 23 |
| circular `requires` chains | 0 | 0 |
| status over-claims | 0 | 0 |

Two of these deserve attention beyond their size:

* **82 out-of-vocabulary statuses**, against a stale report claiming zero. An independent static scan of
  `epistemic_status @ "..."` occurrences found 79 across ten files, agreeing with the engine.
* **buried conditionality is 21, not 0.** `analysis/AUDIT.md`'s narration has been updated to
  the current count, and the full-root findings are triaged case by case in
  `analysis/buried-conditionality-triage.md`.

## The status-vocabulary question is a decision, not a cleanup

`Physlib.Meta.ZilGraph.allowedEpistemicStatuses` admits five values: `inversion`,
`consistency-identity`, `ansatz-loaded`, `risky`, `conditional-model`. The 16 distinct stray values are
not typos — they are *mathematical* statuses (`analytic-theorem` ×27, `mathematical-identity` ×25,
`classification-theorem`, `obstruction-theorem`, `mathematical-counterexample`, …), and the vocabulary is
built for *physical prediction* strength. The fork has grown a body of pure-mathematics results the
vocabulary has no honest slot for.

Two defensible fixes, which are not equivalent:

1. **Extend the vocabulary** with a mathematics tier, and give `conformancePolicy` rows for the new
   values. This records what the declarations already claim.
2. **Remap the 82** onto existing values. This *changes what the program asserts about its own
   epistemic standing* — calling an `analytic-theorem` a `consistency-identity` is a claim about
   content, not a rename.

Option 2 must not be done mechanically. That judgement is left to the author; nothing here changes any
graph data.

## Remaining, not addressed here

* The 850 unsupported claims and 113 untested predictions need citations and bounds — domain work.
* `analysis/AUDIT.md`'s prose figures predate this run and should be refreshed against it.
* `scripts/zil-check.sh` (the `.zc` graph validator) still cannot run here: it needs a `zil-lean`
  checkout at the revision pinned in `formalization/zil/ZIL_REVISION`
  (`abfddd3d4466f24e81830c5f96b102938a832565`) via `ZIL_LEAN_DIR`. The 24 `.zc` graphs are unvalidated.
* `lake exe check_file_imports` fails, but already did so before this work: `Physlib.lean` is missing
  `Physlib.Relativity.Tensors.RealTensor.Vector.Causality.MalamentConformalProperTimeBridge` and
  `Physlib.Thermodynamics.FiniteMarkovEntropyProductionStrict`. Unrelated, and left alone.

## The fix belongs upstream too

`deriveProgramFast` lives in physlib because `zil-lean` is a pinned dependency. The same three changes
belong in `Zil.Datalog.deriveProgram` itself, at which point this module becomes a thin alias and the
`#guard`s become its regression suite.
