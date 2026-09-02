# Buried-conditionality triage — the full-root weakest-link findings, case by case

**Date**: 2026-08-29.  **Scope**: the full-root graph (`Physlib` + `QuantumInfo` +
`PhyslibAlpha`).  **What is triaged**: every `buriedConditionality(D, E)` pair — an exact-status
claim `D` that transitively `dependsOnDecl` a weaker-status declaration `E` — reported by the
weakest-link auditor (`analysis/zil-graph-report.md` counts 21 at full root; the static
replication below resolves the same closure into **41 (claim, weak-declaration) pairs over 20
distinct claims**, the difference being pair-vs-claim counting and leaf modules outside the
root).

**Method.**  The exact rule set of `Physlib.Meta.ZilGraph.weakestLinkRules` (establishes via
formalizes/derives/alias, `dependsOnDecl` via `requires`∘`establishes` and via `supported_by
@ "lean:…"`, both closed transitively, then the `statusStrictlyStronger` join) was replayed over
the `zil attach` blocks of the source tree, three saturation rounds, matching the report's
depth bound.  Each resulting pair was then subjected to a test the Datalog layer cannot
perform: **does the flagged claim's Lean proof actually consume the weak declaration?**  A pair
where it does is a genuine logical dependency; a pair where it does not arose from a
`supported_by` *citation* edge (or a transitive chain through one) that the high-recall
`dependsOnDecl.support` rule promotes to a dependency.

**Resolution (implemented 2026-08-30).**  The detector now carries a **disclosure
exemption**: `buriedConditionalityRule` takes a negative literal on a new extensional
`discloses` relation, so a pair `(D, E)` where `D`'s attach block carries
`discloses @ "lean:E"` is *acknowledged* conditionality, not buried — certified by `decide`
(`buriedConditionality_suppressed_on_disclosed`, with the undisclosed twin still firing).
All 41 pairs below received `discloses` edges (plus four residual root-scope pairs the static
replication had not seen — `uniformlyFocusing_saturating_flux` → the Bousso bound, the
Spohn free-energy chain behind `oneLevelExactDiagonal_freeEnergyGap_antitoneOn`, and the
`SchwarzschildHorizonScaleMobius` one-bit chain behind two inference-`G` capstones — 45 in
all, the last four read directly off the compiled root graph), and the seven claims that had **no** caveat
(the entropic-gravity quartet, `metricStationary_iff_residualCoordinate_zero`, and the two
LightSheet claims) additionally received factual `caveat` edges naming the load.  The
full-root buried count is now **0**, with every former finding preserved in the graph as an
explicit disclosure rather than silence.  The genuine-vs-citation split below remains the
per-pair record of *why* each disclosure is worded as it is.

**Headline split: 13 of 41 pairs are proof-level dependencies; 28 are citation edges.**
This is the single most important fact about the finding set: the majority of the buried
conditionality signal is the (documented) recall/precision trade of the support rule, not
hidden epistemic debt.  The 13 proof-level pairs are the real findings and are triaged below.

## A. The entropic-gravity quartet — genuine, and UNDISCLOSED (highest priority)

| claim (`consistency-identity`) | rests on | via |
|---|---|---|
| `TransverseMomentumEffectiveMass.effectiveNewton_from_unruh` | `newton_second_law_from_verlinde_unruh` (`ansatz-loaded`) | **proof** |
| `TransverseMomentumEffectiveMass.entropic_law_observables_only` | `newton_second_law_from_verlinde_unruh` (`ansatz-loaded`) | **proof** |
| `TransverseMomentumEffectiveMass.inverseSquare_law_observables_only` | `newton_law_of_gravity_from_verlinde` (`ansatz-loaded`) | **proof** |
| `TransverseMomentumEffectiveMass.inverseSquare_holographic` | `bousso_covariant_bound` (`ansatz-loaded`), `generalizedEntropy_monotone` (`conditional-model`) | citation |

The three proof-level claims consume the Verlinde derivation theorems directly, and **none of
the four carries a single `caveat` edge**.  These are exactly the "entropic gravity as
negative control" cases: the algebra in each statement is exact, but the physical reading
routes through the displacement-entropy ansatz.  *Recommendation*: add `caveat` edges
disclosing the Verlinde-ansatz load (mechanical, claim-preserving), or re-status to a
conditional tier if the owner judges the statements' physical content — not just their
algebra — to be the claim.  Do not present these as unconditional results in any publication.

## B. The inference-`G` / D3-brane dictionary family — genuine, disclosed

`d3_centralCharge_complexEinsteinCoupling`, `d3_gkpWittenHessian_complexEinsteinCoupling`,
`d3_gkpWittenHessian_boundaryCentralCharge`, `d3_rtEntropy_boundaryCentralCharge`,
`d3_rtEntropy_complexEinsteinCoupling` (all `EMComplexEinsteinAdSCFT`), plus
`d3_bulkCentralCharge_eq_boundary` and `comptonAnchored_newtonG_eq_from_clockFrequency`.
Eight of these pairs are proof-level: the claims consume
`newtonG_from_positionVariance`, `comptonCell_gkpWitten_source_hessian`,
`comptonCell_d3_compactification_dictionary` or `d3_inferenceEinsteinCoupling_dictionary` —
the `G = ħcσ₀⁴` chain the assumption ledger already ranks as the program's largest
foundational risk (`compton-cell-screen-tiling`, reach 28; `caticha-cafaro-inference-mass`,
reach 25).  **Every claim in this family carries `caveat` and/or `requires` disclosure
edges.**  *Verdict*: the auditor is working as designed — these are known-conditional capstones
correctly surfaced; the disclosure is present; the statuses are defensible because each Lean
statement carries its dictionary hypotheses explicitly.  *Recommendation*: no repo change;
in publications, cite these only as case studies of tracked conditionality (per the
publication review, do not lead with them).

## C. The holographic light-sheet / horizon-thermodynamics family — real chains, honest labels, missing caveats

`bekensteinRate_nonpos`, `entropyFlux_eq_bekenstein_deficit` (LightSheet) and
`einstein_horizon_iff_firstLaw` rest (by citation chains) on `area_monotone`,
`expansion_nonneg`, `focusing_contradiction`, `kerrNewman_firstLaw` and friends — classical-GR
inputs whose `conditional-model` labels are themselves *honest* (energy conditions, model
metrics).  No pair is proof-level by the direct test, but the chains reflect the module's real
logical architecture (the file's own prose says "the `caveat` edges say so" — yet
`bekensteinRate_nonpos` and `entropyFlux_eq_bekenstein_deficit` carry **no caveat edges**).
*Recommendation*: add the missing `caveat` disclosures on the two LightSheet claims;
otherwise keep — an exact identity *conditional on explicitly-stated GR hypotheses* is what
`consistency-identity` means for statements whose binders carry the hypotheses.

## D. The Lindblad certificate pair — citation artifacts

`exactReductionCertificate_zero_error` → `total_reduction_error_bound` and
`inverse_transverseRelaxationTime_eq` → `oneLevelGKSLWithPureDephasingMatrix_eq` (both
`conditional-model` supports; both citation-level).  The "zero error" certificate is an exact
statement *about* the conditional reduction — the support edge is its subject, not its
premise.  *Verdict*: not buried debt; the finding is the support rule's recall.
*Recommendation*: none required; candidates for a future `cites`-vs-`supported_by` vocabulary
split (see §F).

## E. Singletons

* `local_constrained_evolution_unique` → `local_evolution_unique` (`ansatz-loaded`,
  **proof-level**): the ADM constrained-evolution uniqueness genuinely consumes the G-free
  Cauchy uniqueness with its Lipschitz/phase-space assumptions; the claim carries a caveat.
  Verdict: genuine, disclosed.
* `metricStationary_iff_residualCoordinate_zero` → `metricStationary_iff_complexEinstein`
  (`ansatz-loaded`, **proof-level**, no caveat): an iff-composition that inherits the
  complex-Einstein ansatz through its middle term.  Recommendation: add a caveat edge; the
  bare `consistency-identity` reads stronger than the content.
* `gold_relative_gain_threshold_exact` → `referenceRoomTemperatureConductivity_order`
  (`data-loaded`, citation): the only data-loaded finding — an exact threshold claim whose
  neighborhood cites an empirical conductivity datum.  Disclosed via caveat + requires.
  Verdict: honest.
* `intervalArakiProduction_cocycle` → `relativeEntropy_antitone` (citation, disclosed).
  Verdict: honest.

## F. The systematic lesson

1. **The support rule's precision is the story.**  28 of 41 pairs exist because
   `supported_by @ "lean:…"` conflates *citation* with *dependency*.  The clean fix is a
   vocabulary split — a `cites` relation for context references, keeping `supported_by` for
   load-bearing support — after which the auditor's precision matches its recall.  This is a
   vocabulary decision for the owner, like the epistemic-status tier extension before it.
2. **Exactness-with-hypotheses is not over-claiming.**  Most genuine pairs are Lean theorems
   whose binders carry the conditional hypotheses explicitly; `consistency-identity` for the
   *statement* is compatible with an `ansatz-loaded` *instantiation*.  The five undisclosed
   cases (§A quartet + `metricStationary_iff_residualCoordinate_zero`, plus the two §C
   LightSheet claims) are the ones where a reader of the graph alone would miss that — the
   caveat edges are the cheap, claim-preserving fix.
3. **Nothing found here contradicts the honesty-gate result** (0 status over-claims resting
   on undischarged physical postulates): every genuine chain terminates in a *labeled*
   weaker-status theorem, not an unlabeled postulate.  The buried-conditionality count is a
   disclosure-quality metric, not an unsoundness metric.

**Caveat on method**: the pair set was produced by a faithful static replication of the
Datalog rules over source-parsed attach blocks (10,618 edges vs the report's 9,761 — the
surplus is leaf modules outside the root and comment-adjacent blocks), and the proof-use test
is a source-block heuristic.  The authoritative counts remain those of
`Physlib.Meta.ZilGraphAuditFull`; this document adds the per-pair reading the report cannot.
