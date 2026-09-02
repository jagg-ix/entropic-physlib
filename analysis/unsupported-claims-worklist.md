# Unsupported-claim remediation — the factual pass and the remaining worklist

**Date**: 2026-08-29.  **Context**: the full-root audit counted **850** `formalizes`
attachments with no `supported_by` edge (930 in the static whole-tree scope that includes leaf
modules).  The publication review flagged the number; this document records what was fixed
mechanically, on what principle, and what remains for the human author.

## The principle: only factual support, never fabricated citations

A `supported_by` edge is an evidential claim.  Two kinds are machine-verifiable:

* `supported_by @ "lean:X"` — *derivational* support: the claim's own statement or proof
  consumes the formalized result `X`.  This is a fact about the proof term, checkable from
  source, and it is the support kind the weakest-link auditor already consumes.
* `supported_by @ "paper:…"` — *bibliographic* support.  Per `AI-POLICY.md` this is a human
  judgment (does this Lean statement really formalize what that paper asserts?); no such edge
  was added mechanically, and none should be.

## The factual pass (applied)

For every unsupported attachment whose declaration is a theorem/lemma, the statement+proof
block was scanned for references to *other attached declarations*.  A reference was accepted
as a support edge only when unambiguous: a unique attached declaration with that name, or —
under name collisions — a unique same-file or verbatim-qualified match.  Result:

* **372 `supported_by @ "lean:…"` edges inserted into 287 attach blocks across 162 files**,
  each asserting a dependency the proof actually exercises;
* unsupported count: **930 → 645** (whole-tree static scope); the regenerated full-root
  audit reads **850 → 571**, with conformance findings improving 18 → 12 and the
  buried-conditionality count unchanged at 21 (the new derivational edges exposed no
  additional weak chains).

Note an honest side effect: derivational support edges feed `dependsOnDecl`, so the
weakest-link auditor sees *more* of the true dependency structure than before.  If new
buried-conditionality findings appear, they are disclosures gained, not regressions
(see `analysis/buried-conditionality-triage.md` for the reading discipline).

## What remains (645), classified

1. **Roadmap/open-problem ledgers** (the two largest files below, and kin): attachments that
   *document open problems and program claims* — unsupported **by design**; a `supported_by`
   edge would be false.  Recommend: leave, or introduce an `open-problem` marker relation so
   the gap rule can exempt them explicitly rather than by silence.
2. **Infrastructure theorems referencing no attached declaration** (~546 before the pass):
   their proofs rest on unattached helper lemmas or mathlib.  Options: attach the helpers they
   consume (extends the documented graph), or accept them as the coverage frontier.
3. **Bibliographic candidates**: claims whose files already cite the natural source in sibling
   attachments.  These need the human pass — the file-level table below is the queue, largest
   first.

total remaining: 645 across 274 files

| remaining | file |
|---|---|
| 44 | `Physlib/Meta/YukawaMadelungOpenProblemsZil.lean` |
| 20 | `Physlib/Meta/EntropicSpineZil.lean` |
| 15 | `Physlib/QuantumMechanics/ComplexAction/EntropicTime/IpekCatichaSuperpositionViolation.lean` |
| 14 | `Physlib/QuantumMechanics/ComplexAction/Lorentz/SciamaAdSCPTMpembaEntropicClock.lean` |
| 11 | `Physlib/Meta/RelationalClaimLedger.lean` |
| 8 | `Physlib/QuantumMechanics/ComplexAction/ComptonClock/ReversibleLimitConvergence.lean` |
| 8 | `Physlib/QFT/PathIntegral/SchwarzschildFeynmanPropagator.lean` |
| 7 | `Physlib/QuantumMechanics/ComplexAction/Lorentz/SciamaAdSCPTMpembaNewtonObstructionHerglotz.lean` |
| 6 | `Physlib/QuantumMechanics/ComplexAction/Curvature/AffineProjectionTensorGeometry.lean` |
| 5 | `Physlib/QuantumMechanics/ComplexAction/ComptonClock/GeneralDensityRadialPoisson.lean` |
| 5 | `Physlib/Meta/ZilEvidenceClosureRegistry.lean` |
| 5 | `Physlib/Thermodynamics/RelativisticScreenKinematics.lean` |
| 5 | `Physlib/Optics/MpembaIndexRateSelection.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/CaldeiraLeggettGaussianSaddle.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/Curvature/MetricIntervalIsometryInvariance.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/Curvature/ReissnerNordstromHorizons.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/Curvature/ProjectionGradientDecomposition.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/Particles/ShellFillingStability.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/Bogoliubov/Transformation.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/EntropicTime/EntropicDynamicsEvolutionSchrodingerEhrenfest.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/Lorentz/SciamaAdSCPTMpembaComplexActionLorentzian.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/BoseFermiOperatorAlgebra/LindbladSuperoperators.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/CanonicalTetradGravity/SourcedTTWaveComptonCoupling.lean` |
| 4 | `Physlib/QuantumMechanics/ComplexAction/CanonicalTetradGravity/SourcedTransverseTracelessWave.lean` |
| 4 | `Physlib/CondensedMatter/NobleMetalBranchTransport.lean` |

(Full 274-file distribution regenerable with the parser noted in
`analysis/gold-corpus.md`; the counts above are the whole-tree static scope.)

## How this interacts with the gold corpus

Unsupported ≠ unproven: every one of these attachments names a kernel-checked declaration.
The metric measures *anchoring of the claim graph*, and the gold-corpus discipline
(`analysis/gold-corpus.md`) already prevents unanchored claims from being presented as
publication-ready.  The factual pass above moves the anchoring metric by telling the truth
more completely, not by lowering the bar.

## The conformance grounding queue (12 claims, 2026-08-30)

The adaptive-conformance check's remaining findings are all `conditional-model` claims
that carry disclosure (`caveat`) but no *grounding* (`supported_by` source or `derives`).
A proof-dependency scan found no attached declarations their proofs consume, and **their
files contain no literature references at all** — these are self-contained fork-research
models.  Per `AI-POLICY.md` no `paper:` edge was fabricated; per the citation-artifact
lesson of the buried-conditionality triage, no cosmetic `lean:` edge was forced either.
This is the curated human queue — each needs either a literature source (the owner's
bibliographic judgment) or an explicit decision that the model is intentionally
unanchored (in which case a policy row or status change is the honest fix):

| model family | claims | file |
|---|---|---|
| Everett conductivity branches | `exists_gold_silver_crossing`, `supported_gold_first` | `CondensedMatter/NobleMetalBranchTransport.lean` |
| Lindblad driven leads (golden rule / Markov) | `totalRate_eq_goldenRule`, `goldenRuleGamma_eq_coupling_mul_transform_re`, `memory_markov_bound` | `OpenSystems/LindbladDrivenLeads/{OhmicMicroscopicRate,ContinuumWeakCouplingReduction}.lean` |
| Mpemba crossing optics | `crossingTime_pos_iff_isDecayMode`, `spectral_crossing_cross_ratio`, `strongMpemba_exists_of_sign_change` | `Optics/Mpemba*.lean` |
| Zeno stripe readout | `stripe_gap_tendsto_atTop`, `zeno_gap_mul_crossingTime` | `Optics/ZenoStripeGapReadout.lean` |
| Compton-anchored coherence | `comptonAnchored_coherenceTime_eq_inv_comptonFrequency`, `visibility_deficit_depends_only_on_differential` | `ComplexAction/ComptonClock/{ComptonAnchorCoherenceTime,PhaseLikeVisibilityDifferential}.lean` |

Candidate sources the owner may wish to confirm (NOT added): Mpemba-effect Markovian
theory (Lu–Raz 2017, PNAS; Klich et al. 2019), quantum Zeno readout literature (Misra–
Sudarshan 1977 and successors), the golden-rule/Davies weak-coupling limit (Davies 1974),
and decoherence visibility interferometry.  Whether any of these is *the* source for the
fork's specific models is exactly the statement-level judgment the policy reserves.

## The widened pass (2026-08-30): verified derivational support + explicit open-program scope

Second remediation round, on the user's request to clear ~30% of the remainder.  Two
mechanisms, both factual:

1. **The open-program exemption.**  `YukawaMadelungOpenProblemsZil`'s 44 entries already
   carried `open_problem_scope @` markers; the `unsupportedClaim` rule now consults them
   (negative literal on the intensional `openProblemScoped`, `decide`-certified fire and
   suppress), and the report counts the scoped population on its own line — unsupported
   *by declared design* is no longer silently unsupported, and no longer miscounted as
   debt.

2. **The widened derivational pass.**  The 287-edge pass had required support targets to
   be *attached* declarations; this round widens to any proof-consumed Physlib
   theorem/lemma with a repo-unique name — and gates every candidate through an
   elaboration probe (`#check @target` against the compiled root) before insertion, which
   rejected 101 of 480 constructed names.  Result: **426 claims fixed with 591 verified
   `supported_by @ "lean:…"` edges across 197 files**.

Bookkeeping note: this round's parser also fixed an undercount — multi-line `zil attach`
names (the `EntropicSpineZil` registry style) had been missed, so the true whole-tree
unsupported population was 731, not 645.  After this round the machine-fixable remainder
is exhausted: what is left consumes only mathlib or unnamed local steps, or awaits the
human bibliographic queue above.
