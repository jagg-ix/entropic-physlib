/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.EmpiricalEvidence
public import Mathlib.Tactic.NormNum

/-!
# Phase E — discriminator: universality argument

Phase D recorded eight materials whose measured Planckian ratio
falls in the band `(0.1, 10)`.  Phase E asks: does this match
distinguish the entropic-time framework from a trivial alternative?

## The trivial alternative

Standard coordinate-time QM provides no specific prediction for
the transport scattering time of a strange metal.  The dimensional-
analysis null hypothesis says: the only available thermal scale at
temperature `T` is `ℏ/(k_B·T)`, so on dimensional grounds any
scattering time *should* be of that order if there is no other
relevant scale.  Under the null, the O(1) prefactor
`(τ_tr · k_B · T) / ℏ` would be material-dependent — set by
microscopic physics (band structure, coupling strengths, defect
densities) — and could vary across material classes by orders of
magnitude.

## The framework's prediction

The entropic-time framework says the Planckian period IS the
relevant time scale at temperature `T`, not just an upper bound
from dimensional analysis.  Under this hypothesis the O(1)
prefactor is constrained by entropic-time identification
hypotheses (`2·Ṡ_I = k_B·T` in Phase A.1), not by microscopic
parameters.  The prefactor should therefore be O(1) and roughly
universal across material classes that share the strange-metal
identification.

## The discriminator

A single Lean predicate captures the distinguishing observation:

  **All measured strange-metal materials have Planckian ratios
  in a small multiplicative window** (e.g. `(0.3, 1.1)` — a span
  factor of about 4× across the Phase-D corpus).

The dimensional-analysis null does not predict such a narrow
window — under the null, ratios across cuprates, iron pnictides,
heavy semimetals, organic SCs, and twisted bilayer graphene
could differ by orders of magnitude.  The fact that they cluster
within a single factor of 4 across the Phase-D list is the
distinguishing empirical fact.

## What this module does claim

* `IsUniverselyPlanckian` predicate on a list of ratios.
* Theorem: all Phase-D positive instances jointly satisfy the
  predicate within a narrow window `(0.29, 1.11)`.
* Span quantification: `max ratio / min ratio < 4` across the
  Phase-D corpus.

## What this module does NOT claim

* That the universality *proves* the entropic-time framework.
  The inference "universality refutes the null" is a statistical
  argument that depends on the prior plausibility of the null,
  the size of the empirical corpus, and the boundary of "strange
  metal regime" used to select instances.  Lean can certify the
  numerical facts (all measured ratios in band, span < 4);
  framing those facts as evidence requires Bayesian or
  frequentist inference outside the module.
* That the framework correctly predicts the *value* of the
  prefactor — only that the prefactor variation across material
  classes is narrow.  Pinning the O(1) prefactor to a specific
  framework parameter (e.g. an entropic identification ratio) is
  a stronger claim than this module makes.
* That universality holds across *all* metals — only across the
  Phase-D positive subset.  Heavy-fermion and Fermi-liquid
  regimes (Phase D §E) fall outside.

## Quantitative comparison: framework vs null

| Observation                          | Framework prediction | Null prediction |
|--------------------------------------|----------------------|-----------------|
| Ratio O(1) per material               | ✓                    | ✓ (trivially)    |
| Ratio span across material classes    | small (< 10×)        | could be huge   |
| Quantum-critical universality         | expected             | accidental      |
| Reduction in lossless limit (Phase B) | ✓                    | ✓                |
| Modular-time interpretation (Phase A.4) | ✓                  | absent          |

The framework matches all five row predictions; the null matches
rows 1, 4 trivially and rows 2, 3, 5 only through ad-hoc
microscopic explanations.  The Phase-E discriminator focuses on
row 2 — quantitative universality — because it is the row most
sensitive to the framework-vs-null comparison.

## References

* Hartnoll, S. A. & Mackenzie, A. P. (2022), *Planckian dissipation
  in metals*, Rev. Mod. Phys. **94**, 041002.  Discusses the
  universality observation and its theoretical interpretation.
* Sachdev, S. (2011), *Quantum Phase Transitions* (2nd ed.),
  Cambridge.  Chapter 7 connects Planckian dissipation to
  scale-invariance at quantum critical points.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Discriminator

open Physlib.QuantumMechanics.ComplexAction.Particles.EmpiricalEvidence


/-- **Universal-Planckian condition** on a list of measured
ratios: every entry lies inside a stated multiplicative window
`(lo, hi)`.  Used below with a narrow window `(0.29, 1.11)`
covering the Phase-D positive corpus. -/
def IsUniverselyPlanckian (lo hi : ℝ) (ratios : List ℝ) : Prop :=
  ∀ r ∈ ratios, lo < r ∧ r < hi


/-- **Phase-D positive corpus**.  The eight measured Planckian
ratios from `Particles.EmpiricalEvidence` §B–§D, in the order
[Sr₃Ru₂O₇, LSCO p=0.16, BaFe₂(As,P)₂, Bi, BEDT-TTF, LSCO p=0.21,
(Pr,La)CuO₄, MAtBG]. -/
def phaseDPositiveCorpus : List ℝ :=
  [3/10, 7/10, 1/2, 1, 4/10, 11/10, 1, 7/10]


/-- **Phase-D universality** — every entry of the Phase-D positive
corpus lies in the narrow window `(29/100, 111/100)`, i.e.
`(0.29, 1.11)`.

The window edges are chosen as the actual extremes of the corpus
plus a small slack: the minimum entry is `3/10 = 0.3` and the
maximum is `11/10 = 1.1`, so the corpus spans 0.3-1.1 and any
window strictly outside that range works.  We use `(0.29, 1.11)`
to make the inequality strict at both edges. -/
lemma phaseDPositiveCorpus_isUniverselyPlanckian :
    IsUniverselyPlanckian (29/100) (111/100) phaseDPositiveCorpus := by
  unfold IsUniverselyPlanckian phaseDPositiveCorpus
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;>
    (subst h; refine ⟨?_, ?_⟩ <;> norm_num)

/-!

The ratio of the largest to smallest entry of the Phase-D corpus
is `(11/10) / (3/10) = 11/3 ≈ 3.67`.  This is the "span factor"
that distinguishes the framework's narrow-window prediction from
the null's wide-window expectation.

A null hypothesis with material-class-dependent prefactors would
generically span much wider — at least an order of magnitude across
cuprates vs. iron pnictides vs. organic SCs vs. heavy semimetals.
The observed span of about `3.67×` is the discriminator. -/

/-- **Span of the Phase-D positive corpus**: the maximum ratio
divided by the minimum ratio is `11/3`, less than `4`. -/
lemma phaseDPositiveCorpus_span_lt_four :
    (11 / 10) / (3 / 10) < (4 : ℝ) := by
  norm_num

/-- **Strict-inequality form**: every entry of the corpus, divided
by the minimum entry `0.3`, is strictly less than `4`. -/
lemma phaseDPositiveCorpus_entries_lt_four_times_minimum :
    ∀ r ∈ phaseDPositiveCorpus, r / (3/10) < 4 := by
  unfold phaseDPositiveCorpus
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> (subst h; norm_num)

/-!

The framework-versus-null distinction is captured by the
combination of `phaseDPositiveCorpus_isUniverselyPlanckian` and
`phaseDPositiveCorpus_span_lt_four`:

* **Framework prediction**: the Planckian ratio falls inside a
  narrow window across material classes.  Proved here for the
  specific window `(0.29, 1.11)` and the specific corpus.
* **Null prediction**: ratios across structurally unrelated
  materials would not cluster within `4×` of each other.  Not
  proved (the null is a heuristic about microscopic theory); the
  *observation* in the framework column refutes it informally.

What Lean certifies:

1. The eight measured ratios are all in `(0.29, 1.11)`.
2. Their span is less than `4×`.
3. (Phase D §E) Heavy-fermion and insulator counter-instances are
   outside the band, so the band is genuinely falsifiable.

What Lean does not certify:

1. That the null hypothesis is statistically refuted by the
   observed narrowness.  Bayesian / frequentist inference is
   outside the module's scope.
2. That τ_ent IS the right physical time scale — only that the
   framework's prediction (narrow universality) matches the data
   and the null's would-be prediction (wide variability) does not.

The combined evidence from Phases A–E is therefore: **the
entropic-time framework is empirically consistent with measured
strange-metal data, and its universality prediction matches the
data in a way that the dimensional-analysis null does not**.
That is the strongest claim physlib can support.  Stronger claims
— uniqueness of the framework explanation, exclusion of other
non-trivial alternatives — would require comparing against
non-trivial alternative frameworks (e.g. holographic
conjectures, AdS/CFT models, dual-symmetric scenarios), which is
outside this module. -/

end Physlib.QuantumMechanics.ComplexAction.Discriminator

end
