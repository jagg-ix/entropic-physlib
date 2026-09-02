/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
meta import Zil

/-!
# The Wilson-loop area-law criterion for confinement

The static quark–antiquark potential is read off from a rectangular Wilson loop of spatial extent `R` and
temporal extent `T` via `V(R) = −lim_{T→∞} (1/T) log⟨W(R,T)⟩`.  Two behaviours are distinguished:

* **Area law** `⟨W⟩ ∼ exp(−σ R T)` ⟹ `V(R) = σ R`, a **linear** potential — the energy to separate the pair
  grows without bound, so the quarks are **confined** (string tension `σ > 0`).
* Perimeter law `⟨W⟩ ∼ exp(−c(R+T))` ⟹ `V(R)` bounded — the pair can be separated, i.e. deconfined.

This is the *criterion* (Wilson 1974): the area law with positive string tension is the definition of a
confining potential.  It is not a proof that QCD exhibits the area law.

* `wilsonLoopAreaLaw`, `staticQuarkPotential` — `exp(−σRT)` and the extracted `V(R) = σR`.
* `wilsonLoop_potential` — `−(1/T) log⟨W⟩ = σ R` (the potential extraction).
* `IsConfining`, `staticQuarkPotential_confining` — `σ > 0 ⟹` the linear potential is unbounded above
  (confinement).

Honest scope: the algebraic potential extraction from an assumed area law, and that a positive string
tension yields an unbounded (confining) potential; whether QCD *realizes* the area law — the actual
confinement problem — is not addressed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.WilsonLoopConfinementCriterion

open Real

/-- **The Wilson-loop area law** `⟨W(R,T)⟩ = exp(−σ R T)` (string tension `σ`). -/
def wilsonLoopAreaLaw (σ R T : ℝ) : ℝ := Real.exp (-(σ * R * T))

/-- **The static quark potential** `V(R) = σ R` extracted from the area law (a linear potential). -/
def staticQuarkPotential (σ R : ℝ) : ℝ := σ * R

/-- **A potential confines** when it is unbounded above — the pair cannot be separated to finite energy. -/
def IsConfining (V : ℝ → ℝ) : Prop := ∀ M : ℝ, ∃ r : ℝ, 0 ≤ r ∧ M < V r

/-- **The area law yields the linear static potential** `−(1/T) log⟨W(R,T)⟩ = σ R`. -/
@[zil_level physical_theorem]
theorem wilsonLoop_potential (σ R T : ℝ) (hT : 0 < T) :
    -(Real.log (wilsonLoopAreaLaw σ R T)) / T = staticQuarkPotential σ R := by
  unfold wilsonLoopAreaLaw staticQuarkPotential
  rw [Real.log_exp, neg_neg, mul_div_assoc, div_self hT.ne', mul_one]

/-- **A positive string tension confines** — the linear potential `V(R) = σ R` with `σ > 0` is unbounded
above, so infinite energy is required to separate the quark pair. -/
@[zil_level physical_theorem]
theorem staticQuarkPotential_confining (σ : ℝ) (hσ : 0 < σ) :
    IsConfining (staticQuarkPotential σ) := by
  intro M
  have hσ' : σ ≠ 0 := hσ.ne'
  refine ⟨(|M| + 1) / σ, div_nonneg (by positivity) hσ.le, ?_⟩
  have key : staticQuarkPotential σ ((|M| + 1) / σ) = |M| + 1 := by
    unfold staticQuarkPotential; field_simp
  rw [key]
  linarith [le_abs_self M]

end Physlib.QuantumMechanics.ComplexAction.Particles.WilsonLoopConfinementCriterion

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.WilsonLoopConfinementCriterion

zil attach wilsonLoop_potential where
  supported_by @ "lean:HermitianMat.log_exp",
  formalizes @ "claim:the-wilson-loop-area-law-yields-the-linear-static-quark-potential-minus-one-over-t-times-the-log-of-the-area-law-loop-equals-the-string-tension-times-the-separation"

zil attach staticQuarkPotential_confining where
  formalizes @ "claim:a-positive-string-tension-confines-the-linear-static-quark-potential-is-unbounded-above-so-infinite-energy-is-required-to-separate-the-quark-antiquark-pair"

zil_file_contract physlib.wilsonLoopConfinementCriterion where
  promises "The Wilson-loop area-law criterion for confinement. The static quark-antiquark potential is read off from a rectangular Wilson loop of spatial extent R and temporal extent T as minus the large-T limit of one over T times the log of the loop expectation. The area law, the loop decaying like the exponential of minus the string tension times the loop area R times T, yields the linear potential the string tension times the separation. This linear potential extraction is proved: minus one over T times the log of the area-law loop equals the string tension times the separation. A potential confines when it is unbounded above, so that the pair cannot be separated to finite energy; a positive string tension makes the linear potential unbounded above, hence confining. This is the Wilson criterion: the area law with positive string tension is the definition of a confining potential. Honest scope: the algebraic potential extraction from an assumed area law and that a positive string tension yields an unbounded confining potential; whether QCD realizes the area law, the actual confinement problem, is not addressed."
  at_level physical_theorem
  contract_status satisfied
  requires_objects []
  forbids_substitutes [
    "reading the area-law criterion as a proof that QCD exhibits the area law or a solution of the confinement problem"
  ]
  witnessed_by [
    wilsonLoop_potential,
    staticQuarkPotential_confining
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.wilsonLoopConfinementCriterion
