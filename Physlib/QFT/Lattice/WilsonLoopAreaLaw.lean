/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Wilson loops, the area law, and the center-vortex string tension

Ports `lean4/QCDVortex/WilsonLattice.lean` of the qcd-vortex-entanglement tree (Lean layer own
authorship; physics context: Greensite's center-vortex confinement mechanism, LatticeQCD.jl
observables):

* `wilsonAction` `S_W = β(1−P) ≥ 0` with the flat-connection zero;
* `satisfiesAreaLaw` and `areaLaw_implies_decay` — an area law with positive string tension
  forces `W(R,T) < 1`;
* `vortexStringTension` `σ_v(ρ) = −log(1−2ρ)` — positive exactly in the condensed regime
  `ρ ∈ (0,½)`, zero at `ρ = 0`, strictly increasing (`vortexStringTension_strictMono_on`),
  and the vortex model *saturates* its own area law (`vortexAreaLaw_exp`);
* `isConfining_implies_positiveStringTension`, `linear_potential_pos` — confinement gives a
  linearly rising quark–antiquark potential.

**Honest layering.**  Exact real analysis on the observable formulas; the derivation of the
`(1−2ρ)^A` piercing factor from center-vortex counting and the Monte-Carlo estimates of `ρ`
are the physics layer, cited not re-proven.  The exact strong-coupling Wilson-loop machinery
on group carriers is `QFT.PathIntegral.FiniteWilsonGaugeModel`; this module is the
observable-level layer both share.

## References

* J. Greensite, *The confinement problem in lattice gauge theory*,
  Prog. Part. Nucl. Phys. **51** (2003).
* Source: `lean4/QCDVortex/WilsonLattice.lean` (own authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QFT.Lattice.WilsonLoopAreaLaw

open Real

/-! ## 1. Plaquette and Wilson action -/

/--
Single-plaquette Wilson action contribution:
  S_W(β, P) = β · (1 − P)
where P = (1/NC) Re Tr[P_{μν}] ∈ [0,1] is the normalized plaquette.
-/
noncomputable def wilsonAction (β P : ℝ) : ℝ := β * (1 - P)

/-- Wilson action is nonneg for β ≥ 0 and P ≤ 1. -/
theorem wilsonAction_nonneg {β P : ℝ} (hβ : 0 ≤ β) (hP : P ≤ 1) :
    0 ≤ wilsonAction β P :=
  mul_nonneg hβ (by linarith)

/-- At flat connection (P = 1), action vanishes. -/
theorem wilsonAction_zero_at_flat (β : ℝ) : wilsonAction β 1 = 0 := by
  simp [wilsonAction]

/-- Plaquette average: (1/NC) Re Tr[P] averaged over all plaquettes.
    Normalization: 6 independent μ<ν planes × NV sites × NC colors. -/
noncomputable def plaquetteAvg (P_total : ℝ) (NV NC : ℕ) : ℝ :=
  P_total / (6 * NV * NC)

/-! ## 2. Area law and string tension -/

/--
Area law: the Wilson loop W(R,T) decays exponentially in the spatial–temporal
area R·T with rate σ (the string tension).
-/
def satisfiesAreaLaw (W : ℝ → ℝ → ℝ) (σ : ℝ) : Prop :=
  ∀ R T : ℝ, 0 < R → 0 < T → W R T ≤ exp (-σ * R * T)

/-- For σ > 0, the area law forces W(R,T) < 1. -/
theorem areaLaw_implies_decay {W : ℝ → ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (h : satisfiesAreaLaw W σ) (R T : ℝ) (hR : 0 < R) (hT : 0 < T) :
    W R T < 1 := by
  calc W R T ≤ exp (-σ * R * T) := h R T hR hT
    _ < exp 0 := by
        apply Real.exp_lt_exp.mpr
        nlinarith [mul_pos (mul_pos hσ hR) hT]
    _ = 1 := Real.exp_zero

/-! ## 3. Center vortex string tension -/

/--
Vortex string tension:
  σ_v(ρ) = −log(1 − 2ρ)

Derived from: each center vortex linking through a Wilson-loop minimal area
of size A contributes a factor (1 − 2ρ)^A to ⟨W⟩, so
  ⟨W(R,T)⟩ = (1 − 2ρ)^{R·T} = exp(R·T · log(1 − 2ρ)) = exp(−σ_v · R·T).
-/
noncomputable def vortexStringTension (ρ : ℝ) : ℝ := -Real.log (1 - 2 * ρ)

/-- σ_v > 0 for ρ ∈ (0, ½). -/
theorem vortexStringTension_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ < 1/2) :
    0 < vortexStringTension ρ := by
  simp only [vortexStringTension]
  apply neg_pos.mpr
  apply Real.log_neg <;> linarith

/-- σ_v(0) = 0: no vortices, no confinement. -/
theorem vortexStringTension_zero : vortexStringTension 0 = 0 := by
  simp [vortexStringTension]

/-- σ_v is strictly increasing on (0, ½). -/
theorem vortexStringTension_strictMono_on :
    StrictMonoOn vortexStringTension (Set.Ioo 0 (1/2)) := by
  intro a ⟨_, ha2⟩ b ⟨_, hb2⟩ hab
  simp only [vortexStringTension]
  apply neg_lt_neg
  apply Real.log_lt_log <;> linarith

/--
Vortex area law (continuum model): the Wilson loop
  W(R, T) = exp(log(1−2ρ) · R · T)
satisfies the area law with string tension σ_v = −log(1−2ρ).
The two sides are equal (the area law is saturated by the vortex model).
-/
theorem vortexAreaLaw_exp (ρ : ℝ) :
    satisfiesAreaLaw (fun R T => Real.exp (Real.log (1 - 2 * ρ) * (R * T)))
                     (vortexStringTension ρ) := by
  intro R T _ _
  apply le_of_eq
  simp only [vortexStringTension]
  congr 1; ring

/-! ## 4. Confinement and deconfinement -/

/--
Confinement condition: vortex density ρ ∈ (0, ½) (vortices condensed).
Deconfinement: ρ → 0 (vortex condensate evaporates), σ → 0.
-/
def isConfining (ρ : ℝ) : Prop := 0 < ρ ∧ ρ < 1/2

/-- Confinement implies positive string tension. -/
theorem isConfining_implies_positiveStringTension {ρ : ℝ} (h : isConfining ρ) :
    0 < vortexStringTension ρ :=
  vortexStringTension_pos h.1 h.2

/-- Linear quark-antiquark potential: V(R) = σ·R grows linearly with separation. -/
theorem linear_potential_pos {σ R : ℝ} (hσ : 0 < σ) (hR : 0 < R) : 0 < σ * R :=
  mul_pos hσ hR

end Physlib.QFT.Lattice.WilsonLoopAreaLaw

end
