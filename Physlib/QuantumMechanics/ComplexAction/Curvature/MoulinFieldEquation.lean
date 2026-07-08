/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinEnergyMomentumDecomposition

/-!
# Moulin's 4-index field equation reduces to the Einstein field equation

Links the generalized 4-index gravitational field equation (`GravitationalFieldEquations.MoulinEnergyMomentumDecomposition`) to physlib's
ordinary 2-index Einstein field equation (`ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation`). This
is the central consistency result of F. Moulin, *Generalization of Einstein's gravitational field equations*
(arXiv:2405.03698): the new equation `G_{ijkl} = χ T_{ijkl}` (Eq. 31) contains, but generalizes, Einstein's
`G_{μν} = κ T_{μν}` — contracting recovers it exactly (Eqs. 30, 33).

* `FourIndexEinsteinFieldEquation` — the 4-index field equation `G_{ijkl} = χ T_{ijkl}` as a `Prop`.
* `fourIndexField_imp_einsteinField` (Moulin Eqs. 30/33) — the 4-index equation **implies** the 2-index
  Einstein field equation `G_{bd} = χ (gᵃᶜ T_{abcd})` on the contracted source.
* `energyMomentum_satisfies_fourIndexField` — the constructed total energy-momentum tensor `T = G/χ`
  solves the 4-index equation (for `χ ≠ 0`).

## References

* F. Moulin (2024), arXiv:2405.03698, §4.1–4.2, Eqs. 30–33. structure: `Physlib`
  (`GravitationalFieldEquations.MoulinEnergyMomentumDecomposition`, `ComplexEinstein.EinsteinFieldEquationsPhysLean`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {g gInv : Matrix ι ι ℝ}

/-- **Moulin's 4-index gravitational field equation** `G_{ijkl} = χ T_{ijkl}` (Eq. 31), with the generalized
Einstein tensor on the left and a 4-index energy-momentum tensor `T4` on the right. -/
def FourIndexEinsteinFieldEquation (a : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ) (Rm : RiemannTensor ι)
    (χ : ℝ) (T4 : RiemannTensor ι) : Prop :=
  fourIndexEinsteinTensor a (Fintype.card ι) g Ric scalarR Rm = χ • T4

/-- **[Moulin Eqs. 30/33] the 4-index field equation implies the ordinary Einstein field equation.**
Contracting `G_{ijkl} = χ T_{ijkl}` over its first and third indices yields the 2-index Einstein equation
`G_{bd} = χ (gᵃᶜ T_{abcd})` — the generalized theory contains general relativity. -/
theorem fourIndexField_imp_einsteinField (a χ : ℝ) (T4 : RiemannTensor ι)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0)
    (hfield : FourIndexEinsteinFieldEquation a g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm χ T4) :
    einsteinFieldEquation (ricci gInv Rm) (scalarCurvature gInv Rm) g (ricci gInv T4) χ := by
  rw [einsteinFieldEquation, ← fourIndexEinstein_contraction a hg hgi hinv h hn1 hn2,
    show fourIndexEinsteinTensor a (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm
      = χ • T4 from hfield, ricci_smul]

omit [DecidableEq ι] in
/-- **The constructed total energy-momentum tensor `T = G/χ` solves the 4-index field equation** `G = χ T`
(for `χ ≠ 0`). -/
theorem energyMomentum_satisfies_fourIndexField (a χ : ℝ) (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm : RiemannTensor ι) (hχ : χ ≠ 0) :
    FourIndexEinsteinFieldEquation a g Ric scalarR Rm χ
      (fourIndexEnergyMomentum χ a (Fintype.card ι) g Ric scalarR Rm) := by
  rw [FourIndexEinsteinFieldEquation, fourIndexEnergyMomentum, smul_smul, mul_inv_cancel₀ hχ, one_smul]

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
