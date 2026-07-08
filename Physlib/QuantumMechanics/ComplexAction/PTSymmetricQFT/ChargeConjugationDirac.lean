/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
public import Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass

/-!
# Greaves–Thomas §3 charge conjugation on the concrete Dirac structure

`PTSymmetricQFT.ChargeConjugation` defines the abstract Def. 4/5 charge grading (`IsChargePreserving`,
`IsChargeConjugating`) and the two charge conjugations — the `ℂ`-linear `C_#` and the anti-linear `C_∗`.
This bridge instantiates both on the concrete Dirac data already in the repo, so those definitions are
*used*, not merely stated.

* **§A — the chirality grading `γ⁵` as a charge grading** (`dirac_vector_chiralityConjugating`,
  `dirac_chirality_chargePreserving`). Reading `γ⁵` as a `ℤ₂` grading on the spinor space (`(γ⁵)² = 1`,
  eigenspaces = the Weyl chiralities `ψ_L / ψ_R`), the Dirac vector `γ^μ` is **charge-conjugating**
  (it *anti-commutes* with `γ⁵`, `{γ⁵, γ^μ} = 0`, flipping chirality — the off-diagonal mass-coupling
  block), while `γ⁵` itself is **charge-preserving**. This is a concrete instance of Greaves–Thomas
  Definition 4, built from `PTSymmetricQFT.CPTComplexification.γ5_anticomm_γ`. The chirality grading is the
  formal analogue of their particle/anti-particle charge grading `W⁺ / W⁻`.
* **§B — the anti-linear `C_∗` flips the complex fermion mass** (`chargeConj_complexFermionMass`,
  `chargeConj_complexFermionMass_sq`). The anti-linear charge conjugation `C_∗ = conjFactor true`
  (`PTSymmetricQFT.TemporalOrientation`) acts on the Nagao–Nielsen complex mass `m = m_R + i m_I`
  (`Dirac.ComplexWeylDiracFermionMass`) by `m ↦ m_R − i m_I`: charge conjugation negates the dissipative
  imaginary mass `m_I` (the particle ↔ anti-particle decay-width flip) while fixing `m_R`. Consequently the
  real part of `m²` is invariant and its imaginary part (`2 m_R m_I`, the width) changes sign.

So the §3 grading and `C_∗` are anchored to the repo's Dirac `γ`-matrices and its complex mass.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §3 (Definitions 4–5, charge conjugation).
* Repo dependencies: `PTSymmetricQFT.ChargeConjugation` (`IsChargePreserving`, `IsChargeConjugating`);
  `PTSymmetricQFT.CPTComplexification` (`γ5`, `γ5_anticomm_γ`); `PTSymmetricQFT.TemporalOrientation`
  (`conjFactor`); `Dirac.ComplexWeylDiracFermionMass` (`complexFermionMass`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugationDirac

open Matrix Complex spaceTime
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
open Physlib.QuantumMechanics.ComplexAction.Dirac.ComplexWeylDiracFermionMass

/-! ## §A — the chirality grading `γ⁵` as a concrete charge grading -/

/-- **[Def. 4 instance] The Dirac vector `γ^μ` is charge-conjugating w.r.t. the chirality grading `γ⁵`.**
Acting on the spinor space `Fin 4 → ℂ`, `γ^μ` *anti-commutes* with `γ⁵` (`{γ⁵, γ^μ} = 0`,
`PTSymmetricQFT.CPTComplexification.γ5_anticomm_γ`), so it flips chirality `ψ_L ↔ ψ_R` — the concrete analogue
of swapping the particle/anti-particle sectors `W⁺ ↔ W⁻`. -/
theorem dirac_vector_chiralityConjugating (μ : Fin 4) :
    IsChargeConjugating (Matrix.mulVecLin γ5) (Matrix.mulVecLin (γ μ)) := by
  unfold IsChargeConjugating
  ext v
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec]
  rw [show γ μ * γ5 = -(γ5 * γ μ) by rw [γ5_anticomm_γ, neg_neg], Matrix.neg_mulVec]

/-- **[Def. 4 instance] The chirality grading `γ⁵` is charge-preserving** — it commutes with itself, fixing
each chirality eigenspace. -/
theorem dirac_chirality_chargePreserving :
    IsChargePreserving (Matrix.mulVecLin γ5) (Matrix.mulVecLin γ5) := rfl

/-! ## §B — the anti-linear `C_∗` flips the Nagao–Nielsen complex fermion mass -/

/-- **[`C_∗` on the complex mass] Charge conjugation negates the dissipative imaginary mass.** The anti-linear
charge conjugation `C_∗ = conjFactor true` sends the complex fermion mass `m = m_R + i m_I`
(`Dirac.ComplexWeylDiracFermionMass.complexFermionMass`) to `m_R − i m_I`: it fixes the Hermitian mass `m_R` and
flips the sign of the dissipative `m_I` — the particle ↔ anti-particle conjugation. -/
theorem chargeConj_complexFermionMass (m_R m_I : ℝ) :
    conjFactor true (complexFermionMass m_R m_I) = complexFermionMass m_R (-m_I) := by
  simp [conjFactor, complexFermionMass]

/-- **[`C_∗` on `m²`] The mass-squared real part is charge-conjugation invariant; its width flips.** Since
`C_∗` is the complex conjugation, `C_∗(m²) = (C_∗ m)² = (m_R − i m_I)²`: the real part `m_R² − m_I²` is
unchanged and the imaginary part `2 m_R m_I` (the decay width) changes sign. -/
theorem chargeConj_complexFermionMass_sq (m_R m_I : ℝ) :
    conjFactor true (complexFermionMass m_R m_I ^ 2) = complexFermionMass m_R (-m_I) ^ 2 := by
  rw [map_pow, chargeConj_complexFermionMass]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugationDirac

end
