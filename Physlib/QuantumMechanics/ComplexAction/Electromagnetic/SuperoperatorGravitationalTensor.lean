/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor

/-!
# The fused superoperator uses the complex gravitational tensor

Ensures that the fused EM–Lorentz–Dirac superoperator (`Electromagnetic.EMSuperoperatorComplexEinsteinDirac`,
`ComplexEinstein.FusedSuperoperatorComplexEinstein`) — which until now only referenced the *scalar* complex Einstein
**energy** `E_C = m_C c²` (`ComplexEinstein.ComplexMassEinsteinEquations`, `dirac_entropic_gap_eq_imaginary_einstein`:
`m_I c² = Im E_C`) — is tied to the full complex Einstein/Levi-Civita **tensor**
(`ComplexEinstein.FieldEquations`, `LeviCivita.ComplexLeviCivitaGravitationalTensor`).

On a solution of the complex Einstein equation `𝒢 = κ(T + iS)` of the Nagao–Nielsen complex action, the
superoperator's imaginary Einstein source `m_I c²` (the entropic gap) and the complex
gravitational/inertial **tensor** `𝒜 = −(1/κ)𝒢` are the two sides of the same entropic structure:

* the superoperator's imaginary source is `m_I c² = Im E_C` (`dirac_entropic_gap_eq_imaginary_einstein`);
* the complex gravitational tensor's **real part is Levi-Civita's tensor** `Re 𝒜 = A`
  (`complexGravitationalTensor_re_eq_leviCivita`);
* its **imaginary part is the entropic stress** `Im 𝒜 = −S` (since `Λ = κS`);
* and the **complex d'Alembert balance** `(T + iS) + 𝒜 = 0` holds.

So the fused superoperator's entropic Einstein source is the imaginary sector of the complex
gravitational tensor — the superoperator uses the tensor, not just the scalar energy.

* **§A — the fused superoperator uses the complex gravitational tensor**
  (`superoperator_complexGravitationalTensor`).

## References

* structures: `Electromagnetic.EMSuperoperatorComplexEinsteinDirac` (`dirac_entropic_gap_eq_imaginary_einstein`),
  `LeviCivita.ComplexLeviCivitaGravitationalTensor` (`complexGravitationalTensor`),
  `LeviCivita.GravitationalTensor` (`gravitationalTensor`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.SuperoperatorGravitationalTensor

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac

variable {ι : Type*}

/-! ## §A — the fused superoperator uses the complex gravitational tensor -/

/-- **[The fused superoperator uses the complex gravitational tensor].** On a solution of the complex
Einstein equation `𝒢 = κ(T + iS)` (`κ ≠ 0`), the fused EM–Lorentz–Dirac superoperator's imaginary Einstein
source and the complex gravitational/inertial tensor `𝒜 = −(1/κ)𝒢` are one entropic structure:

* the superoperator's imaginary Einstein source is `m_I c² = Im E_C`;
* the complex gravitational tensor's real part is Levi-Civita's tensor `Re 𝒜 = A`;
* its imaginary part is the entropic stress `Im 𝒜 = −S`;
* the complex d'Alembert balance `(T + iS) + 𝒜 = 0` holds.

The superoperator's entropic Einstein source is the imaginary sector of the complex gravitational tensor —
it uses the tensor, not just the scalar complex Einstein energy. -/
theorem superoperator_complexGravitationalTensor (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ m_R m_I c : ℝ) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
          = gravitationalTensor Ric scalarR g κ
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.im = -S
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0 := by
  obtain ⟨_, hΛ⟩ := (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp h
  refine ⟨dirac_entropic_gap_eq_imaginary_einstein m_R m_I c,
    complexGravitationalTensor_re_eq_leviCivita Ric scalarR g Λ κ, ?_,
    complex_dAlembert_balance (einsteinTensor Ric scalarR g) Λ T S κ hκ h⟩
  rw [complexGravitationalTensor_im, hΛ, smul_smul, show -(1 / κ) * κ = -1 from by field_simp,
    neg_one_smul]

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.SuperoperatorGravitationalTensor

end
