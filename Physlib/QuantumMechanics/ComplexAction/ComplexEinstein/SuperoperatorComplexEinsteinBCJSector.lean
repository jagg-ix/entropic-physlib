/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.SuperoperatorGravitationalTensor
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy

/-!
# The superoperator and complex Einstein equations incorporate the mapped BCJ sector

Updates the fused EM–Lorentz–Dirac superoperator (`Electromagnetic.EMSuperoperatorComplexEinsteinDirac`,
`Electromagnetic.SuperoperatorGravitationalTensor`) and the complex Einstein field equations
(`ComplexEinstein.FieldEquations`) to **incorporate the BCJ double-copy sector**
(`BCJDoubleCopy.ColorKinematicsDoubleCopy`, `LeviCivita.BianchiDoubleCopy`). The double copy maps the **gauge**
(EM / Maxwell–Faraday) sector that the superoperator records to the **gravity** (complex Einstein) sector,
`gravity = gauge²`, on two faces:

* **the entropic Einstein source is the double copy of two gauge actions.** The superoperator's entropic
  gap is the imaginary Einstein energy `m_I c² = Im E` (`dirac_entropic_gap_eq_imaginary_einstein`), which
  also sources the imaginary sector of the complex gravitational tensor `Im 𝒜 = −S`
  (`superoperator_complexGravitationalTensor`). Identifying `Im E` with a sum of two gauge entropic actions
  `S₁ + S₂`, its path-integral weight **factorizes as the BCJ double copy**
  `exp(−Im E) = exp(−S₁)·exp(−S₂)` (`entropic_einstein_doublecopy_factorizes`,
  `bcj_doublecopy_fk_factorization`): the gravity entropic source is `gauge²`;

* **the gauge Bianchi maps to the gravity conservation.** The superoperator's EM sector includes the
  Maxwell–Faraday cyclic identity `k_λF_{μν} + k_μF_{νλ} + k_νF_{λμ} = 0` (the **first Bianchi** / BCJ
  kinematic Jacobi); its gravity dual is the **contracted second Bianchi** (Levi-Civita Eq. 12), which
  conserves the complex Einstein source `∇^μ T_{μν} = 0`
  (`superoperator_em_gravity_bianchi_doublecopy`, reusing `firstBianchi_double_copy`,
  `eq12_discharges_bcj`).

So the superoperator's complex gravitational tensor and the complex Einstein source now include the mapped
BCJ sector: the entropic Einstein source is the double copy (`gauge²`) of the gauge entropic actions, and
the EM-sector first Bianchi double-copies to the gravity-sector conservation.

* **§A — the entropic Einstein source is the BCJ double copy** (`entropic_einstein_doublecopy_factorizes`).
* **§B — the gauge Bianchi double-copies to the gravity conservation**
  (`superoperator_em_gravity_bianchi_doublecopy`).
* **§C — the superoperator + complex Einstein equations with the BCJ sector**
  (`superoperator_complexEinstein_incorporates_bcj`).

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993); T. Levi-Civita (arXiv:physics/9906004, §7).
  structures: `Electromagnetic.SuperoperatorGravitationalTensor` (`superoperator_complexGravitationalTensor`),
  `Electromagnetic.EMSuperoperatorComplexEinsteinDirac` (`dirac_entropic_gap_eq_imaginary_einstein`),
  `BCJDoubleCopy.ColorKinematicsDoubleCopy` (`bcj_doublecopy_fk_factorization`), `LeviCivita.BianchiDoubleCopy`
  (`firstBianchi_double_copy`, `eq12_discharges_bcj`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSuperoperatorComplexEinsteinDirac
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.SuperoperatorGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

variable {ι : Type*}

/-! ## §A — the entropic Einstein source is the BCJ double copy (gravity = gauge²) -/

/-- **[The entropic Einstein source is the double copy of two gauge actions] `exp(−Im E) = exp(−S₁)·exp(−S₂)`.**
The superoperator's entropic gap is the imaginary Einstein energy `m_I c² = Im E`
(`dirac_entropic_gap_eq_imaginary_einstein`). Identifying it with a sum of two gauge entropic actions
`Im E = S₁ + S₂`, its path-integral (Feynman–Kac) weight factorizes as the BCJ double copy
`exp(−Im E) = exp(−S₁)·exp(−S₂)` — the gravity entropic source is `gauge²`. -/
theorem entropic_einstein_doublecopy_factorizes (m_R m_I c S₁ S₂ : ℝ)
    (h : m_I * c ^ 2 = S₁ + S₂) :
    Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂) := by
  rw [← dirac_entropic_gap_eq_imaginary_einstein m_R m_I c, h]
  exact bcj_doublecopy_fk_factorization S₁ S₂

/-! ## §B — the gauge Bianchi double-copies to the gravity conservation -/

/-- **[The superoperator's EM Bianchi double-copies to the complex Einstein conservation].** The
superoperator's EM (gauge) sector includes the Maxwell–Faraday cyclic identity (the first Bianchi / BCJ
kinematic Jacobi); its gravity dual is the contracted second Bianchi (Levi-Civita Eq. 12), which conserves
the complex Einstein source `∇^μ T_{μν} = 0`. The gauge-side Bianchi of the superoperator maps to the
gravity-side conservation of the complex Einstein equations. -/
theorem superoperator_em_gravity_bianchi_doublecopy
    {R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ} (hFB : FirstBianchi R) (a b c d : Fin 4)
    (k A_g : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) :
    (k lam * faraday k A_g μ ν + k μ * faraday k A_g ν lam + k ν * faraday k A_g lam μ = 0)
      ∧ divT = 0 :=
  ⟨(firstBianchi_double_copy hFB a b c d k A_g lam μ ν).2,
    eq12_discharges_bcj divRicci gradScalar divT κ hκ hField hBianchi⟩

/-! ## §C — the superoperator + complex Einstein equations with the mapped BCJ sector -/

/-- **[The superoperator and complex Einstein equations incorporate the mapped BCJ sector].** On a solution
of the complex Einstein equation `𝒢 = κ(T + iS)` (`κ ≠ 0`), with the superoperator's entropic gap split
across two gauge actions `m_I c² = S₁ + S₂`:

* the superoperator uses the complex gravitational tensor — `m_I c² = Im E`, `Re 𝒜 = A` (Levi-Civita's true
  tensor), `Im 𝒜 = −S` (the entropic source), and the complex d'Alembert balance `(T + iS) + 𝒜 = 0`;
* the entropic Einstein source is the **BCJ double copy** of the two gauge actions,
  `exp(−Im E) = exp(−S₁)·exp(−S₂)` (`gravity = gauge²`).

So the superoperator's complex gravitational tensor and the complex Einstein source include the mapped BCJ
sector: the entropic Einstein source is the double copy of the gauge entropic actions. -/
theorem superoperator_complexEinstein_incorporates_bcj (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ m_R m_I c : ℝ) (hκ : κ ≠ 0)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ)
    (S₁ S₂ : ℝ) (hsplit : m_I * c ^ 2 = S₁ + S₂) :
    ((m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
          = gravitationalTensor Ric scalarR g κ
      ∧ (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.im = -S
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0)
      ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂) :=
  ⟨superoperator_complexGravitationalTensor Ric scalarR g Λ T S κ m_R m_I c hκ hEFE,
    entropic_einstein_doublecopy_factorizes m_R m_I c S₁ S₂ hsplit⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.SuperoperatorComplexEinsteinBCJSector

end
