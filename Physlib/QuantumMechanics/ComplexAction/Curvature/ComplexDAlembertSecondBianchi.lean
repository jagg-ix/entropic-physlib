/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor

/-!
# The complex d'Alembert balance and the second Bianchi identity: source conservation

Links the **complex d'Alembert balance** `(T + iS) + 𝒜 = 0` (`LeviCivita.ComplexLeviCivitaGravitationalTensor`) to
the **second (contracted) Bianchi identity** `∇^μ𝒢_μν = 0` (`ComplexEinstein.FieldEquations`,
`complexBianchi_iff`).

This is Levi-Civita's validation argument (arXiv:physics/9906004, Eq. 12) complexified. The complex
gravitational/inertial tensor `𝒜 = −(1/κ)𝒢` is a scalar multiple of the complex Einstein tensor, so the
second Bianchi identity `∇^μ𝒢 = 0` makes it **divergence-free**:

  `∇^μ𝒜_μν = 0`   (`complexGravitationalTensor_divergence_free`).

Combined with the d'Alembert balance `(T + iS) = −𝒜`, the complex source `T + iS` (energy–momentum plus
entropic stress) is therefore **conserved**: the second Bianchi identity forces
`∇^μT_μν = 0` and `∇^μS_μν = 0` (`complex_dAlembert_bianchi`). The conservation of energy–momentum is not
an extra postulate — it is the divergence-freedom of the gravitational tensor, i.e. the second Bianchi
identity, read through the d'Alembert balance.

* **§A — the complex gravitational tensor is divergence-free** (`complexGravitationalTensor_eq`,
  `complexGravitationalTensor_divergence_free`).
* **§B — the d'Alembert balance + second Bianchi = source conservation** (`complex_dAlembert_bianchi`).

## References

* T. Levi-Civita (arXiv:physics/9906004, Eq. 12): the contracted Bianchi identity validates the field
  equations and gives the vanishing divergence of the energy tensor. structures:
  `LeviCivita.ComplexLeviCivitaGravitationalTensor` (`complexGravitationalTensor`, `complex_dAlembert_balance`),
  `ComplexEinstein.FieldEquations` (`complexBianchi_iff`, `complexEinstein_conservation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ComplexDAlembertSecondBianchi

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor

variable {ι : Type*}

/-! ## §A — the complex gravitational tensor is divergence-free (second Bianchi) -/

/-- **[The complex gravitational tensor as a rescaled Einstein tensor] `𝒜 = 𝒢[(−1/κ)G, (−1/κ)Λ]`.** -/
theorem complexGravitationalTensor_eq (G Λ : Matrix ι ι ℝ) (κ : ℝ) :
    complexGravitationalTensor G Λ κ
      = complexEinsteinTensor ((-(1 / κ)) • G) ((-(1 / κ)) • Λ) := by
  simp only [complexGravitationalTensor, complexEinsteinTensor, smul_complexCombine]

/-- **[The complex gravitational tensor is divergence-free] `∇^μ𝒜_μν = 0`** from the second Bianchi
identity `∇^μ𝒢 = 0`. Since `𝒜 = −(1/κ)𝒢` is a scalar multiple of the complex Einstein tensor, the
contracted Bianchi identity extends. -/
theorem complexGravitationalTensor_divergence_free (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (G Λ : Matrix ι ι ℝ) (κ : ℝ) (h : complexDiv Div (complexEinsteinTensor G Λ) = 0) :
    complexDiv Div (complexGravitationalTensor G Λ κ) = 0 := by
  obtain ⟨hG, hΛ⟩ := (complexBianchi_iff Div G Λ).mp h
  rw [complexGravitationalTensor_eq, complexBianchi_iff]
  exact ⟨by rw [map_smul, hG, smul_zero], by rw [map_smul, hΛ, smul_zero]⟩

/-! ## §B — the d'Alembert balance + second Bianchi = source conservation -/

/-- **[The d'Alembert balance and the second Bianchi identity give source conservation].** On a solution
of the complex Einstein equation `𝒢 = κ(T + iS)` (`κ ≠ 0`) satisfying the second Bianchi identity
`∇^μ𝒢 = 0`:

* the complex gravitational/inertial tensor is divergence-free, `∇^μ𝒜 = 0` (second Bianchi);
* the complex d'Alembert balance `(T + iS) + 𝒜 = 0` holds;
* hence the complex source is conserved, `∇^μT = 0` and `∇^μS = 0`.

The conservation of energy–momentum and entropic stress is the divergence-freedom of the gravitational
tensor — the second Bianchi identity read through Levi-Civita's d'Alembert balance. -/
theorem complex_dAlembert_bianchi (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ)
    (hBianchi : complexDiv Div (complexEinsteinTensor (einsteinTensor Ric scalarR g) Λ) = 0) :
    complexDiv Div (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ) = 0
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0
      ∧ Div T = 0 ∧ Div S = 0 := by
  refine ⟨complexGravitationalTensor_divergence_free Div (einsteinTensor Ric scalarR g) Λ κ hBianchi,
    complex_dAlembert_balance (einsteinTensor Ric scalarR g) Λ T S κ hκ hEFE, ?_, ?_⟩ <;>
    [exact (complexEinstein_conservation Div Ric scalarR g T S Λ κ hEFE hBianchi hκ).1;
     exact (complexEinstein_conservation Div Ric scalarR g T S Λ κ hEFE hBianchi hκ).2]

end Physlib.QuantumMechanics.ComplexAction.Curvature.ComplexDAlembertSecondBianchi

end
