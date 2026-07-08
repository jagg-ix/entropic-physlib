/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

/-!
# The complex Levi-Civita gravitational tensor: the d'Alembert balance of the complex Einstein equations

Extends Levi-Civita's gravitational/inertial tensor (`LeviCivita.GravitationalTensor`, the real d'Alembert
balance `T + A = 0`) to the **complex** Einstein equations of `ComplexEinstein.FieldEquations` (the complex
Einstein tensor `𝒢 = G + iΛ`, the entropic stress `S_μν`).

The **complex gravitational/inertial tensor** is `1/κ` times the complex Einstein tensor,

  `𝒜 = −(1/κ) 𝒢 = −(1/κ)(G + iΛ)`   (`complexGravitationalTensor`),

so the complex Einstein equation `𝒢 = κ(T + iS)` becomes the **complex d'Alembert balance**

  `(T + iS) + 𝒜 = 0`   (`complex_dAlembert_balance`):

the complex matter+entropic source and the complex gravitational/inertial tensor identically cancel. Its
**real part is Levi-Civita's gravitational tensor** `Re 𝒜 = A = −(1/κ)G` (`complexGravitationalTensor_re`),
so the real d'Alembert balance is the genuine GR balance `T + A = 0`; its **imaginary part** is the
entropic gravitational tensor `Im 𝒜 = −(1/κ)Λ` (`complexGravitationalTensor_im`), which balances the
entropic stress `S` (`Λ = κS`). At equilibrium (`Λ = 0`, `S = 0`) the imaginary tensor vanishes
(`complexGravitationalTensor_im_equilibrium`) and the complex balance reduces to the real Levi-Civita one.

So Levi-Civita's gravitational tensor is the real part of the complex gravitational tensor of the
Nagao–Nielsen complex action: the reversible geometric sector, with the entropic stress as the imaginary
source.

* **§A — the complex gravitational tensor and its real/imaginary parts** (`complexGravitationalTensor`,
  `complexGravitationalTensor_re`, `complexGravitationalTensor_im`,
  `complexGravitationalTensor_im_equilibrium`).
* **§B — the complex d'Alembert balance** (`complex_dAlembert_balance`).

## References

* T. Levi-Civita (arXiv:physics/9906004), the gravitational tensor `A = (1/κ)G`. structures:
  `LeviCivita.GravitationalTensor` (`gravitationalTensor`), `ComplexEinstein.FieldEquations`
  (`complexEinsteinTensor`, `complexStressEnergy`, `complexEinsteinFieldEquation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

variable {ι : Type*}

/-! ## §A — the complex gravitational (inertial) tensor -/

/-- **The complex Levi-Civita gravitational tensor** `𝒜 = −(1/κ)(G + iΛ)` — `1/κ` times the complex
Einstein tensor `𝒢 = G + iΛ` (sign chosen for the complex d'Alembert balance `(T + iS) + 𝒜 = 0`). -/
noncomputable def complexGravitationalTensor (G Λ : Matrix ι ι ℝ) (κ : ℝ) : Matrix ι ι ℂ :=
  (-(1 / κ)) • complexEinsteinTensor G Λ

/-- **[Real part is the Levi-Civita gravitational tensor] `Re 𝒜 = −(1/κ)G`.** With `G = einsteinTensor`,
the real part is exactly Levi-Civita's `gravitationalTensor`. -/
theorem complexGravitationalTensor_re (G Λ : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor G Λ κ).map Complex.re = (-(1 / κ)) • G := by
  rw [complexGravitationalTensor, complexEinsteinTensor, smul_complexCombine, complexCombine_map_re]

/-- **[Imaginary part is the entropic gravitational tensor] `Im 𝒜 = −(1/κ)Λ`.** -/
theorem complexGravitationalTensor_im (G Λ : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor G Λ κ).map Complex.im = (-(1 / κ)) • Λ := by
  rw [complexGravitationalTensor, complexEinsteinTensor, smul_complexCombine, complexCombine_map_im]

/-- **[The real part is Levi-Civita's gravitational tensor] `Re 𝒜 = A`.** With the real Einstein tensor,
the real part of the complex gravitational tensor is exactly the Levi-Civita gravitational/inertial
tensor. -/
theorem complexGravitationalTensor_re_eq_leviCivita (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
      = gravitationalTensor Ric scalarR g κ :=
  complexGravitationalTensor_re (einsteinTensor Ric scalarR g) Λ κ

/-- **[Equilibrium: no imaginary gravitational tensor] `Im 𝒜 = 0` at `Λ = 0`.** With the imaginary
curvature off, the complex gravitational tensor is real — the complex d'Alembert balance reduces to the
real Levi-Civita balance. -/
theorem complexGravitationalTensor_im_equilibrium (G : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor G 0 κ).map Complex.im = 0 := by
  rw [complexGravitationalTensor_im, smul_zero]

/-! ## §B — the complex d'Alembert balance -/

/-- **[The complex d'Alembert balance] `(T + iS) + 𝒜 = 0`.** On a solution of the complex Einstein
equation `𝒢 = κ(T + iS)` (the Nagao–Nielsen complex action, `κ ≠ 0`), the complex matter+entropic source
and the complex gravitational/inertial tensor identically cancel — Levi-Civita's d'Alembert balance
complexified. -/
theorem complex_dAlembert_balance (G Λ T S : Matrix ι ι ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation G Λ T S κ) :
    complexStressEnergy T S + complexGravitationalTensor G Λ κ = 0 := by
  unfold complexGravitationalTensor
  unfold complexEinsteinFieldEquation at h
  rw [h, smul_smul, show -(1 / κ) * κ = -1 from by field_simp, neg_one_smul, add_neg_cancel]

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor

end
