/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
meta import Zil

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

* T. Levi-Civita (arXiv:physics/9906004), the gravitational tensor `A = (1/κ)G`. Carriers:
  `LeviCivita.GravitationalTensor` (`gravitationalTensor`), `ComplexEinstein.FieldEquations`
  (`complexEinsteinTensor`, `complexStressEnergy`, `complexEinsteinFieldEquation`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

variable {ι : Type*}


/-- **The complex Levi-Civita gravitational tensor** `𝒜 = −(1/κ)(G + iΛ)` — `1/κ` times the complex
Einstein tensor `𝒢 = G + iΛ` (sign chosen for the complex d'Alembert balance `(T + iS) + 𝒜 = 0`). -/
noncomputable def complexGravitationalTensor (G Λ : Matrix ι ι ℝ) (κ : ℝ) : Matrix ι ι ℂ :=
  (-(1 / κ)) • complexEinsteinTensor G Λ

/-- **[Real part is the Levi-Civita gravitational tensor] `Re 𝒜 = −(1/κ)G`.** With `G = einsteinTensor`,
the real part is exactly Levi-Civita's `gravitationalTensor`. -/
lemma complexGravitationalTensor_re (G Λ : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor G Λ κ).map Complex.re = (-(1 / κ)) • G := by
  rw [complexGravitationalTensor, complexEinsteinTensor, smul_complexCombine, complexCombine_map_re]

/-- **[Imaginary part is the entropic gravitational tensor] `Im 𝒜 = −(1/κ)Λ`.** -/
lemma complexGravitationalTensor_im (G Λ : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor G Λ κ).map Complex.im = (-(1 / κ)) • Λ := by
  rw [complexGravitationalTensor, complexEinsteinTensor, smul_complexCombine, complexCombine_map_im]

/-- **[The real part is Levi-Civita's gravitational tensor] `Re 𝒜 = A`.** With the real Einstein tensor,
the real part of the complex gravitational tensor is exactly the Levi-Civita gravitational/inertial
tensor. -/
lemma complexGravitationalTensor_re_eq_leviCivita (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ).map Complex.re
      = gravitationalTensor Ric scalarR g κ :=
  complexGravitationalTensor_re (einsteinTensor Ric scalarR g) Λ κ

/-- **[Equilibrium: no imaginary gravitational tensor] `Im 𝒜 = 0` at `Λ = 0`.** With the imaginary
curvature off, the complex gravitational tensor is real — the complex d'Alembert balance reduces to the
real Levi-Civita balance. -/
lemma complexGravitationalTensor_im_equilibrium (G : Matrix ι ι ℝ) (κ : ℝ) :
    (complexGravitationalTensor G 0 κ).map Complex.im = 0 := by
  rw [complexGravitationalTensor_im, smul_zero]


/-- **[The complex d'Alembert balance] `(T + iS) + 𝒜 = 0`.** On a solution of the complex Einstein
equation `𝒢 = κ(T + iS)` (the Nagao–Nielsen complex action, `κ ≠ 0`), the complex matter+entropic source
and the complex gravitational/inertial tensor identically cancel — Levi-Civita's d'Alembert balance
complexified. -/
lemma complex_dAlembert_balance (G Λ T S : Matrix ι ι ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation G Λ T S κ) :
    complexStressEnergy T S + complexGravitationalTensor G Λ κ = 0 := by
  unfold complexGravitationalTensor
  unfold complexEinsteinFieldEquation at h
  rw [h, smul_smul, show -(1 / κ) * κ = -1 from by field_simp, neg_one_smul, add_neg_cancel]

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor_re_eq_leviCivita where
  formalizes @ "claim:the-real-part-of-the-complex-gravitational-inertial-tensor-is-exactly-levi-civitas-real-gravitational-tensor-a",
  supported_by @ "object:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.gravitationalTensor"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor_im where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexCombine_map_im",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.smul_complexCombine",
  formalizes @ "claim:the-imaginary-part-of-the-complex-gravitational-inertial-tensor-is-minus-one-over-kappa-times-the-imaginary-curvature-lambda-the-entropic-gravitational-tensor"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor_im_equilibrium where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor_im",
  formalizes @ "claim:at-equilibrium-lambda-equals-zero-the-imaginary-part-of-the-complex-gravitational-tensor-vanishes-the-complex-dalembert-balance-reduces-to-the-real-levi-civita-balance"

zil attach Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complex_dAlembert_balance where
  formalizes @ "claim:the-complex-dalembert-balance-t-plus-i-s-plus-the-complex-gravitational-inertial-tensor-equals-zero-on-a-solution-of-the-complex-einstein-equation-levi-civitas-balance-complexified",
  requires @ "claim:the-real-part-of-the-complex-gravitational-inertial-tensor-is-exactly-levi-civitas-real-gravitational-tensor-a"

zil_file_contract physlib.complexLeviCivitaGravitationalTensor where
  promises "Extends Levi-Civita's gravitational/inertial tensor to the complex Einstein equations of the Nagao-Nielsen complex action. The complex gravitational tensor is A_complex = -(1/kappa)(G + i Lambda); its real part is exactly Levi-Civita's real gravitational tensor (complexGravitationalTensor_re_eq_leviCivita) and its imaginary part is the entropic gravitational tensor -(1/kappa)Lambda (complexGravitationalTensor_im), which vanishes at equilibrium Lambda = 0 so the complex balance reduces to the real one (complexGravitationalTensor_im_equilibrium). On a solution of the complex Einstein equation G_complex = kappa(T + iS) the complex matter+entropic source and the complex gravitational tensor identically cancel: the complex d'Alembert balance (T + iS) + A_complex = 0 (complex_dAlembert_balance) -- Levi-Civita's balance complexified, the geometric foundation of the complete complex Einstein field equations."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.gravitationalTensor"]
  forbids_substitutes ["the complex Einstein tensor construction and the tensor-calculus infrastructure, which are the cited geometric inputs",
    "any dynamics of the entropic sector, only the algebraic complex d'Alembert balance and its real/imaginary decomposition are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor_re_eq_leviCivita,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor_im,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complexGravitationalTensor_im_equilibrium,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor.complex_dAlembert_balance]

/- ZIL-END -/
