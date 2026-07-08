/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-!
# The Levi-Civita gravitational tensor and the d'Alembert balance — the real sector of the NN complex action

Formalizes the **gravitational (inertial) tensor** of T. Levi-Civita (*Rendiconti R. Acc. Lincei* **26**
(1917) 381, translated as arXiv:physics/9906004) and applies it to the Nagao–Nielsen complex-action
gravity (the complex Einstein equations of `ComplexEinstein.FieldEquations`).

Levi-Civita defines (Eq. 13) the gravitational tensor as `1/κ` times the Einstein tensor,

  `A_ik = (1/κ)(G_ik − ½ g_ik G)`   (`gravitationalTensor`, here with the sign that makes the balance
  below hold against the repo's `einsteinFieldEquation` convention `G_μν = κ T_μν`),

so that the Einstein field equation becomes the **d'Alembert balance** (Eq. 10')

  `T_ik + A_ik = 0`   (`dAlembert_balance`),

the matter energy tensor and the gravitational/inertial energy tensor identically cancel — "the nature of
`ds²` is always such as to balance all mechanical actions". The gravitational tensor is the *negative of
the matter tensor* (`gravitationalTensor_eq_neg_matter`), `A = −T`, and (by the contracted Bianchi
identity, Eq. 12) is **divergence-free** whenever the matter tensor is conserved
(`gravitationalTensor_divergence_free`).

**Application to the Nagao–Nielsen complex action.** The complex action `S = S_R + iS_I` yields the
complex Einstein equations `G_μν + iΛ_μν = κ(T_μν + iS_μν)` (`complexEinsteinFieldEquation`). Its **real
sector is exactly the Levi-Civita d'Alembert balance** `T + A = 0` (`complexEinstein_real_is_dAlembert`),
while the imaginary sector `Λ = κ S` is the entropic curvature. So Levi-Civita's gravitational/inertial
tensor is the real, reversible, geometric sector of the Nagao–Nielsen complex action's gravity — the
entropic sector being the imaginary stress.

* **§A — the gravitational tensor and the d'Alembert balance** (`gravitationalTensor`,
  `gravitationalTensor_eq_neg_matter`, `dAlembert_balance`, `gravitationalTensor_divergence_free`).
* **§B — the real sector of the NN complex action** (`complexEinstein_real_is_dAlembert`).

## References

* T. Levi-Civita, *Rend. R. Acc. Lincei* 26 (1917) 381 (arXiv:physics/9906004, trans. Antoci–Loinger):
  the gravitational tensor `A_ik = (1/κ)(G_ik − ½g_ik G)`, the balance `T_ik + A_ik = 0`, `κ = 8πf/c⁴`.
  structures: `ComplexEinstein.EinsteinFieldEquationsPhysLean` (`einsteinTensor`, `einsteinFieldEquation`,
  `bianchi_implies_conservation`), `ComplexEinstein.FieldEquations` (`complexEinsteinFieldEquation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

variable {ι : Type*}

/-! ## §A — the gravitational (inertial) tensor and the d'Alembert balance -/

/-- **The Levi-Civita gravitational (inertial) tensor** `A_ik = (1/κ)(G_ik − ½ g_ik G)` (Eq. 13) — the
energy tensor of the space-time environment, `1/κ` times the Einstein tensor. The sign is taken so that
the d'Alembert balance `T + A = 0` matches the repo's field-equation convention `G_μν = κ T_μν`. -/
noncomputable def gravitationalTensor (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ) (κ : ℝ) :
    Matrix ι ι ℝ :=
  (-(1 / κ)) • einsteinTensor Ric scalarR g

/-- **[The gravitational tensor is the negative matter tensor] `A = −T`** (Eq. 10'). On a solution of the
Einstein field equation, the Levi-Civita gravitational/inertial tensor is exactly minus the matter energy
tensor. -/
theorem gravitationalTensor_eq_neg_matter (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0) (h : einsteinFieldEquation Ric scalarR g T κ) :
    gravitationalTensor Ric scalarR g κ = -T := by
  unfold gravitationalTensor
  unfold einsteinFieldEquation at h
  rw [h, smul_smul, show -(1 / κ) * κ = -1 from by field_simp, neg_one_smul]

/-- **[The d'Alembert balance] `T + A = 0`** (Levi-Civita Eq. 10'). The matter energy tensor and the
gravitational/inertial energy tensor identically cancel — the Einstein field equation as the complete
mechanical equilibrium of d'Alembert's principle. -/
theorem dAlembert_balance (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (h : einsteinFieldEquation Ric scalarR g T κ) :
    T + gravitationalTensor Ric scalarR g κ = 0 := by
  rw [gravitationalTensor_eq_neg_matter Ric scalarR g T κ hκ h, add_neg_cancel]

/-- **[The gravitational tensor is divergence-free] `∇^μ A_μν = 0`** (Eq. 12, the contracted Bianchi
identity). The gravitational/inertial tensor inherits the divergence-freedom of the Einstein tensor (it
is a scalar multiple of it). -/
theorem gravitationalTensor_divergence_free (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ) (κ : ℝ)
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0) :
    Div (gravitationalTensor Ric scalarR g κ) = 0 := by
  rw [gravitationalTensor, map_smul, hBianchi, smul_zero]

/-! ## §B — the real sector of the Nagao–Nielsen complex action -/

/-- **[The real sector of the NN complex action is the Levi-Civita d'Alembert balance].** The complex
Einstein equation `G + iΛ = κ(T + iS)` of the Nagao–Nielsen complex action splits (`κ ≠ 0`) into the
**real** Levi-Civita d'Alembert balance `T + A = 0` (the reversible, geometric gravitational sector) and
the **imaginary** entropic curvature `Λ = κ S` (the dissipative sector). Levi-Civita's gravitational
tensor is the real sector of the complex action's gravity. -/
theorem complexEinstein_real_is_dAlembert (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    T + gravitationalTensor Ric scalarR g κ = 0 ∧ Λ = κ • S := by
  obtain ⟨hR, hI⟩ := (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp h
  exact ⟨dAlembert_balance Ric scalarR g T κ hκ hR, hI⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

end
