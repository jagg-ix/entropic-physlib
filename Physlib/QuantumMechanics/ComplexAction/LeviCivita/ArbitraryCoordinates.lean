/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

/-!
# Reference to arbitrary co-ordinates: general covariance of the Levi-Civita d'Alembert balance

Formalizes Levi-Civita's **"reference to arbitrary co-ordinates"** (arXiv:physics/9906004): the
field-equation formalism (`LeviCivita.GravitationalTensor`, `ComplexEinstein.FieldEquations`) is
**generally covariant**. A rank-2 covariant tensor `M_ik` transforms under a coordinate change with
Jacobian `J` by the **congruence**

  `M'_ik = Jᵀ M J`   (`coordCongruence`),

the covariant transformation of `(0,2)`-tensors. This transformation is **linear** (`coordCongruence_add`,
`coordCongruence_smul`, `coordCongruence_zero`) and **symmetry-preserving** (`coordCongruence_transpose`,
`coordCongruence_isSymm`), so every tensor identity of the theory holds in arbitrary co-ordinates:

* the **metric is the arbitrary-coordinate transform of the flat metric** — Lusanna's tetrad metric
  `g = EᵀηE` is exactly the congruence of the Minkowski metric `η` by the cotetrad `E`
  (`tetradMetric_eq_coordCongruence`), and is symmetric in any frame
  (`tetradMetric_coordCongruence_symm`); the cotetrad `E` plays the role of the coordinate Jacobian taking
  the local Minkowski frame to the arbitrary one;
* the **Levi-Civita d'Alembert balance is covariant** — `T + A = 0` in one frame gives
  `JᵀTJ + JᵀAJ = 0` in any other (`dAlembert_balance_covariant`,
  `leviCivita_balance_arbitraryCoords`): the matter and gravitational tensors cancel in every coordinate
  system;
* the **complex Einstein field equation is covariant in both sectors** — `G = κT` and `Λ = κS` transform to
  `JᵀGJ = κ JᵀTJ` and `JᵀΛJ = κ JᵀSJ` (`complexEinsteinFieldEquation_covariant`): the real (matter) and
  imaginary (entropic) sectors of the Nagao–Nielsen complex action are both generally covariant.

So Levi-Civita's gravitational tensor and the complex-action Einstein equations are not tied to a special
coordinate system: written through the congruence `JᵀMJ`, the d'Alembert balance and both sectors of the
field equation hold in arbitrary co-ordinates — the metric itself being the arbitrary-coordinate transform
of the flat Minkowski metric.

* **§A — the covariant transformation of a `(0,2)`-tensor** (`coordCongruence`, `coordCongruence_add`,
  `coordCongruence_smul`, `coordCongruence_zero`, `coordCongruence_transpose`, `coordCongruence_isSymm`).
* **§B — the metric as the arbitrary-coordinate transform of the flat metric**
  (`tetradMetric_eq_coordCongruence`, `tetradMetric_coordCongruence_symm`).
* **§C — covariance of the d'Alembert balance and the field equation** (`dAlembert_balance_covariant`,
  `leviCivita_balance_arbitraryCoords`, `complexEinsteinFieldEquation_covariant`).
* **§D — the assembly** (`leviCivita_arbitraryCoordinates`).

## References

* T. Levi-Civita (arXiv:physics/9906004), the reference of the gravitational tensor to arbitrary
  co-ordinates (general covariance). structures: `LeviCivita.GravitationalTensor` (`gravitationalTensor`,
  `dAlembert_balance`), `ComplexEinstein.FieldEquations` (`complexEinsteinFieldEquation`,
  `complexEinsteinFieldEquation_iff`), `CanonicalTetradGravity.TetradADMGravity` (`tetradMetric`, `minkowskiMatrix`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Matrix

variable {ι : Type*} [Fintype ι]

/-! ## §A — the covariant transformation of a `(0,2)`-tensor `M ↦ JᵀMJ` -/

section Generic

variable {R : Type*} [CommRing R]

/-- **The covariant transformation of a `(0,2)`-tensor under a coordinate change** `M'_ik = Jᵀ M J` —
the congruence of the rank-2 covariant tensor `M` by the coordinate Jacobian `J`. This is how every
tensor of the theory is referred to arbitrary co-ordinates (Levi-Civita, physics/9906004). -/
def coordCongruence (J M : Matrix ι ι R) : Matrix ι ι R := Jᵀ * M * J

/-- **[The coordinate transformation is additive] `Jᵀ(M+N)J = JᵀMJ + JᵀNJ`.** -/
theorem coordCongruence_add (J M N : Matrix ι ι R) :
    coordCongruence J (M + N) = coordCongruence J M + coordCongruence J N := by
  simp only [coordCongruence, mul_add, add_mul]

/-- **[The coordinate transformation commutes with scalars] `Jᵀ(c•M)J = c•(JᵀMJ)`.** -/
theorem coordCongruence_smul (c : R) (J M : Matrix ι ι R) :
    coordCongruence J (c • M) = c • coordCongruence J M := by
  rw [coordCongruence, coordCongruence, Matrix.mul_smul, Matrix.smul_mul]

/-- **[The coordinate transformation fixes the zero tensor] `Jᵀ0J = 0`.** -/
theorem coordCongruence_zero (J : Matrix ι ι R) : coordCongruence J 0 = 0 := by
  simp only [coordCongruence, Matrix.mul_zero, Matrix.zero_mul]

/-- **[The coordinate transformation commutes with transpose] `(JᵀMJ)ᵀ = JᵀMᵀJ`.** A covariant tensor
transforms as a tensor in arbitrary co-ordinates. -/
theorem coordCongruence_transpose (J M : Matrix ι ι R) :
    (coordCongruence J M)ᵀ = coordCongruence J Mᵀ := by
  simp only [coordCongruence, transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- **[The coordinate transformation preserves symmetry] `M symmetric ⟹ JᵀMJ symmetric`.** A symmetric
tensor (a metric, a stress tensor) stays symmetric in every coordinate system. -/
theorem coordCongruence_isSymm (J M : Matrix ι ι R) (hM : Mᵀ = M) :
    (coordCongruence J M)ᵀ = coordCongruence J M := by
  rw [coordCongruence_transpose, hM]

end Generic

/-! ## §B — the metric as the arbitrary-coordinate transform of the flat metric -/

/-- **[The tetrad metric is the congruence of the flat metric] `g = EᵀηE = coordCongruence E η`.** Lusanna's
tetrad metric `g = EᵀηE` (`CanonicalTetradGravity.TetradADMGravity.tetradMetric`) is exactly the reference of the flat
Minkowski metric `η` to arbitrary co-ordinates by the cotetrad `E`: the cotetrad is the coordinate Jacobian
taking the local Minkowski frame to the arbitrary frame. -/
theorem tetradMetric_eq_coordCongruence {d : ℕ}
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    tetradMetric E = coordCongruence E minkowskiMatrix := rfl

/-- **[The metric is symmetric in arbitrary co-ordinates] `gᵀ = g`.** The flat metric is symmetric, so its
arbitrary-coordinate transform — the curved metric `g = EᵀηE` — is symmetric in every frame. -/
theorem tetradMetric_coordCongruence_symm {d : ℕ}
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    (coordCongruence E minkowskiMatrix)ᵀ = coordCongruence E minkowskiMatrix :=
  coordCongruence_isSymm E minkowskiMatrix minkowskiMatrix.eq_transpose

/-! ## §C — covariance of the d'Alembert balance and the field equation -/

/-- **[The d'Alembert balance is covariant] `T + A = 0 ⟹ JᵀTJ + JᵀAJ = 0`.** If the matter and
gravitational tensors cancel in one frame, they cancel in every coordinate system — the balance is a
generally-covariant tensor identity. -/
theorem dAlembert_balance_covariant (J T A : Matrix ι ι ℝ) (h : T + A = 0) :
    coordCongruence J T + coordCongruence J A = 0 := by
  rw [← coordCongruence_add, h, coordCongruence_zero]

/-- **[Levi-Civita's balance in arbitrary co-ordinates].** On a solution of the Einstein field equation,
the Levi-Civita d'Alembert balance `T + A = 0` holds referred to any coordinate system:
`JᵀTJ + Jᵀ A J = 0`. -/
theorem leviCivita_balance_arbitraryCoords (J Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g T : Matrix ι ι ℝ) (κ : ℝ) (hκ : κ ≠ 0) (h : einsteinFieldEquation Ric scalarR g T κ) :
    coordCongruence J T + coordCongruence J (gravitationalTensor Ric scalarR g κ) = 0 :=
  dAlembert_balance_covariant J T (gravitationalTensor Ric scalarR g κ)
    (dAlembert_balance Ric scalarR g T κ hκ h)

/-- **[The complex Einstein field equation is covariant in both sectors].** Referring the complex Einstein
equation `G + iΛ = κ(T + iS)` to arbitrary co-ordinates, the real (matter) sector `G = κT` and the
imaginary (entropic) sector `Λ = κS` each transform covariantly: `JᵀGJ = κ JᵀTJ` and `JᵀΛJ = κ JᵀSJ`. Both
sectors of the Nagao–Nielsen complex action are generally covariant. -/
theorem complexEinsteinFieldEquation_covariant (J Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix ι ι ℝ) (κ : ℝ)
    (h : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    coordCongruence J (einsteinTensor Ric scalarR g) = κ • coordCongruence J T
      ∧ coordCongruence J Λ = κ • coordCongruence J S := by
  obtain ⟨hG, hΛ⟩ := (complexEinsteinFieldEquation_iff (einsteinTensor Ric scalarR g) Λ T S κ).mp h
  exact ⟨by rw [hG, coordCongruence_smul], by rw [hΛ, coordCongruence_smul]⟩

/-! ## §D — the assembly -/

/-- **[Levi-Civita's field equations referred to arbitrary co-ordinates].** For a coordinate Jacobian `J`,
a cotetrad `E`, and a solution of the complex Einstein equation `𝒢 = κ(T + iS)` (`κ ≠ 0`):

* the metric is the arbitrary-coordinate transform of the flat metric, `g = EᵀηE = coordCongruence E η`;
* the Levi-Civita d'Alembert balance is covariant, `JᵀTJ + Jᵀ A J = 0`;
* the complex Einstein field equation is covariant in both sectors, `JᵀGJ = κ JᵀTJ` (matter) and
  `JᵀΛJ = κ JᵀSJ` (entropic).

Levi-Civita's gravitational tensor and the Nagao–Nielsen complex-action Einstein equations are generally
covariant — written through the congruence `JᵀMJ`, every tensor identity holds in arbitrary co-ordinates,
the metric itself being the arbitrary-coordinate transform of the flat Minkowski metric. -/
theorem leviCivita_arbitraryCoordinates {d : ℕ}
    (J E Ric : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (scalarR : ℝ)
    (g Λ T S : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (h : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    tetradMetric E = coordCongruence E minkowskiMatrix
      ∧ coordCongruence J T + coordCongruence J (gravitationalTensor Ric scalarR g κ) = 0
      ∧ coordCongruence J (einsteinTensor Ric scalarR g) = κ • coordCongruence J T
      ∧ coordCongruence J Λ = κ • coordCongruence J S := by
  obtain ⟨hReal, _⟩ := (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp h
  refine ⟨tetradMetric_eq_coordCongruence E,
    leviCivita_balance_arbitraryCoords J Ric scalarR g T κ hκ hReal, ?_, ?_⟩
  · exact (complexEinsteinFieldEquation_covariant J Ric scalarR g Λ T S κ h).1
  · exact (complexEinsteinFieldEquation_covariant J Ric scalarR g Λ T S κ h).2

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates

end
