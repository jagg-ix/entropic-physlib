/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.SpinDensityFunctionalOperators
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Cartan decompositions of the double covers `SU(2)` and `SU(1,1)`

Formalizes the exact matrix core of §§2–3 of Varlamov, *Towards the Quantum Electrodynamics
on the Poincaré Group* (arXiv:hep-th/0403070): the Euler parametrizations and Cartan `KAK`
decompositions of the two double covers underlying the paper's harmonic analysis — the
compact `SU(2)` (covering `SO(3)`, Eqs. (1)–(3)) and the noncompact `SU(1,1)` (covering the
2+1 Lorentz group, Eqs. (19)–(20)) — and their tangent Lie algebras, *derived from the
repository's existing Pauli-matrix lemmas* rather than recomputed:

* **§A `SU(2)`**: `su2_cartan_kak` — the Euler matrix factorizes as
  `diag(e^{iφ/2}, e^{−iφ/2}) · rot(θ) · diag(e^{iψ/2}, e^{−iψ/2})` (Eq. (3));
  `su2Euler_det` and `su2Euler_unitary` — determinant one and unitarity, the latter by pure
  factor algebra through the `KAK` form (each factor is unitary);
* **§B `su(2)`**: the tangent matrices `A₁ = (i/2)σ_x`, `A₂ = −(i/2)σ_y`, `A₃ = (i/2)σ_z`
  satisfy the *cyclic* relations `[A₁,A₂] = A₃`, `[A₂,A₃] = A₁`, `[A₃,A₁] = A₂`
  (`su2_tangent_cyclic`), built on `SpinDensityFunctionalOperators.pauliX_mul_pauliY` and
  two new product lemmas in the same style;
* **§C `SU(1,1)`**: `su11_cartan_kak` — the same torus factors with the middle rotation
  replaced by a `cosh/sinh` boost (Eq. (20), `cos ↦ cosh`); `su11Euler_det` and
  `su11Euler_pseudoUnitary` — `gᴴ σ_z g = σ_z`, pseudo-unitarity with respect to the
  `(1,−1)` metric, which *is* the repository's `pauliZ`; and the tangent matrices
  `B₁ = (1/2)σ_x`, `B₂ = −(1/2)σ_y`, `B₃ = (i/2)σ_z` with the **sign-flipped** relations
  `[B₁,B₂] = −B₃`, `[B₂,B₃] = B₁`, `[B₃,B₁] = B₂` (`su11_sign_flip`) — the single sign
  that separates the compact and noncompact real forms; the Cartan direction `A₃ = B₃` is
  shared, the flip lives in the (rotation ↦ boost) plane.

**Honest layering.**  Exact `2×2` matrix and elementary-function algebra.  The paper's
harmonic-analysis superstructure — matrix elements `t^l_{mn}` as hypergeometric functions,
the Laplace–Beltrami eigenvalue `−l(l+1)`, Peter–Weyl orthogonality (Eq. (17)), the
homogeneous space `M = T₄ × ℂS²`, and the Dirac/Maxwell boundary-value problems — is the
analytic layer, cited not re-proven.  Related repository carriers: the *same* `su(1,1)`
algebra in the Bargmann–Fock polynomial representation
(`OperatorAlgebra.BargmannFockCCR`, `eulerOp`/`singletAnn`), the `SL(2,ℂ) ≃ SU(2)⊗SU(2)`
spinor labels this paper's matrix elements represent
(`Particles.SpinorStructureInternalSymmetries`), and the `so(4,2)`/Yao basis consumed by the
periodic-table tower (`PeriodicTableMadelungSpinTower`).

## References

* V. V. Varlamov, *Towards the Quantum Electrodynamics on the Poincaré Group*,
  arXiv:hep-th/0403070.
* Carrier reuse: `QuantumMechanics.SpinDensityFunctionalOperators` (Pauli matrices and
  products).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators
open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CartanDecompositionDoubleCovers

/-! ## §A — the `SU(2)` Euler parametrization and its Cartan decomposition -/

/-- The maximal-torus factor `diag(e^{iφ/2}, e^{−iφ/2})` — the `K` of both `KAK`
decompositions. -/
noncomputable def torusFactor (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * (φ / 2 : ℝ)), 0;
     0, Complex.exp (-(Complex.I * (φ / 2 : ℝ)))]

/-- The middle `SU(2)` rotation `[[cos θ/2, i sin θ/2], [i sin θ/2, cos θ/2]]` — the compact
`A` of Eq. (3). -/
noncomputable def middleRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), Complex.I * (Real.sin (θ / 2) : ℝ);
     Complex.I * (Real.sin (θ / 2) : ℝ), (Real.cos (θ / 2) : ℂ)]

/-- **The `SU(2)` Euler matrix** (Eq. (2)). -/
noncomputable def su2Euler (φ θ ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ) * Complex.exp (Complex.I * ((φ + ψ) / 2 : ℝ)),
     Complex.I * (Real.sin (θ / 2) : ℝ) * Complex.exp (Complex.I * ((φ - ψ) / 2 : ℝ));
     Complex.I * (Real.sin (θ / 2) : ℝ) * Complex.exp (Complex.I * ((ψ - φ) / 2 : ℝ)),
     (Real.cos (θ / 2) : ℂ) * Complex.exp (-(Complex.I * ((φ + ψ) / 2 : ℝ)))]

/-- **The Cartan `KAK` decomposition of `SU(2)`** (Eq. (3)): the Euler matrix is torus ×
rotation × torus. -/
theorem su2_cartan_kak (φ θ ψ : ℝ) :
    torusFactor φ * middleRotation θ * torusFactor ψ = su2Euler φ θ ψ := by
  unfold torusFactor middleRotation su2Euler
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
      rw [Complex.exp_add]
      ring

/-- The torus factor is unitary. -/
theorem torusFactor_unitary (φ : ℝ) :
    (torusFactor φ)ᴴ * torusFactor φ = 1 := by
  unfold torusFactor
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        ← Complex.exp_conj, map_mul, map_ofNat, map_div₀,
        Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add,
        neg_add_cancel, Complex.exp_zero]

/-- The middle rotation is unitary: `cos² + sin² = 1`. -/
theorem middleRotation_unitary (θ : ℝ) :
    (middleRotation θ)ᴴ * middleRotation θ = 1 := by
  unfold middleRotation
  have hz := Complex.sin_sq_add_cos_sq ((θ : ℂ) / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.ofReal_cos, Complex.ofReal_sin,
        ← Complex.cos_conj, ← Complex.sin_conj, map_div₀, map_ofNat,
        Complex.conj_ofReal, Complex.conj_I]
      first
        | ring1
        | linear_combination hz - (Complex.sin ((θ : ℂ) / 2)) ^ 2 * Complex.I_sq

/-- **The Euler matrix is unitary** — by pure factor algebra through the `KAK` form. -/
theorem su2Euler_unitary (φ θ ψ : ℝ) :
    (su2Euler φ θ ψ)ᴴ * su2Euler φ θ ψ = 1 := by
  rw [← su2_cartan_kak]
  calc (torusFactor φ * middleRotation θ * torusFactor ψ)ᴴ
        * (torusFactor φ * middleRotation θ * torusFactor ψ)
      = (torusFactor ψ)ᴴ * ((middleRotation θ)ᴴ
          * (((torusFactor φ)ᴴ * torusFactor φ) * middleRotation θ) * torusFactor ψ) := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
    _ = 1 := by
        rw [torusFactor_unitary, Matrix.one_mul, middleRotation_unitary, Matrix.one_mul,
          torusFactor_unitary]

/-- **Determinant one** — the Euler phases cancel pairwise and `cos² + sin² = 1` closes:
together with `su2Euler_unitary`, membership in `SU(2)` rather than merely `U(2)`. -/
theorem su2Euler_det (φ θ ψ : ℝ) : (su2Euler φ θ ψ).det = 1 := by
  unfold su2Euler
  rw [Matrix.det_fin_two_of]
  have h1 : Complex.exp (Complex.I * ((φ + ψ) / 2 : ℝ)) *
      Complex.exp (-(Complex.I * ((φ + ψ) / 2 : ℝ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : Complex.exp (Complex.I * ((φ - ψ) / 2 : ℝ)) *
      Complex.exp (Complex.I * ((ψ - φ) / 2 : ℝ)) = 1 := by
    rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add,
      show (φ - ψ) / 2 + (ψ - φ) / 2 = 0 by ring]
    simp
  have hz : ((Real.sin (θ / 2) : ℂ)) ^ 2 + ((Real.cos (θ / 2) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (θ / 2)
  linear_combination ((Real.cos (θ / 2) : ℂ)) ^ 2 * h1
    - Complex.I ^ 2 * ((Real.sin (θ / 2) : ℂ)) ^ 2 * h2
    + hz - ((Real.sin (θ / 2) : ℂ)) ^ 2 * Complex.I_sq

/-! ## §B — the `su(2)` tangent algebra from the Pauli carriers -/

/-- The missing Pauli products, in the style of
`SpinDensityFunctionalOperators.pauliX_mul_pauliY`. -/
lemma pauliY_mul_pauliZ : pauliY * pauliZ = Complex.I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliZ_mul_pauliY : pauliZ * pauliY = -Complex.I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliZ_mul_pauliX : pauliZ * pauliX = Complex.I • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliX_mul_pauliZ : pauliX * pauliZ = -Complex.I • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `A₁ = (i/2)σ_x` — the tangent matrix of the first `SU(2)` one-parameter subgroup. -/
noncomputable def su2TangentA1 : Matrix (Fin 2) (Fin 2) ℂ := (Complex.I / 2) • pauliX
/-- `A₂ = −(i/2)σ_y = (1/2)[[0,−1],[1,0]]`. -/
noncomputable def su2TangentA2 : Matrix (Fin 2) (Fin 2) ℂ := (-(Complex.I) / 2) • pauliY
/-- `A₃ = (i/2)σ_z` — the Cartan direction, shared with `su(1,1)` below. -/
noncomputable def su2TangentA3 : Matrix (Fin 2) (Fin 2) ℂ := (Complex.I / 2) • pauliZ

/-- **The cyclic `su(2)` relations** `[A₁,A₂] = A₃`, `[A₂,A₃] = A₁`, `[A₃,A₁] = A₂` — the
compact real form, derived from the Pauli product lemmas. -/
theorem su2_tangent_cyclic :
    (su2TangentA1 * su2TangentA2 - su2TangentA2 * su2TangentA1 = su2TangentA3) ∧
    (su2TangentA2 * su2TangentA3 - su2TangentA3 * su2TangentA2 = su2TangentA1) ∧
    (su2TangentA3 * su2TangentA1 - su2TangentA1 * su2TangentA3 = su2TangentA2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · unfold su2TangentA1 su2TangentA2 su2TangentA3
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
        pauliX_mul_pauliY, pauliY_mul_pauliX, pauliY_mul_pauliZ, pauliZ_mul_pauliY,
        pauliZ_mul_pauliX, pauliX_mul_pauliZ, smul_smul]
      match_scalars
      first
        | ring1
        | linear_combination (Complex.I / 2) * Complex.I_sq
        | linear_combination (-(Complex.I) / 2) * Complex.I_sq

/-! ## §C — the noncompact double cover `SU(1,1)` -/

/-- The middle `SU(1,1)` boost `[[cosh τ/2, sinh τ/2], [sinh τ/2, cosh τ/2]]` — the
noncompact `A` of Eq. (20): the rotation with `cos ↦ cosh`, `i sin ↦ sinh`. -/
noncomputable def middleBoost (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cosh (τ / 2) : ℂ), (Real.sinh (τ / 2) : ℂ);
     (Real.sinh (τ / 2) : ℂ), (Real.cosh (τ / 2) : ℂ)]

/-- **The `SU(1,1)` Euler matrix** (Eq. (19) in Euler form). -/
noncomputable def su11Euler (φ τ ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cosh (τ / 2) : ℂ) * Complex.exp (Complex.I * ((φ + ψ) / 2 : ℝ)),
     (Real.sinh (τ / 2) : ℂ) * Complex.exp (Complex.I * ((φ - ψ) / 2 : ℝ));
     (Real.sinh (τ / 2) : ℂ) * Complex.exp (Complex.I * ((ψ - φ) / 2 : ℝ)),
     (Real.cosh (τ / 2) : ℂ) * Complex.exp (-(Complex.I * ((φ + ψ) / 2 : ℝ)))]

/-- **The Cartan `KAK` decomposition of `SU(1,1)`** (Eq. (20)): the same torus factors, the
compact rotation replaced by the boost. -/
theorem su11_cartan_kak (φ τ ψ : ℝ) :
    torusFactor φ * middleBoost τ * torusFactor ψ = su11Euler φ τ ψ := by
  unfold torusFactor middleBoost su11Euler
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
      rw [Complex.exp_add]
      ring

/-- The boost preserves the `(1,−1)` metric — which *is* `pauliZ`:
`Bᴴ σ_z B = σ_z`, by `cosh² − sinh² = 1`. -/
theorem middleBoost_pseudoUnitary (τ : ℝ) :
    (middleBoost τ)ᴴ * pauliZ * middleBoost τ = pauliZ := by
  unfold middleBoost
  have hz := Complex.cosh_sq_sub_sinh_sq ((τ : ℂ) / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.ofReal_cosh, Complex.ofReal_sinh, ← Complex.cosh_conj,
        ← Complex.sinh_conj, map_div₀, map_ofNat, Complex.conj_ofReal]
      first
        | ring1
        | linear_combination hz
        | linear_combination -hz

/-- The torus factor also preserves the metric (both are diagonal). -/
theorem torusFactor_pseudoUnitary (φ : ℝ) :
    (torusFactor φ)ᴴ * pauliZ * torusFactor φ = pauliZ := by
  unfold torusFactor
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        ← Complex.exp_conj, map_mul, map_ofNat, map_div₀, Complex.conj_I,
        Complex.conj_ofReal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- **`SU(1,1)` pseudo-unitarity** `gᴴ σ_z g = σ_z` — by factor algebra through the `KAK`
form: each factor preserves the `(1,−1)` metric carried by the repository's `pauliZ`. -/
theorem su11Euler_pseudoUnitary (φ τ ψ : ℝ) :
    (su11Euler φ τ ψ)ᴴ * pauliZ * su11Euler φ τ ψ = pauliZ := by
  rw [← su11_cartan_kak]
  calc (torusFactor φ * middleBoost τ * torusFactor ψ)ᴴ * pauliZ
        * (torusFactor φ * middleBoost τ * torusFactor ψ)
      = (torusFactor ψ)ᴴ * ((middleBoost τ)ᴴ
          * ((torusFactor φ)ᴴ * pauliZ * torusFactor φ) * middleBoost τ)
          * torusFactor ψ := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
    _ = pauliZ := by
        rw [torusFactor_pseudoUnitary, middleBoost_pseudoUnitary,
          torusFactor_pseudoUnitary]

/-- **Determinant one** — the phases cancel and `cosh² − sinh² = 1` closes: together with
`su11Euler_pseudoUnitary`, membership in `SU(1,1)` rather than merely `U(1,1)`. -/
theorem su11Euler_det (φ τ ψ : ℝ) : (su11Euler φ τ ψ).det = 1 := by
  unfold su11Euler
  rw [Matrix.det_fin_two_of]
  have h1 : Complex.exp (Complex.I * ((φ + ψ) / 2 : ℝ)) *
      Complex.exp (-(Complex.I * ((φ + ψ) / 2 : ℝ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : Complex.exp (Complex.I * ((φ - ψ) / 2 : ℝ)) *
      Complex.exp (Complex.I * ((ψ - φ) / 2 : ℝ)) = 1 := by
    rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add,
      show (φ - ψ) / 2 + (ψ - φ) / 2 = 0 by ring]
    simp
  have hz : ((Real.cosh (τ / 2) : ℂ)) ^ 2 - ((Real.sinh (τ / 2) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq (τ / 2)
  linear_combination ((Real.cosh (τ / 2) : ℂ)) ^ 2 * h1
    - ((Real.sinh (τ / 2) : ℂ)) ^ 2 * h2 + hz

/-- `B₁ = (1/2)σ_x` — real, unlike its compact partner `A₁ = (i/2)σ_x`. -/
noncomputable def su11TangentB1 : Matrix (Fin 2) (Fin 2) ℂ := ((1 : ℂ) / 2) • pauliX
/-- `B₂ = −(1/2)σ_y = (i/2)[[0,1],[−1,0]]`. -/
noncomputable def su11TangentB2 : Matrix (Fin 2) (Fin 2) ℂ := (-(1 : ℂ) / 2) • pauliY
/-- `B₃ = (i/2)σ_z = A₃` — the shared compact Cartan direction. -/
noncomputable def su11TangentB3 : Matrix (Fin 2) (Fin 2) ℂ := (Complex.I / 2) • pauliZ

/-- **The `su(1,1)` sign flip** `[B₁,B₂] = −B₃`, `[B₂,B₃] = B₁`, `[B₃,B₁] = B₂` — the
noncompact real form differs from `su2_tangent_cyclic` by exactly one sign, in the plane
where the rotation became a boost; the Cartan direction `B₃ = A₃` is untouched. -/
theorem su11_sign_flip :
    (su11TangentB1 * su11TangentB2 - su11TangentB2 * su11TangentB1 = -su11TangentB3) ∧
    (su11TangentB2 * su11TangentB3 - su11TangentB3 * su11TangentB2 = su11TangentB1) ∧
    (su11TangentB3 * su11TangentB1 - su11TangentB1 * su11TangentB3 = su11TangentB2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · unfold su11TangentB1 su11TangentB2 su11TangentB3
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
        pauliX_mul_pauliY, pauliY_mul_pauliX, pauliY_mul_pauliZ, pauliZ_mul_pauliY,
        pauliZ_mul_pauliX, pauliX_mul_pauliZ, smul_smul]
      match_scalars
      first
        | ring1
        | linear_combination (Complex.I / 2) * Complex.I_sq
        | linear_combination (-(Complex.I) / 2) * Complex.I_sq
        | linear_combination -Complex.I_sq
        | linear_combination Complex.I_sq
        | linear_combination (1/2 : ℂ) * Complex.I_sq
        | linear_combination (-(1/2) : ℂ) * Complex.I_sq

end Physlib.QuantumMechanics.ComplexAction.CartanDecompositionDoubleCovers

end
