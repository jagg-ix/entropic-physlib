/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldFormulaDuality
public import Physlib.QFT.PerturbationTheory.FieldOpFreeAlgebra.SuperCommute

/-!
# The field superoperator: the adjoint (commutator) action on `K^form`

A **superoperator** is a linear map *on* the operator algebra. On the field-formula algebra
`K^form = TensorAlgebra ℂ U` of the Greaves–Thomas framework (`PTSymmetricQFT.FormalFieldTheory`), the
canonical superoperator is the **adjoint action** — the inner derivation

  `ad_X(Y) = [X, Y] = X·Y − Y·X`   (`fieldAdjoint`),

a `ℂ`-linear endomorphism of `K^form`. This is the generator of inner automorphisms and the Heisenberg
time-evolution; on field symbols its realization is the canonical commutation relation, and physlib's
`superCommuteF` is its graded (bose/fermi) analogue on the field-operator algebra.

* **§A — the adjoint superoperator** (`fieldAdjoint`, `fieldAdjoint_apply`, `fieldAdjointBilin`,
  `fieldAdjoint_leibniz`). `ad_X : K^form →ₗ K^form`; the assignment `X ↦ ad_X` is itself linear, a
  *superoperator-valued bilinear map* `fieldAdjointBilin`; and `ad_X` is a **derivation**
  `ad_X(YZ) = ad_X(Y)·Z + Y·ad_X(Z)`.
* **§B — realization intertwines it with the operator commutator** (`realize_fieldAdjoint`,
  `realize_fieldAdjoint_symbol`). `realize(ad_X(Y)) = [realize X, realize Y]`; on field symbols
  `realize(ad_{Φ^λ}(Φ^μ)) = φ^λφ^μ − φ^μφ^λ` — the canonical commutation relation.
* **§C — equivariance under formula automorphisms** (`fieldAdjoint_conj`). `σ ∘ ad_X ∘ σ⁻¹ = ad_{σX}` for
  the dual automorphism `σ = tensorAlgEquiv e` of `PTSymmetricQFT.FieldFormulaDuality` — the superoperator
  transforms covariantly under field-symbol symmetries.
* **§D — the Liouville / Heisenberg generator** (`liouvilleGenerator`, `liouvilleGenerator_apply`,
  `realize_liouvilleGenerator`). `𝓛_H = −i·ad_H`, `𝓛_H(Y) = −i[H, Y]` — the unitary time-evolution
  superoperator; its realization is the Heisenberg generator `−i[realize H, ·]`.
* **§E — link to physlib's graded super-commutator** (`superCommuteF_bosonic_eq_commutator`).
  `superCommuteF X : FieldOpFreeAlgebra →ₗ FieldOpFreeAlgebra` is the *graded* adjoint superoperator
  (with the bose/fermi exchange sign); for the bosonic statistic it is exactly the ordinary commutator
  superoperator `ad`.

## References

* Standard QFT: the adjoint action / Heisenberg generator on the operator algebra.
* Repo dependencies: `PTSymmetricQFT.FormalFieldTheory` (`KForm`); `PTSymmetricQFT.QuantumSymmetry`
  (`quantumRealize`); `PTSymmetricQFT.FieldFormulaDuality` (`tensorAlgEquiv`);
  `QFT.PerturbationTheory.FieldOpFreeAlgebra` (`superCommuteF`, `ofCrAnOpF`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldSuperoperator

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldFormulaDuality
open FieldSpecification FieldSpecification.FieldOpFreeAlgebra FieldStatistic

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-! ## §A — the adjoint (commutator) superoperator on `K^form` -/

/-- **The field superoperator** `ad_X(Y) = [X, Y] = X·Y − Y·X` — the adjoint action, a `ℂ`-linear
endomorphism of `K^form` (`mulLeft X − mulRight X`). -/
noncomputable def fieldAdjoint (X : KForm U) : KForm U →ₗ[ℂ] KForm U :=
  LinearMap.mulLeft ℂ X - LinearMap.mulRight ℂ X

@[simp] theorem fieldAdjoint_apply (X Y : KForm U) : fieldAdjoint X Y = X * Y - Y * X := by
  simp [fieldAdjoint]

/-- **The superoperator-valued bilinear map** `X ↦ ad_X` (linear in `X` too) — the full inner-derivation
structure of `K^form`. -/
noncomputable def fieldAdjointBilin : KForm U →ₗ[ℂ] (KForm U →ₗ[ℂ] KForm U) :=
  LinearMap.mul ℂ (KForm U) - (LinearMap.mul ℂ (KForm U)).flip

@[simp] theorem fieldAdjointBilin_apply (X Y : KForm U) : fieldAdjointBilin X Y = X * Y - Y * X := by
  simp [fieldAdjointBilin]

theorem fieldAdjointBilin_eq (X : KForm U) : fieldAdjointBilin X = fieldAdjoint X := by
  ext Y; rw [fieldAdjointBilin_apply, fieldAdjoint_apply]

/-- **The adjoint superoperator is a derivation** `ad_X(YZ) = ad_X(Y)·Z + Y·ad_X(Z)` — the Leibniz rule of
the inner derivation. -/
theorem fieldAdjoint_leibniz (X Y Z : KForm U) :
    fieldAdjoint X (Y * Z) = fieldAdjoint X Y * Z + Y * fieldAdjoint X Z := by
  simp only [fieldAdjoint_apply]; noncomm_ring

/-! ## §B — the realization intertwines `ad` with the operator commutator -/

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **[Intertwiner] `realize(ad_X(Y)) = [realize X, realize Y]`.** The realization includes the field-formula
superoperator to the commutator of the realized operators. -/
theorem realize_fieldAdjoint (ev : U →ₗ[ℂ] A) (X Y : KForm U) :
    quantumRealize ev (fieldAdjoint X Y)
      = quantumRealize ev X * quantumRealize ev Y - quantumRealize ev Y * quantumRealize ev X := by
  rw [fieldAdjoint_apply, map_sub, map_mul, map_mul]

/-- **[CCR] The adjoint of a field symbol realizes to the canonical commutation relation.**
`realize(ad_{Φ^λ}(Φ^μ)) = φ^λφ^μ − φ^μφ^λ = [φ^λ, φ^μ]`. -/
theorem realize_fieldAdjoint_symbol (ev : U →ₗ[ℂ] A) (s t : U) :
    quantumRealize ev (fieldAdjoint (TensorAlgebra.ι ℂ s) (TensorAlgebra.ι ℂ t))
      = ev s * ev t - ev t * ev s := by
  rw [realize_fieldAdjoint]; simp [quantumRealize]

/-! ## §C — equivariance under formula automorphisms -/

/-- **The adjoint superoperator is equivariant under formula automorphisms** `σ ∘ ad_X ∘ σ⁻¹ = ad_{σX}`
(`σ = tensorAlgEquiv e`) — the field-symbol symmetry conjugates `ad`. -/
theorem fieldAdjoint_conj (e : U ≃ₗ[ℂ] U) (X Y : KForm U) :
    fieldAdjoint (tensorAlgEquiv e X) Y
      = tensorAlgEquiv e (fieldAdjoint X ((tensorAlgEquiv e).symm Y)) := by
  rw [fieldAdjoint_apply, fieldAdjoint_apply, map_sub, map_mul, map_mul, AlgEquiv.apply_symm_apply]

/-! ## §D — the Liouville / Heisenberg generator `𝓛_H = −i·ad_H` -/

/-- **The Liouville / Heisenberg generator** `𝓛_H = −i·ad_H` — the unitary time-evolution superoperator on
`K^form`. -/
noncomputable def liouvilleGenerator (H : KForm U) : KForm U →ₗ[ℂ] KForm U :=
  (-Complex.I) • fieldAdjoint H

theorem liouvilleGenerator_apply (H Y : KForm U) :
    liouvilleGenerator H Y = (-Complex.I) • (H * Y - Y * H) := by
  rw [liouvilleGenerator, LinearMap.smul_apply, fieldAdjoint_apply]

/-- **[Intertwiner] The realization records `𝓛_H` to the Heisenberg generator** `−i[realize H, ·]`. -/
theorem realize_liouvilleGenerator (ev : U →ₗ[ℂ] A) (H Y : KForm U) :
    quantumRealize ev (liouvilleGenerator H Y)
      = (-Complex.I) • (quantumRealize ev H * quantumRealize ev Y
          - quantumRealize ev Y * quantumRealize ev H) := by
  rw [liouvilleGenerator_apply, map_smul, map_sub, map_mul, map_mul]

/-! ## §E — link to physlib's graded super-commutator -/

/-- **[Link] `superCommuteF` is the graded adjoint superoperator; bosonic = the ordinary commutator.**
physlib's `superCommuteF X : FieldOpFreeAlgebra →ₗ FieldOpFreeAlgebra` is the *graded* adjoint
superoperator; for a bosonic field operator (`𝓢 = 1`) it is exactly the commutator superoperator `ad`. -/
theorem superCommuteF_bosonic_eq_commutator {𝓕 : FieldSpecification} (φ φ' : 𝓕.CrAnFieldOp)
    (hφ : (𝓕 |>ₛ φ) = bosonic) :
    superCommuteF (ofCrAnOpF φ) (ofCrAnOpF φ')
      = ofCrAnOpF φ * ofCrAnOpF φ' - ofCrAnOpF φ' * ofCrAnOpF φ := by
  rw [superCommuteF_ofCrAnOpF_ofCrAnOpF, hφ]; simp

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldSuperoperator

end
