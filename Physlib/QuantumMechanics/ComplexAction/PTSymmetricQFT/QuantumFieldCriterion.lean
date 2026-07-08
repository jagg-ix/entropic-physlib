/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldFormulaDuality
public import Physlib.QFT.PerturbationTheory.FieldOpFreeAlgebra.SuperCommute

/-!
# Greaves–Thomas: the classical/quantum criterion for a field theory, and its physlib realization

Answers the question *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674) poses for §3 — *what,
first of all, is a quantum field theory?* — and links it to physlib's field-operator algebra.

In the formal-field-theory framework the answer is sharp and method-neutral: **a field theory is a formal
field theory** — a complex (affine) subspace `D^form ⊆ K^form` of the non-commutative algebra of
differential formulae. It is the *same kind of object* classical or quantum; it is a **quantum** field
theory when its fields are realized in a **non-commutative** operator algebra, i.e. when the canonical
commutation relations do not all vanish.

The classical/quantum distinction is therefore **not** in `K^form` or `D^form` (common to both) but in the
*realization*: a classical field realizes `K^form` into a commutative function algebra (all commutators
collapse), a quantum field into a non-commutative operator algebra (the CCRs survive).

* **§A — the definition** (`FieldTheory`, `Satisfies`, `IsClassicalField`, `IsQuantumField`).
* **§B — the criterion** (`isClassicalField_iff_CCR_zero`, `commutative_isClassicalField`, `DF_mul`): a
  field is classical **iff all canonical commutators vanish** `D_{Φ^λΦ^μ − Φ^μΦ^λ} = 0`.
* **§C — quantum field theories exist** (`witnessEv`, `quantum_field_exists`): a concrete `2×2`-matrix
  realization with `[φ⁰, φ¹] ≠ 0` — the framework is not vacuously classical.
* **§D — method independence** (`satisfies_congr`): the physics depends only on `D^form`.
* **§E — the physlib realization** (`realize_superCommuteF`, `realize_superCommuteF_bosonic`,
  `IsClassicalFieldOp`, `isClassicalFieldOp_iff_superCommuteF_zero`). physlib's field-operator algebra
  `FieldSpecification.FieldOpFreeAlgebra 𝓕 = FreeAlgebra ℂ 𝓕.CrAnFieldOp` **is** a Greaves–Thomas `K^form`
  (a free ℂ-algebra of field formulae); its universal property is the realization (`FreeAlgebra.lift`) and
  its graded CCR is `superCommuteF`. We prove the realization records `superCommuteF` to the (graded)
  operator commutator and that, for the bosonic statistic, the Greaves–Thomas criterion holds verbatim on
  physlib's algebra: a realization is classical iff its super-commutators vanish.

Symmetries of such a theory are the geometric actions of `PTSymmetricQFT.GeometricAction` / the formula
automorphisms of `PTSymmetricQFT.FieldFormulaDuality`; the `CPT`/`PT` theorems
(`PTSymmetricQFT.CPTDiracDynamics`, `PTSymmetricQFT.PTTensorDynamics`) are the total-inversion instances.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2 (the question opening §3).
* Repo dependencies: `PTSymmetricQFT.FormalFieldTheory` (`KForm`); `PTSymmetricQFT.QuantumSymmetry`
  (`quantumRealize`, `quantumDF`, `quantumDF_commutator`); `QFT.PerturbationTheory.FieldOpFreeAlgebra`
  (`ofCrAnOpF`, `universality`, `superCommuteF`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumFieldCriterion

open Matrix
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry

variable {U : Type*} [AddCommGroup U] [Module ℂ U]
variable {A : Type*} [Ring A] [Algebra ℂ A]

/-! ## §A — the definition: a field theory is a formal field theory `D^form` -/

/-- **[Greaves–Thomas] A field theory is a formal field theory** — a complex subspace `D^form ⊆ K^form` of
the differential formulae. (The Lagrangian reading replaces the subspace by the affine `densityClass`; both
are complex affine subspaces.) This single object serves classical *and* quantum theories. -/
structure FieldTheory (U : Type*) [AddCommGroup U] [Module ℂ U] where
  /-- The formal field theory `D^form`. -/
  DForm : Submodule ℂ (KForm U)

/-- **A field satisfies the theory** (Eq. 6): every differential formula of `D^form` vanishes on it,
`D_F = 0` for all `F ∈ D^form`. -/
def Satisfies (ev : U →ₗ[ℂ] A) (𝒯 : FieldTheory U) : Prop :=
  ∀ F ∈ 𝒯.DForm, quantumRealize ev F = 0

/-- **A field is classical** when its field operators commute. -/
def IsClassicalField (ev : U →ₗ[ℂ] A) : Prop := ∀ s t : U, ev s * ev t = ev t * ev s

/-- **A field is quantum** when it is not classical — some canonical commutator is non-zero. -/
def IsQuantumField (ev : U →ₗ[ℂ] A) : Prop := ¬ IsClassicalField ev

/-! ## §B — the criterion: classical ⟺ vanishing canonical commutators -/

/-- **[Greaves–Thomas — the classical/quantum criterion] A field is classical iff all canonical commutators
vanish.** `D_{Φ^λΦ^μ − Φ^μΦ^λ} = 0` for all field symbols ⟺ the field operators commute. The
non-commutativity of `K^form` is detected exactly by a *quantum* field. -/
theorem isClassicalField_iff_CCR_zero (ev : U →ₗ[ℂ] A) :
    IsClassicalField ev ↔ ∀ s t : U,
      quantumDF ev (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t
        - TensorAlgebra.ι ℂ t * TensorAlgebra.ι ℂ s) = 0 := by
  constructor
  · intro h s t; rw [quantumDF_commutator, h, sub_self]
  · intro h s t; have hst := h s t; rw [quantumDF_commutator, sub_eq_zero] at hst; exact hst

/-- **The classical field theories** are the commutative realizations: a field valued in a commutative
algebra is automatically classical. -/
theorem commutative_isClassicalField {Acomm : Type*} [CommRing Acomm] [Algebra ℂ Acomm]
    (ev : U →ₗ[ℂ] Acomm) : IsClassicalField ev := fun s t => mul_comm _ _

/-- **`D_F` is an algebra hom** — the differential operator is a well-defined polynomial in the field
operators (`D_{FG} = D_F D_G`), classical or quantum. -/
theorem DF_mul (ev : U →ₗ[ℂ] A) (F G : KForm U) :
    quantumDF ev (F * G) = quantumDF ev F * quantumDF ev G := by
  simp [quantumDF, quantumRealize]

/-! ## §C — quantum field theories exist (the framework is not vacuously classical) -/

/-- A concrete non-commutative realization: the field symbols `ℂ²` map to the `2×2` matrix operators
`φ⁰ = E₀₁`, `φ¹ = E₁₀`, which do **not** commute (`E₀₁E₁₀ = E₀₀ ≠ E₁₁ = E₁₀E₀₁`). -/
noncomputable def witnessEv : (Fin 2 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (LinearMap.proj 0).smulRight (!![0, 1; 0, 0]) + (LinearMap.proj 1).smulRight (!![0, 0; 1, 0])

/-- **[Greaves–Thomas] A genuinely quantum field theory exists.** The matrix realization `witnessEv` has a
non-zero canonical commutator, so it is a *quantum* field — the non-commutativity of `K^form` is genuinely
realizable, not a vacuous formal artifact. -/
theorem quantum_field_exists :
    ∃ ev : (Fin 2 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ, IsQuantumField ev := by
  refine ⟨witnessEv, fun hcl => ?_⟩
  have h0 : witnessEv (Pi.single 0 1) = !![0, 1; 0, 0] := by
    simp [witnessEv, LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne]
  have h1 : witnessEv (Pi.single 1 1) = !![0, 0; 1, 0] := by
    simp [witnessEv, LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne]
  have hcomm := hcl (Pi.single 0 1) (Pi.single 1 1)
  rw [h0, h1] at hcomm
  have := congrFun (congrFun hcomm 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

/-! ## §D — method independence -/

/-- **[Greaves–Thomas] The physics depends only on `D^form`.** Two field theories with the same formal field
theory have the same fields — independently of how `D^form` was presented (canonical, path-integral,
Lagrangian). -/
theorem satisfies_congr (ev : U →ₗ[ℂ] A) {𝒯 𝒯' : FieldTheory U} (h : 𝒯.DForm = 𝒯'.DForm) :
    Satisfies ev 𝒯 ↔ Satisfies ev 𝒯' := by
  simp only [Satisfies, h]

/-! ## §E — the physlib realization: `FieldSpecification.FieldOpFreeAlgebra` is a `K^form` -/

open FieldSpecification FieldSpecification.FieldOpFreeAlgebra FieldStatistic

/-- **[Link] The realization includes the physlib super-commutator to the operator super-commutator.**
physlib's `FieldOpFreeAlgebra 𝓕 = FreeAlgebra ℂ 𝓕.CrAnFieldOp` is a Greaves–Thomas `K^form`; its
realization (universal property, `FreeAlgebra.lift`) sends the graded CCR `superCommuteF` to the graded
commutator `f φ · f φ' − 𝓢(φ,φ') · f φ' · f φ` of the realized field operators. -/
theorem realize_superCommuteF {𝓕 : FieldSpecification} {B : Type} [Ring B] [Algebra ℂ B]
    (f : 𝓕.CrAnFieldOp → B) (φ φ' : 𝓕.CrAnFieldOp) :
    (FreeAlgebra.lift ℂ f) (superCommuteF (ofCrAnOpF φ) (ofCrAnOpF φ'))
      = f φ * f φ' - (exchangeSign (𝓕 |>ₛ φ) (𝓕 |>ₛ φ')) • (f φ' * f φ) := by
  rw [superCommuteF_ofCrAnOpF_ofCrAnOpF]
  simp only [ofCrAnOpF, map_sub, map_mul, map_smul, FreeAlgebra.lift_ι_apply, smul_mul_assoc]

/-- For a **bosonic** field operator the super-commutator is the ordinary commutator (`𝓢 = 1`). -/
theorem realize_superCommuteF_bosonic {𝓕 : FieldSpecification} {B : Type} [Ring B] [Algebra ℂ B]
    (f : 𝓕.CrAnFieldOp → B) (φ φ' : 𝓕.CrAnFieldOp) (hφ : (𝓕 |>ₛ φ) = bosonic) :
    (FreeAlgebra.lift ℂ f) (superCommuteF (ofCrAnOpF φ) (ofCrAnOpF φ'))
      = f φ * f φ' - f φ' * f φ := by
  rw [realize_superCommuteF, hφ]; simp

/-- **A physlib field-operator realization is classical** when its operators commute (the Greaves–Thomas
`IsClassicalField` on `FieldOpFreeAlgebra`). -/
def IsClassicalFieldOp {𝓕 : FieldSpecification} {B : Type} [Ring B] [Algebra ℂ B]
    (f : 𝓕.CrAnFieldOp → B) : Prop := ∀ φ φ', f φ * f φ' = f φ' * f φ

/-- **[Greaves–Thomas criterion on physlib's algebra] A bosonic realization is classical iff its
super-commutators vanish.** The Greaves–Thomas classical/quantum criterion holds verbatim on physlib's
field-operator algebra: with all statistics bosonic, `f` is classical iff every realized `superCommuteF`
vanishes — the canonical commutation relations are exactly what makes the field quantum. -/
theorem isClassicalFieldOp_iff_superCommuteF_zero {𝓕 : FieldSpecification} {B : Type} [Ring B]
    [Algebra ℂ B] (f : 𝓕.CrAnFieldOp → B) (hbose : ∀ φ : 𝓕.CrAnFieldOp, (𝓕 |>ₛ φ) = bosonic) :
    IsClassicalFieldOp f ↔
      ∀ φ φ', (FreeAlgebra.lift ℂ f) (superCommuteF (ofCrAnOpF φ) (ofCrAnOpF φ')) = 0 := by
  constructor
  · intro h φ φ'; rw [realize_superCommuteF_bosonic f φ φ' (hbose φ), h, sub_self]
  · intro h φ φ'
    have hz := h φ φ'
    rw [realize_superCommuteF_bosonic f φ φ' (hbose φ), sub_eq_zero] at hz
    exact hz

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumFieldCriterion

end
