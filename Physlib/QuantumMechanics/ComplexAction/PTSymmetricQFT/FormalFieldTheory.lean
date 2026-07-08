/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics

/-!
# Greaves–Thomas §2.2: Formal field theories

Formalizes §2.2 of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674): the shift from
differential *operators* to the *formulae* that define them. This abstraction puts classical and quantum
field theories on the same footing, and is the framework in which the paper states symmetries (and the
`CPT`/`PT` theorems of the companion files).

The construction:

* **Field symbols.** A field symbol `Φ^λ_{ξ₁⋯ξₙ}` is the element `λ ⊗ (ξ₁⋯ξₙ)` of the complex vector space
  `W ⊗_ℝ TM`, where `W = Hom(V, ℂ)` are the field-value covectors and `TM = TensorAlgebra ℝ M` is the
  tensor algebra of spacetime `M` (`FieldSymbol`, `fieldSymbol`).
* **`K^form` = the free ℂ-algebra on the field symbols** `= TensorAlgebra ℂ (W ⊗_ℝ TM)` (`KForm`). It is
  **non-commutative** — this is what leaves room for *quantum* fields, whose components do not commute.
* **A differential formula** is an element `F ∈ K^form` (a polynomial in field symbols).
* **The differential operator `D_F`.** A classical field `Φ` assigns to each field symbol its derived
  component `∂_{ξ₁}⋯∂_{ξₙ}(λ∘Φ)`, a `ℂ`-linear map `ev : U →ₗ[ℂ] R` into the *commutative* ℂ-algebra `R` of
  `ℂ`-valued functions. By the universal property of the free algebra this extends to the algebra hom
  `realize ev : K^form →ₐ[ℂ] R` (`realize`), and `D_F(Φ) = realize ev F` (`DF`).

This file proves the structural facts §2.2 relies on:

* **§A–B — field symbols, `K^form`, and `D_F`** (`FieldSymbol`, `fieldSymbol`, `KForm`, `realize`, `DF`,
  `DF_symbol`, `DF_mul`, `DF_add`). `D_F` is the polynomial combination of derived components: an algebra
  hom.
* **§C — classical vs quantum** (`DF_comm`, `DF_commutator_zero`). `K^form` is non-commutative, but every
  *classical* realization lands in a *commutative* `R`, so `D_{Φ^λΦ^μ}(Φ) = D_{Φ^μΦ^λ}(Φ)`: the commutator
  `Φ^λΦ^μ − Φ^μΦ^λ` vanishes on every classical field, *though it is a non-zero formula in `K^form`*. Keeping
  the distinction is exactly what leaves room for non-commuting quantum components.
* **§D — formal field theory and Eq. (6)** (`dynamics`, `dynamics_antitone`, `largestFormalTheory`,
  `mem_largestFormalTheory`, `subset_dynamics_largestFormalTheory`). A formal field theory is a complex
  subspace `D^form ⊆ K^form`, defining the classical theory `D = {Φ | ∀ F ∈ D^form, D_F(Φ) = 0}` (Eq. 6);
  the largest formal theory for a classical `D` is `⋂_{Φ∈D} ker(realize Φ)` — *a complex subspace*, as the
  paper claims.
* **§E — the Lagrangian/Hamiltonian reading** (`densityClass`, `densityClass_affine`,
  `zero_mem_densityClass_iff`, `mem_densityClass_iff_sub_mem_ker`). The formulae defining a fixed density
  `ℐ` form a complex *affine* subspace (a coset of `ker(density)`), which is a subspace **iff `ℐ = 0`** — the
  paper's affine-vs-linear distinction.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2.2 (Definition 1, Eq. 6); App. A.6–A.7 (the
  free algebra). The non-commutativity / quantum-field remark is the paragraph after Eq. 6.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory

open scoped TensorProduct

/-! ## §A — field symbols and `K^form`, the free ℂ-algebra -/

/-- **Field-value covectors** `W = Hom(V, ℂ)`. -/
abbrev WCov (V : Type*) [AddCommGroup V] [Module ℝ V] := V →ₗ[ℝ] ℂ

/-- **The tensor algebra of spacetime** `TM` (the `ξ₁⋯ξₙ` directions). -/
abbrev TMalg (M : Type*) [AddCommGroup M] [Module ℝ M] := TensorAlgebra ℝ M

/-- **The space of field symbols** `W ⊗_ℝ TM` — a complex vector space (the `ℂ`-action via `W`). A field
symbol `Φ^λ_{ξ₁⋯ξₙ}` is `λ ⊗ (ξ₁⋯ξₙ)`. -/
abbrev FieldSymbol (M V : Type*) [AddCommGroup M] [Module ℝ M] [AddCommGroup V] [Module ℝ V] :=
  TensorProduct ℝ (WCov V) (TMalg M)

/-- **The field symbol** `Φ^λ_{ξ} = λ ⊗ ξ`. -/
noncomputable def fieldSymbol {M V : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup V] [Module ℝ V]
    (lam : WCov V) (xi : TMalg M) : FieldSymbol M V := lam ⊗ₜ[ℝ] xi

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-- **`K^form` — the formal field algebra**: the free ℂ-algebra (tensor algebra) on the field symbols `U`.
Non-commutative by construction — the room for quantum (non-commuting) fields. The intended instance is
`U = FieldSymbol M V`. -/
abbrev KForm (U : Type*) [AddCommGroup U] [Module ℂ U] := TensorAlgebra ℂ U

/-! ## §B — the realization homomorphism `D_F` -/

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- **The realization of a classical field**: from its derived-component assignment `ev : U →ₗ[ℂ] R` (field
symbol ↦ `∂_ξ(λ∘Φ)`), the unique algebra hom `K^form →ₐ[ℂ] R` (universal property of the free algebra). -/
noncomputable def realize (ev : U →ₗ[ℂ] R) : KForm U →ₐ[ℂ] R := TensorAlgebra.lift ℂ ev

/-- **The differential operator `D_F(Φ)`** — the formula `F` evaluated on the field with realization `ev`. -/
noncomputable def DF (ev : U →ₗ[ℂ] R) (F : KForm U) : R := realize ev F

/-- A field symbol realizes to its derived component: `D_{Φ^λ_ξ}(Φ) = ∂_ξ(λ∘Φ)`. -/
theorem DF_symbol (ev : U →ₗ[ℂ] R) (s : U) : DF ev (TensorAlgebra.ι ℂ s) = ev s := by
  simp [DF, realize, TensorAlgebra.lift_ι_apply]

/-- `D_F` is the **polynomial** (multiplicative) combination of derived components. -/
theorem DF_mul (ev : U →ₗ[ℂ] R) (F G : KForm U) : DF ev (F * G) = DF ev F * DF ev G := by
  simp [DF, realize]

/-- `D_F` is additive. -/
theorem DF_add (ev : U →ₗ[ℂ] R) (F G : KForm U) : DF ev (F + G) = DF ev F + DF ev G := by
  simp [DF, realize]

/-! ## §C — classical vs quantum: the realization collapses the non-commutativity -/

/-- **[Greaves–Thomas §2.2] The classical realization commutes.** Although `K^form` is non-commutative, a
*classical* field realizes into the *commutative* algebra `R`, so `D_{F·G}(Φ) = D_{G·F}(Φ)`. -/
theorem DF_comm (ev : U →ₗ[ℂ] R) (F G : KForm U) : DF ev (F * G) = DF ev (G * F) := by
  rw [DF_mul, DF_mul, mul_comm]

/-- **[Greaves–Thomas §2.2] The commutator of field symbols vanishes on every classical field.**
`D_{Φ^λΦ^μ − Φ^μΦ^λ}(Φ) = 0` for all `Φ` — even though `Φ^λΦ^μ − Φ^μΦ^λ` is a **non-zero** formula in the
non-commutative `K^form`. Maintaining this distinction is precisely what leaves open the possibility that
`Φ` is a *quantum* field with non-commuting components (a non-commutative codomain `R`, where `DF_comm`
fails). -/
theorem DF_commutator_zero (ev : U →ₗ[ℂ] R) (s t : U) :
    DF ev (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t
      - TensorAlgebra.ι ℂ t * TensorAlgebra.ι ℂ s) = 0 := by
  unfold DF realize
  rw [map_sub, map_mul, map_mul, mul_comm, sub_self]

/-! ## §D — formal field theory and Eq. (6) -/

variable {Φ : Type*}

/-- **[Eq. 6] The classical field theory defined by a formal field theory.** `D = {Φ | ∀ F ∈ D^form,
D_F(Φ) = 0}` — `Φ` is dynamically allowed iff every differential formula of `D^form` vanishes on it. -/
def dynamics (evv : Φ → (U →ₗ[ℂ] R)) (DForm : Set (KForm U)) : Set Φ :=
  {φ | ∀ F ∈ DForm, realize (evv φ) F = 0}

/-- **`dynamics` is antitone**: a larger formal theory (more formulae) carves out a smaller classical
theory (more constraints) — the Galois-type correspondence between `D^form` and `D`. -/
theorem dynamics_antitone (evv : Φ → (U →ₗ[ℂ] R)) {DForm DForm' : Set (KForm U)}
    (h : DForm ⊆ DForm') : dynamics evv DForm' ⊆ dynamics evv DForm :=
  fun _ hφ F hF => hφ F (h hF)

/-- **[Eq. 6 converse] The largest formal field theory for a classical theory `D`** — `⋂_{Φ∈D} ker(realize Φ)`.
Its *type* is `Submodule ℂ (K^form)`: it is **a complex subspace**, exactly as Greaves–Thomas state. -/
noncomputable def largestFormalTheory (evv : Φ → (U →ₗ[ℂ] R)) (D : Set Φ) :
    Submodule ℂ (KForm U) :=
  ⨅ φ ∈ D, LinearMap.ker (realize (evv φ)).toLinearMap

/-- A formula lies in the largest formal theory iff it vanishes on every field of `D`. -/
theorem mem_largestFormalTheory (evv : Φ → (U →ₗ[ℂ] R)) (D : Set Φ) (F : KForm U) :
    F ∈ largestFormalTheory evv D ↔ ∀ φ ∈ D, realize (evv φ) F = 0 := by
  simp [largestFormalTheory, Submodule.mem_iInf, LinearMap.mem_ker]

/-- **Consistency of Eq. 6**: every field of `D` satisfies all formulae of its largest formal theory,
`D ⊆ dynamics(D^form)`. -/
theorem subset_dynamics_largestFormalTheory (evv : Φ → (U →ₗ[ℂ] R)) (D : Set Φ) :
    D ⊆ dynamics evv ((largestFormalTheory evv D : Submodule ℂ (KForm U)) : Set (KForm U)) :=
  fun φ hφ F hF => (mem_largestFormalTheory evv D F).mp hF φ hφ

/-! ## §E — the Lagrangian/Hamiltonian reading: a complex affine subspace -/

variable {Rp : Type*} [AddCommGroup Rp] [Module ℂ Rp]

/-- **The formulae defining a fixed density `ℐ`** (the Lagrangian/Hamiltonian reading). `den` is the map
sending a formula to the density it defines; `densityClass den ℐ` is the set of formulae giving density
`ℐ`. -/
def densityClass (den : KForm U →ₗ[ℂ] Rp) (I : Rp) : Set (KForm U) := {F | den F = I}

/-- **[Greaves–Thomas §2.2] The density class is a complex *affine* subspace** — closed under affine
combinations `c·F + (1−c)·G` (coefficients summing to `1`). -/
theorem densityClass_affine (den : KForm U →ₗ[ℂ] Rp) (I : Rp) (c : ℂ) {F G : KForm U}
    (hF : F ∈ densityClass den I) (hG : G ∈ densityClass den I) :
    c • F + (1 - c) • G ∈ densityClass den I := by
  simp only [densityClass, Set.mem_setOf_eq] at *
  rw [map_add, map_smul, map_smul, hF, hG, ← add_smul, add_sub_cancel, one_smul]

/-- **[Greaves–Thomas §2.2] Affine but not linear**: the density class contains `0` — i.e. is a complex
*subspace* — **iff `ℐ = 0`**. For a non-zero density it is a proper affine subspace, not a subspace. -/
theorem zero_mem_densityClass_iff (den : KForm U →ₗ[ℂ] Rp) (I : Rp) :
    (0 : KForm U) ∈ densityClass den I ↔ I = 0 := by
  simp [densityClass, eq_comm]

/-- **The density class is a coset of `ker(den)`**: `F` defines density `ℐ` iff `F − F₀` is in the kernel,
for any reference `F₀` defining `ℐ`. -/
theorem mem_densityClass_iff_sub_mem_ker (den : KForm U →ₗ[ℂ] Rp) (I : Rp) {F₀ : KForm U}
    (h₀ : F₀ ∈ densityClass den I) (F : KForm U) :
    F ∈ densityClass den I ↔ F - F₀ ∈ LinearMap.ker den := by
  simp only [densityClass, Set.mem_setOf_eq] at *
  rw [LinearMap.mem_ker, map_sub, h₀, sub_eq_zero]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory

end
