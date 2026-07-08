/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory

/-!
# Greaves–Thomas §2.2–2.4: quantum (AQFT) realizations and symmetries of `D^form`

`PTSymmetricQFT.FormalFieldTheory` realized the *classical* case — each field maps into a **commutative**
function algebra, collapsing the non-commutativity of `K^form`. This file expands to the **quantum / AQFT**
case and to the symmetry correspondence, completing the part of *H. Greaves, T. Thomas, "The CPT Theorem"*
(arXiv:1204.4674) §2.2 that says: a theory is specified by a density `ℐ` (a differential formula), but the
*interpretation* — canonical quantization, path integrals, operator distributions — is "largely irrelevant
insofar as we can focus not on `ℐ` itself, but on the collection `D^form` of all differential formulae that
define it"; and the closing remark that **symmetries of `D` correspond to symmetries of `D^form`**.

* **§A — quantum realization into a non-commutative operator algebra** (`quantumRealize`, `quantumDF`,
  `quantumDF_commutator`, `quantumDF_commutator_comm`). A *quantum* field realizes `K^form` into a possibly
  **non-commutative** ℂ-algebra `A` (operator distributions). The realization is still an algebra hom, but
  now the field-symbol commutator `Φ^λΦ^μ − Φ^μΦ^λ` realizes to the **operator commutator**
  `[φ^λ, φ^μ] = φ^λφ^μ − φ^μφ^λ` (`quantumDF_commutator`) — the canonical commutation relations, generally
  non-zero. The classical collapse (`quantumDF_commutator_comm`) is the special case where `A` is
  commutative. This is exactly the non-commutativity that `K^form` keeps room for.
* **§B — symmetries of `D^form` induce symmetries of `D`** (`quantumDynamics`, `Compatible`, `Preserves`,
  `symmetry_preserves_dynamics`). A symmetry is an algebra automorphism `σ : K^form ≃ₐ K^form` together with
  a field transformation `T : Φ → Φ` that are **compatible** — `D_F(Tφ) = D_{σF}(φ)` (transforming the
  field equals transforming the formula). If `σ` **preserves** the formal theory `D^form`, then `T`
  preserves the dynamics `D = dynamics(D^form)`: `Tφ ∈ D ↔ φ ∈ D`. This is the precise content of
  "symmetries of `D` correspond to symmetries of `D^form`."
* **§C — Lagrangian/density invariance is a symmetry** (`density_invariant_preserves`,
  `lagrangian_symmetry`). When `D^form` is a density class (the Lagrangian/Hamiltonian presentation,
  `densityClass den ℐ`), a `σ` that **leaves the density invariant** (`den ∘ σ = den`) preserves `D^form`,
  hence — with a compatible `T` — is a symmetry of the dynamics. An invariant Lagrangian gives a symmetry of
  the equations of motion, *independently of how `ℐ` is interpreted*.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2.2 (the density `ℐ` / `D^form` / method
  independence paragraph) and the closing remark of §2.2 (symmetries of `D` ↔ symmetries of `D^form`),
  made precise in §2.4.
* Repo structure: `PTSymmetricQFT.FormalFieldTheory` (`KForm`, `densityClass`, the classical realization).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-! ## §A — quantum realization into a non-commutative operator algebra (AQFT) -/

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **The quantum realization** of a field into a (possibly non-commutative) operator algebra `A` — the
AQFT / operator-distribution reading. Still an algebra hom (universal property of the free algebra), but the
codomain need not commute. -/
noncomputable def quantumRealize (ev : U →ₗ[ℂ] A) : KForm U →ₐ[ℂ] A := TensorAlgebra.lift ℂ ev

/-- **`D_F(Φ)` for a quantum field** — the formula `F` realized as an operator. -/
noncomputable def quantumDF (ev : U →ₗ[ℂ] A) (F : KForm U) : A := quantumRealize ev F

/-- **[AQFT — the canonical commutation relations] The field-symbol commutator realizes to the operator
commutator.** `D_{Φ^λΦ^μ − Φ^μΦ^λ}(Φ) = φ^λφ^μ − φ^μφ^λ = [φ^λ, φ^μ]` — the non-commutativity of `K^form`
becomes the CCR of the quantum field operators (generally non-zero). -/
theorem quantumDF_commutator (ev : U →ₗ[ℂ] A) (s t : U) :
    quantumDF ev (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t
        - TensorAlgebra.ι ℂ t * TensorAlgebra.ι ℂ s)
      = ev s * ev t - ev t * ev s := by
  unfold quantumDF quantumRealize
  simp only [map_sub, map_mul, TensorAlgebra.lift_ι_apply]

/-- **The classical collapse is the commutative special case.** When the operator algebra is commutative the
field commutator vanishes — recovering `PTSymmetricQFT.FormalFieldTheory.DF_commutator_zero`. -/
theorem quantumDF_commutator_comm {Acomm : Type*} [CommRing Acomm] [Algebra ℂ Acomm]
    (ev : U →ₗ[ℂ] Acomm) (s t : U) :
    quantumDF ev (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t
      - TensorAlgebra.ι ℂ t * TensorAlgebra.ι ℂ s) = 0 := by
  rw [quantumDF_commutator, mul_comm, sub_self]

/-! ## §B — symmetries of `D^form` induce symmetries of `D` -/

variable {Φ : Type*}

/-- The dynamics defined by a formal theory for quantum (or classical) realizations. -/
def quantumDynamics (evv : Φ → (U →ₗ[ℂ] A)) (DForm : Set (KForm U)) : Set Φ :=
  {φ | ∀ F ∈ DForm, quantumRealize (evv φ) F = 0}

/-- **Compatibility of a field transformation with a formula automorphism**: `D_F(Tφ) = D_{σF}(φ)`.
Transforming the field equals transforming the formula — the duality underlying every geometric symmetry. -/
def Compatible (evv : Φ → (U →ₗ[ℂ] A)) (T : Φ → Φ) (σ : KForm U ≃ₐ[ℂ] KForm U) : Prop :=
  ∀ φ F, quantumRealize (evv (T φ)) F = quantumRealize (evv φ) (σ F)

/-- **`σ` preserves the formal field theory `D^form`** (a symmetry of `D^form`). -/
def Preserves (σ : KForm U ≃ₐ[ℂ] KForm U) (DForm : Set (KForm U)) : Prop :=
  ∀ F, (σ F ∈ DForm ↔ F ∈ DForm)

/-- **[Greaves–Thomas §2.2/2.4] Symmetries of `D^form` are symmetries of `D`.** If the field transformation
`T` is compatible with a formula automorphism `σ` that preserves the formal theory `D^form`, then `T`
preserves the dynamics: `Tφ ∈ D ↔ φ ∈ D`. This is the precise sense in which symmetries of the theory
correspond to symmetries of the defining formulae. -/
theorem symmetry_preserves_dynamics (evv : Φ → (U →ₗ[ℂ] A)) (T : Φ → Φ)
    (σ : KForm U ≃ₐ[ℂ] KForm U) (DForm : Set (KForm U))
    (hcompat : Compatible evv T σ) (hpres : Preserves σ DForm) (φ : Φ) :
    T φ ∈ quantumDynamics evv DForm ↔ φ ∈ quantumDynamics evv DForm := by
  constructor
  · intro h G hG
    have hmem : σ.symm G ∈ DForm := by
      have hh := hpres (σ.symm G); rw [σ.apply_symm_apply] at hh; exact hh.mp hG
    have h2 := h (σ.symm G) hmem
    rw [hcompat, σ.apply_symm_apply] at h2
    exact h2
  · intro h F hF
    rw [hcompat]
    exact h (σ F) ((hpres F).mpr hF)

/-! ## §C — Lagrangian/density invariance is a symmetry (method-independent) -/

variable {Rp : Type*} [AddCommGroup Rp] [Module ℂ Rp]

/-- **A density-invariant automorphism preserves the formal theory.** If `σ` leaves the density map
invariant (`den ∘ σ = den`), then it preserves every density class `D^form = densityClass den ℐ` (the
Lagrangian/Hamiltonian presentation). -/
theorem density_invariant_preserves (den : KForm U →ₗ[ℂ] Rp) (I : Rp)
    (σ : KForm U ≃ₐ[ℂ] KForm U) (hden : ∀ F, den (σ F) = den F) :
    Preserves σ (densityClass den I) := by
  intro F
  simp only [densityClass, Set.mem_setOf_eq, hden]

/-- **[Greaves–Thomas] An invariant Lagrangian gives a symmetry of the dynamics.** If `σ` leaves the density
(Lagrangian/Hamiltonian) invariant and is compatible with the field transformation `T`, then `T` is a
symmetry of the equations of motion `D = dynamics(densityClass den ℐ)` — *independently of how the density
`ℐ` is interpreted* (canonical, path-integral, …). -/
theorem lagrangian_symmetry (evv : Φ → (U →ₗ[ℂ] A)) (T : Φ → Φ)
    (σ : KForm U ≃ₐ[ℂ] KForm U) (den : KForm U →ₗ[ℂ] Rp) (I : Rp)
    (hcompat : Compatible evv T σ) (hden : ∀ F, den (σ F) = den F) (φ : Φ) :
    T φ ∈ quantumDynamics evv (densityClass den I)
      ↔ φ ∈ quantumDynamics evv (densityClass den I) :=
  symmetry_preserves_dynamics evv T σ _ hcompat (density_invariant_preserves den I σ hden) φ

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry

end
