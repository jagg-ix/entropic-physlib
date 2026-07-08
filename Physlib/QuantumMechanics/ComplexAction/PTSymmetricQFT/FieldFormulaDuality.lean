/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.GeometricAction

/-!
# Greaves–Thomas §2.4: the field-side ↔ formula-side correspondence, made precise

`PTSymmetricQFT.GeometricAction` gave the symmetries on the *field* side — the geometric action `u(g)` on
`K = M → V` and its symmetry subgroup. `PTSymmetricQFT.QuantumSymmetry` gave the symmetries on the *formula*
side — automorphisms `σ` of `K^form` that `Preserve` a formal field theory `D^form`. This file makes their
correspondence (the content of §2.4 of *H. Greaves, T. Thomas, "The CPT Theorem"*, arXiv:1204.4674) precise
and **functorial**.

The bridge is the tensor algebra functor. A linear transformation `f : U →ₗ U` of the field symbols induces,
on one side, a transformation of fields (acting on their derived components by `f`), and on the other, the
algebra hom `σ = tensorMap f` of `K^form = TensorAlgebra ℂ U`. The realization `D_F(Φ)` intertwines them:

  `realize (ev ∘ f) = (realize ev) ∘ σ`     (`realize_comp_tensorMap`),

i.e. **`D_F` of a field whose derived components are transformed by `f` equals `D_{σF}` of the original** —
which is exactly the `Compatible` condition of `PTSymmetricQFT.QuantumSymmetry`. Hence a field symmetry and
its dual formula automorphism are two faces of one functor, and a symmetry of `D` is a symmetry of
`D^form`.

* **§A — the tensor algebra functor** (`tensorMap`, `tensorMap_ι`, `tensorMap_id`, `tensorMap_comp`). A
  linear map on field symbols lifts to an algebra hom on `K^form`, functorially (`σ(id) = id`,
  `σ(f∘g) = σ(f)∘σ(g)`).
* **§B — the formula-side automorphism** (`tensorAlgEquiv`, `tensorAlgEquiv_apply`). A *linear equivalence*
  `e` of field symbols gives the algebra **automorphism** `σ = tensorAlgEquiv e` of `K^form` — the dual of a
  field symmetry.
* **§C — the bridge** (`realize_comp_tensorMap`, `compatible_of_linear`). The realization intertwines the
  field-symbol transformation with the formula automorphism, so a field transformation `T` with
  `ev(Tφ) = ev(φ) ∘ e` is automatically `Compatible` with `σ = tensorAlgEquiv e`.
* **§D — the correspondence** (`field_formula_symmetry`). Combining with
  `PTSymmetricQFT.QuantumSymmetry.symmetry_preserves_dynamics`: if the dual formula automorphism
  `tensorAlgEquiv e` **preserves** `D^form`, then the field transformation `T` is a **symmetry of the
  dynamics** `D = dynamics(D^form)`. This is the precise §2.4 statement that symmetries of `D` correspond to
  symmetries of `D^form`.

The geometric action of §2.3 is the special case where `e = ω(g⁻¹) ⊗ ρ(g)` acts on the field symbols
`U = W ⊗ TM`: `T = u(g)`, and `σ(g) = tensorAlgEquiv e` is its formula-side dual. The `CPT`/`PT` theorems are
this at `g = ` total inversion.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2.3–2.4 (geometric actions and their dual
  action on differential formulae).
* Repo dependencies: `PTSymmetricQFT.FormalFieldTheory` (`KForm`); `PTSymmetricQFT.QuantumSymmetry`
  (`quantumRealize`, `Compatible`, `Preserves`, `symmetry_preserves_dynamics`);
  `PTSymmetricQFT.GeometricAction` (the field-side geometric action).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldFormulaDuality

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-! ## §A — the tensor algebra functor `f ↦ σ` -/

/-- **The formula-side transformation `σ = tensorMap f`** induced by a linear map `f` of the field symbols:
the algebra hom of `K^form = TensorAlgebra ℂ U` sending `Φ^λ ↦ Φ^{f λ}`. -/
noncomputable def tensorMap (f : U →ₗ[ℂ] U) : KForm U →ₐ[ℂ] KForm U :=
  TensorAlgebra.lift ℂ ((TensorAlgebra.ι ℂ).comp f)

/-- `σ` acts on a field symbol by `f`: `σ(Φ^λ) = Φ^{f λ}`. -/
theorem tensorMap_ι (f : U →ₗ[ℂ] U) (s : U) :
    tensorMap f (TensorAlgebra.ι ℂ s) = TensorAlgebra.ι ℂ (f s) := by
  simp [tensorMap, TensorAlgebra.lift_ι_apply]

/-- **Functoriality: `σ(id) = id`.** -/
theorem tensorMap_id : tensorMap (LinearMap.id : U →ₗ[ℂ] U) = AlgHom.id ℂ (KForm U) := by
  apply TensorAlgebra.hom_ext; ext s; simp [tensorMap_ι]

/-- **Functoriality: `σ(f∘g) = σ(f)∘σ(g)`.** -/
theorem tensorMap_comp (f g : U →ₗ[ℂ] U) :
    tensorMap (f.comp g) = (tensorMap f).comp (tensorMap g) := by
  apply TensorAlgebra.hom_ext; ext s; simp [tensorMap_ι]

/-! ## §B — the formula-side automorphism from a field-symbol equivalence -/

/-- **The formula-side automorphism `σ = tensorAlgEquiv e`** of `K^form` induced by a linear *equivalence*
`e` of the field symbols — the dual of a field symmetry. -/
noncomputable def tensorAlgEquiv (e : U ≃ₗ[ℂ] U) : KForm U ≃ₐ[ℂ] KForm U :=
  AlgEquiv.ofAlgHom (tensorMap (e : U →ₗ[ℂ] U)) (tensorMap (e.symm : U →ₗ[ℂ] U))
    (by rw [← tensorMap_comp]; simp [tensorMap_id])
    (by rw [← tensorMap_comp]; simp [tensorMap_id])

@[simp] theorem tensorAlgEquiv_apply (e : U ≃ₗ[ℂ] U) (F : KForm U) :
    tensorAlgEquiv e F = tensorMap (e : U →ₗ[ℂ] U) F := rfl

/-! ## §C — the bridge: the realization intertwines the two sides -/

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **[The intertwiner] `realize (ev ∘ f) = (realize ev) ∘ σ`.** Realizing a field whose derived components
are transformed by `f` equals realizing the original field of the `σ`-transformed formula — `D_F` includes the
field-symbol transformation `f` to the formula automorphism `tensorMap f`. -/
theorem realize_comp_tensorMap (ev : U →ₗ[ℂ] A) (f : U →ₗ[ℂ] U) :
    quantumRealize (ev.comp f) = (quantumRealize ev).comp (tensorMap f) := by
  apply TensorAlgebra.hom_ext; ext s
  simp [quantumRealize, tensorMap_ι, TensorAlgebra.lift_ι_apply]

/-- **[Field ↔ formula] A field transformation acting by `e` on derived components is `Compatible` with its
dual formula automorphism.** If `ev(Tφ) = ev(φ) ∘ e` (the geometric action on derived components), then `T`
satisfies `D_F(Tφ) = D_{σF}(φ)` with `σ = tensorAlgEquiv e`. -/
theorem compatible_of_linear {Φ : Type*} (evv : Φ → (U →ₗ[ℂ] A)) (T : Φ → Φ) (e : U ≃ₗ[ℂ] U)
    (hT : ∀ φ, evv (T φ) = (evv φ).comp (e : U →ₗ[ℂ] U)) :
    Compatible evv T (tensorAlgEquiv e) := by
  intro φ F
  rw [hT, realize_comp_tensorMap, AlgHom.comp_apply, tensorAlgEquiv_apply]

/-! ## §D — the correspondence: symmetry of `D` ⟺ symmetry of `D^form` -/

/-- **[Greaves–Thomas §2.4] Symmetries of `D` correspond to symmetries of `D^form`.** If a field
transformation `T` acts by the field-symbol equivalence `e` on derived components, and the dual formula
automorphism `σ = tensorAlgEquiv e` **preserves** the formal field theory `D^form`, then `T` is a symmetry
of the dynamics `D = dynamics(D^form)`: `Tφ ∈ D ↔ φ ∈ D`. The field-side symmetry and the formula-side
symmetry are the two faces of the single functor `tensorMap`. -/
theorem field_formula_symmetry {Φ : Type*} (evv : Φ → (U →ₗ[ℂ] A)) (T : Φ → Φ) (e : U ≃ₗ[ℂ] U)
    (DForm : Set (KForm U)) (hT : ∀ φ, evv (T φ) = (evv φ).comp (e : U →ₗ[ℂ] U))
    (hpres : Preserves (tensorAlgEquiv e) DForm) (φ : Φ) :
    T φ ∈ quantumDynamics evv DForm ↔ φ ∈ quantumDynamics evv DForm :=
  symmetry_preserves_dynamics evv T (tensorAlgEquiv e) DForm
    (compatible_of_linear evv T e hT) hpres φ

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldFormulaDuality

end
