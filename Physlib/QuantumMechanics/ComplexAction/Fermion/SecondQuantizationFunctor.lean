/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The fermionic second-quantization functor `K ↦ Fock(K)`

`Bogoliubov.CARAlgebraAutomorphism` proved the gauge Bogoliubov transformation preserves the CAR but left the
**Fock functor** `K ↦ Λ(K)` unbuilt. This file supplies it, for fermions, on the exact algebraic structure
that *is* the fermionic Fock space: the **exterior algebra** `ExteriorAlgebra ℂ K`. The wedge square
`ι(f)² = 0` is precisely Pauli exclusion `{a†(f), a†(f)} = 0`, so the antisymmetric tensor algebra is the
finite-particle fermionic Fock space, with `ι(f) = a†(f)|0⟩` the one-particle creation.

**The functor.**

* **Objects** `K ↦ Fock(K) := ExteriorAlgebra ℂ K` (`FermionFock`), with creation `a†(f) = ι(f)`
  (`creation`) satisfying the creation CAR `{a†(f), a†(g)} = 0` (`creation_anticomm`, `creation_sq` = Pauli).
* **Morphisms** `U ↦ Γ(U) := ExteriorAlgebra.map U` (`secondQuant`), the second quantization of a one-particle
  map `U : K →ₗ K'` as an algebra homomorphism `Fock(K) →ₐ Fock(K')`.
* **Functoriality**: `Γ(id) = id` (`secondQuant_id`) and `Γ(V ∘ U) = Γ(V) ∘ Γ(U)` (`secondQuant_comp`).

**The defining intertwining (second quantization implements the one-particle map).**

  `Γ(U)(a†(f)·x) = a†(U f)·Γ(U)(x)`   (`secondQuant_creation_mul`),

i.e. `Γ(U) a†(f) Γ(U)⁻¹ = a†(U f)`. For a one-particle isomorphism `U` (a gauge Bogoliubov rotation),
`Γ(U)` is an **algebra automorphism of the Fock space** (`secondQuantEquiv`) — the *unitary (algebraic)
implementation* on Fock space of the gauge Bogoliubov automorphism that `Bogoliubov.CARAlgebraAutomorphism`
showed preserves the CAR. So the gauge case of the Shale–Stinespring implementation is exact and complete.

**The annihilation operator and the full CAR.** Over an inner-product one-particle space `H`, the
annihilation operator is the **interior product (contraction)** by the inner dual `⟨f, ·⟩`,
`a(f) = ⟨f,·⟩⌋(·)` (`annihilation`, Mathlib `CliffordAlgebra.contractLeft`). It squares to zero
(`annihilation_sq`, Pauli) and closes the **full CAR**

  `{a(f), a†(g)} = a(f)(a†(g)·x) + a†(g)·a(f)(x) = ⟨f, g⟩·x`   (`creation_annihilation_car`),

from `CliffordAlgebra.contractLeft_ι_mul`. So both canonical anticommutation relations hold algebraically on
the Fock space.

**Honest scope (what remains).** With the full CAR now in place, the remaining piece is purely the
**Hilbert-space completion**: the **Fock inner product** (the Slater/Gram-determinant form on antisymmetric
tensors — absent from Mathlib: there is an inner product on `TensorProduct` but none on `ExteriorAlgebra` /
`exteriorPower`), which is what would make `Γ(U)` a *unitary* and `a(f)` the literal *adjoint* of `a†(f)`; and
the antiparticle/Nambu **mixing** case, whose unitary implementability is the Shale–Stinespring criterion —
unstatable without a Hilbert–Schmidt operator ideal, which Mathlib does not have. This file completes the
*functor and the CAR representation*; the analytic completion (inner product → unitarity; HS → mixing) is the
remaining frontier.

* **§A — the Fock object and creation CAR** (`FermionFock`, `creation`, `creation_sq`, `creation_anticomm`).
* **§B — the functor and functoriality** (`secondQuant`, `secondQuant_id`, `secondQuant_comp`).
* **§C — intertwining and the implemented Bogoliubov** (`secondQuant_creation`, `secondQuant_creation_mul`,
  `secondQuantEquiv`).
* **§D — annihilation and the full CAR** (`annihilation`, `annihilation_sq`, `creation_annihilation_car`).

## References

* Second quantization / the CAR functor (Araki; the exterior algebra as fermionic Fock space). Carriers:
  `Mathlib.LinearAlgebra.ExteriorAlgebra` (`ι_sq_zero`, `map`, `map_id`, `map_comp_map`, `map_apply_ι`);
  cf. `Bogoliubov.CARAlgebraAutomorphism`, `BoseFermiOperatorAlgebra.CompositeFermionCAR`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.SecondQuantizationFunctor

open ExteriorAlgebra

variable {K K' K'' : Type*}
  [AddCommGroup K] [Module ℂ K] [AddCommGroup K'] [Module ℂ K'] [AddCommGroup K''] [Module ℂ K'']


/-- **The fermionic Fock space** `Fock(K) = Λ(K)` — the exterior (antisymmetric tensor) algebra of the
one-particle space `K`. The finite-particle fermionic Fock space, with `ι(f)` the one-particle state. -/
abbrev FermionFock (K : Type*) [AddCommGroup K] [Module ℂ K] : Type _ := ExteriorAlgebra ℂ K

/-- **The creation operator** `a†(f) = ι(f)` — the one-particle creation, realized as the exterior-algebra
generator (left multiplication by `ι(f)` is the creation operator on Fock space). -/
def creation (f : K) : FermionFock K := ι ℂ f

/-- **[Pauli] `a†(f)² = 0`** — the wedge square vanishes, `{a†(f), a†(f)} = 0`. -/
lemma creation_sq (f : K) : creation f * creation f = 0 := ι_sq_zero f

/-- **[The creation CAR] `{a†(f), a†(g)} = a†(f) a†(g) + a†(g) a†(f) = 0`** — creation operators anticommute,
from `ι(f + g)² = 0` expanded. -/
lemma creation_anticomm (f g : K) : creation f * creation g + creation g * creation f = 0 := by
  have h : ι ℂ (f + g) * ι ℂ (f + g) = (0 : FermionFock K) := ι_sq_zero _
  simp only [map_add, add_mul, mul_add, ι_sq_zero, zero_add, add_zero] at h
  simp only [creation]
  rw [add_comm]
  simp


/-- **The second-quantization functor on morphisms** `Γ(U) = ExteriorAlgebra.map U` — the second quantization
of a one-particle map `U : K →ₗ K'`, an algebra homomorphism `Fock(K) →ₐ Fock(K')`. -/
def secondQuant (U : K →ₗ[ℂ] K') : FermionFock K →ₐ[ℂ] FermionFock K' := ExteriorAlgebra.map U

/-- **[Functoriality: identity] `Γ(id) = id`.** -/
lemma secondQuant_id : secondQuant (LinearMap.id : K →ₗ[ℂ] K) = AlgHom.id ℂ (FermionFock K) :=
  ExteriorAlgebra.map_id

/-- **[Functoriality: composition] `Γ(V ∘ U) = Γ(V) ∘ Γ(U)`.** -/
lemma secondQuant_comp (U : K →ₗ[ℂ] K') (V : K' →ₗ[ℂ] K'') :
    secondQuant (V ∘ₗ U) = (secondQuant V).comp (secondQuant U) :=
  (ExteriorAlgebra.map_comp_map U V).symm


/-- **[Second quantization intertwines creation] `Γ(U)(a†(f)) = a†(U f)`.** -/
lemma secondQuant_creation (U : K →ₗ[ℂ] K') (f : K) :
    secondQuant U (creation f) = creation (U f) :=
  ExteriorAlgebra.map_apply_ι U f

/-- **[The defining intertwining] `Γ(U)(a†(f)·x) = a†(U f)·Γ(U)(x)`** — equivalently
`Γ(U) a†(f) Γ(U)⁻¹ = a†(U f)`: the second quantization `Γ(U)` implements the one-particle map `U` on the
creation operators of Fock space. -/
lemma secondQuant_creation_mul (U : K →ₗ[ℂ] K') (f : K) (x : FermionFock K) :
    secondQuant U (creation f * x) = creation (U f) * secondQuant U x := by
  rw [map_mul, secondQuant_creation]

/-- **[The implemented gauge Bogoliubov] `Γ(U)` is an algebra automorphism of Fock space.** For a one-particle
isomorphism `U` (a gauge Bogoliubov rotation), the second quantization `Γ(U)` is an algebra **equivalence**
`Fock(K) ≃ₐ Fock(K')`, with inverse `Γ(U⁻¹)` (by functoriality). This is the unitary (algebraic)
implementation on Fock space of the gauge Bogoliubov automorphism `a†(f) ↦ a†(U f)`. -/
noncomputable def secondQuantEquiv (U : K ≃ₗ[ℂ] K') : FermionFock K ≃ₐ[ℂ] FermionFock K' :=
  AlgEquiv.ofAlgHom (secondQuant U.toLinearMap) (secondQuant U.symm.toLinearMap)
    (by
      have h : U.toLinearMap ∘ₗ U.symm.toLinearMap = LinearMap.id := by ext x; simp
      show (ExteriorAlgebra.map U.toLinearMap).comp (ExteriorAlgebra.map U.symm.toLinearMap)
        = AlgHom.id ℂ (FermionFock K')
      rw [ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id])
    (by
      have h : U.symm.toLinearMap ∘ₗ U.toLinearMap = LinearMap.id := by ext x; simp
      show (ExteriorAlgebra.map U.symm.toLinearMap).comp (ExteriorAlgebra.map U.toLinearMap)
        = AlgHom.id ℂ (FermionFock K)
      rw [ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id])


section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The annihilation operator** `a(f) = ⟨f, ·⟩⌋(·)` — the interior product (contraction) by the inner dual
`⟨f, ·⟩` of `f`, antilinear in `f`. The adjoint of creation (`CliffordAlgebra.contractLeft`). -/
noncomputable def annihilation (f : H) (x : FermionFock H) : FermionFock H :=
  CliffordAlgebra.contractLeft (innerSL ℂ f).toLinearMap x

/-- **[Pauli for annihilation] `a(f)² = 0`** (`CliffordAlgebra.contractLeft_contractLeft`). -/
lemma annihilation_sq (f : H) (x : FermionFock H) : annihilation f (annihilation f x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ x

/-- **[The full CAR] `{a(f), a†(g)} = ⟨f, g⟩`** — `a(f)(a†(g)·x) + a†(g)·a(f)(x) = ⟨f, g⟩·x`, from
`CliffordAlgebra.contractLeft_ι_mul`. Together with `creation_anticomm` and `annihilation_sq`, this is the
complete canonical anticommutation relations on the fermionic Fock space `Λ(H)`. -/
lemma creation_annihilation_car (f g : H) (x : FermionFock H) :
    annihilation f (creation g * x) + creation g * annihilation f x = inner ℂ f g • x := by
  simp only [annihilation, creation]
  rw [CliffordAlgebra.contractLeft_ι_mul]
  have hd : (innerSL ℂ f).toLinearMap g = inner ℂ f g := rfl
  rw [hd]
  abel

end Hilbert

end Physlib.QuantumMechanics.ComplexAction.Fermion.SecondQuantizationFunctor

end
