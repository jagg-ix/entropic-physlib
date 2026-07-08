/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

/-!
# The dual-sphere holonomy defect is the cross-product norm: Levi-Civita meets the dual sphere

Links the Levi-Civita tensor (`LeviCivita.Tensor`, the cross product `(a × b)_i = ∑_{jk} ε_{ijk} a_j b_k`)
to the Navier–Stokes **dual-sphere fiber decomposition** (`Hopf.DualSphereFiberDecomposition`, the cross-sphere
alignment term `|ξ × η|²`).

The dual-sphere holonomy defect — the cross-sphere alignment `crossSphereDefect ξ η = |ξ × η|²` that
measures the non-collinearity of the geometric vorticity sphere and the information sphere — is *exactly*
the squared norm of Mathlib's `crossProduct`:

  `crossSphereDefect ξ η = ∑_i (ξ × η)_i²`   (`crossSphereDefect_eq_crossProduct_normSq`),

hence the **Levi-Civita contraction** `∑_i (∑_{jk} ε_{ijk} ξ_j η_k)²`
(`crossSphereDefect_eq_leviCivita_normSq`). The **Lagrange identity** proved on the dual-sphere defect,
`|ξ × η|² = ‖ξ‖²‖η‖² − ⟨ξ, η⟩²`, is therefore the geometric (Binet–Cauchy) form of the ε–δ identity,
holding for Mathlib's `crossProduct` (`crossProduct_normSq_lagrange`).

* **§A — the dual-sphere defect is the cross-product norm²**
  (`crossSphereDefect_eq_crossProduct_normSq`, `crossSphereDefect_eq_leviCivita_normSq`).
* **§B — the Lagrange identity for the cross product** (`crossProduct_normSq_lagrange`).

## References

* The Binet–Cauchy / Lagrange identity `‖a × b‖² = ‖a‖²‖b‖² − ⟨a,b⟩²`. structures: `LeviCivita.Tensor`
  (`crossProduct_eq_leviCivita`, `leviCivita3`), `Hopf.DualSphereFiberDecomposition` (`crossSphereDefect`,
  `crossSphereDefect_lagrange`), Mathlib's `crossProduct`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.CrossSphere

open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionLieAlgebra
open Matrix

/-! ## §A — the dual-sphere holonomy defect is the cross-product norm² -/

/-- **[The cross-sphere alignment is the cross-product norm²] `|ξ × η|² = ∑_i (ξ × η)_i²`.** The
dual-sphere holonomy defect (the cross-sphere alignment of `Hopf.DualSphereFiberDecomposition`) is exactly the
squared norm of Mathlib's `crossProduct`. -/
theorem crossSphereDefect_eq_crossProduct_normSq (ξ η : Fin 3 → ℝ) :
    crossSphereDefect ξ η = ∑ i, crossProduct ξ η i ^ 2 := by
  unfold crossSphereDefect
  simp only [Fin.sum_univ_three, cross_apply]
  dsimp only [Matrix.cons_val]

/-- **[The dual-sphere defect is the Levi-Civita contraction] `|ξ × η|² = ∑_i (∑_{jk} ε_{ijk} ξ_j η_k)²`.**
The cross-sphere alignment written through the Levi-Civita tensor. -/
theorem crossSphereDefect_eq_leviCivita_normSq (ξ η : Fin 3 → ℝ) :
    crossSphereDefect ξ η = ∑ i, (∑ j, ∑ k, (leviCivita3 i j k : ℝ) * ξ j * η k) ^ 2 := by
  rw [crossSphereDefect_eq_crossProduct_normSq]
  exact Finset.sum_congr rfl fun i _ => by rw [crossProduct_eq_leviCivita]

/-! ## §B — the Lagrange (Binet–Cauchy) identity for the cross product -/

/-- **[The Lagrange identity for the cross product] `‖ξ × η‖² = ‖ξ‖²‖η‖² − ⟨ξ, η⟩²`.** Combining the
dual-sphere identification with the dual-sphere Lagrange identity (`crossSphereDefect_lagrange`), Mathlib's
`crossProduct` satisfies the Binet–Cauchy identity — the geometric form of the ε–δ identity. -/
theorem crossProduct_normSq_lagrange (ξ η : Fin 3 → ℝ) :
    ∑ i, crossProduct ξ η i ^ 2 = sphereNormSq ξ * sphereNormSq η - (sphereInner ξ η) ^ 2 := by
  rw [← crossSphereDefect_eq_crossProduct_normSq, crossSphereDefect_lagrange]

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.CrossSphere

end
