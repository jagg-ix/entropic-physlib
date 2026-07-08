/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic

/-!
# The gluon Lie bracket: structure constants, three- and four-gluon vertices

Grounds the gluon self-interaction in the actual **Lie bracket** (matrix commutator) of the gauge-field
algebra. Gauge fields are matrices `Matrix (Fin n) (Fin n) ℂ` (`n = 3` for the `su(3)` gluons, `n = 2` for
the `su(2)` weak bosons); their bracket is the commutator `⁅A, B⁆ = A·B − B·A`
(`Mathlib.Algebra.Lie.OfAssociative`), whose components in a generator basis are the structure constants
`⁅Tₐ, T_b⁆ = f^{abc} T_c`.

* **§A — the three-gluon vertex is the commutator.** `gluon_vertex_commutator` (`⁅A,B⁆ = A·B − B·A`),
 **antisymmetric** `gluon_vertex_antisymm` (`⁅A,B⁆ = −⁅B,A⁆` — the `f^{abc}` antisymmetry), and
 `gluon_self_vertex_zero` (`⁅A,A⁆ = 0`).
* **§B — the Jacobi identity (four-gluon consistency).** `gluon_jacobi`
 (`⁅A,⁅B,C⁆⁆ + ⁅B,⁅C,A⁆⁆ + ⁅C,⁅A,B⁆⁆ = 0`) — the structure-constant Jacobi `f^{abe}f^{ecd} + ⟲ = 0` that
 makes the nested (four-gluon) vertices consistent.
* **§C — the abelian contrast.** `abelian_vertex_zero` — commuting (abelian, `U(1)`/photon) fields have
 vanishing bracket: no photon self-vertex.
* **§D — the main result** `gluon_lie_structure`.

This is the concrete Lie-algebraic origin later used by the non-Abelian three-vertex layer: the bracket's
antisymmetry and Jacobi *are* the structure-constant antisymmetry and Jacobi behind the color factors
`c_s+c_t+c_u=0`. This `3`-structure is shared by every non-abelian group (`su(3)` and `su(2)` alike) and is
**distinct** from the `ℤ/3` colour centre.

Proven from Mathlib's commutator Lie ring: the bracket is antisymmetric, self-annihilating,
and satisfies the cyclic Jacobi, while commuting fields bracket to zero. The full `su(3)` Gell-Mann basis and
the explicit `f^{abc}` numerics, and the gauge-field dynamics, are not built — the bracket encodes the same
antisymmetry/Jacobi basis-free.

## References

* Yang–Mills self-interaction; structure constants `⁅Tₐ,T_b⁆ = f^{abc}T_c`, antisymmetry + Jacobi. Mathlib
 (`Algebra.Lie.OfAssociative`, `lie_skew`, `lie_jacobi`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra

variable {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ)

/-! ## §A — the three-gluon vertex is the commutator bracket -/

/-- **[The three-gluon vertex is the commutator]** `⁅A, B⁆ = A·B − B·A` — two gauge fields couple through
their commutator (the cubic `A³` term of `F = dA + g[A,A]`). -/
theorem gluon_vertex_commutator : ⁅A, B⁆ = A * B - B * A := Ring.lie_def A B

/-- **[The three-gluon vertex is antisymmetric]** `⁅A, B⁆ = −⁅B, A⁆` — the structure constants `f^{abc}` are
antisymmetric in the first two indices. -/
theorem gluon_vertex_antisymm : ⁅A, B⁆ = -⁅B, A⁆ := by
  rw [Ring.lie_def, Ring.lie_def]; abel

/-- **[A gluon does not self-couple to its own copy]** `⁅A, A⁆ = 0`. -/
theorem gluon_self_vertex_zero : ⁅A, A⁆ = 0 := by rw [Ring.lie_def, sub_self]

/-! ## §B — the Jacobi identity (four-gluon-vertex consistency) -/

/-- **[The structure-constant Jacobi identity]** `⁅A,⁅B,C⁆⁆ + ⁅B,⁅C,A⁆⁆ + ⁅C,⁅A,B⁆⁆ = 0` — the cyclic Jacobi
`f^{abe}f^{ecd} + ⟲ = 0`, the consistency condition for the nested (four-gluon) vertices. -/
theorem gluon_jacobi : ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 := by
  simp only [Ring.lie_def]; noncomm_ring

/-! ## §C — the abelian (photon) contrast -/

/-- **[Abelian fields have no self-vertex]** if `A` and `B` commute (an abelian `U(1)` gauge theory, e.g. the
photon), their bracket vanishes — `⁅A, B⁆ = 0`: no self-interaction. -/
theorem abelian_vertex_zero (h : A * B = B * A) : ⁅A, B⁆ = 0 := by
  rw [Ring.lie_def, h, sub_self]

/-! ## §D — the gluon Lie structure, assembled -/

/-- **[The gluon Lie structure]** the gauge-field bracket is antisymmetric (`⁅A,B⁆ = −⁅B,A⁆`), self-annihilating
(`⁅A,A⁆=0`), and satisfies the cyclic Jacobi identity — the three-gluon vertex and its four-gluon (Jacobi)
consistency. -/
theorem gluon_lie_structure :
    ⁅A, B⁆ = -⁅B, A⁆
      ∧ ⁅A, A⁆ = 0
      ∧ ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 :=
  ⟨by rw [Ring.lie_def, Ring.lie_def]; abel, by rw [Ring.lie_def, sub_self],
    by simp only [Ring.lie_def]; noncomm_ring⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra

end
