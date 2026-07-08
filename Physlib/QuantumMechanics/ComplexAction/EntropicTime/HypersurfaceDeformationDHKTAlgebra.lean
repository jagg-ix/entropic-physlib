/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian

/-!
# The DHKT hypersurface-deformation algebra (Ipek–Abedi–Caticha §4, Eqs 24–26)

Formalizes the Dirac–Hojman–Kuchař–Teitelboim (DHKT) **hypersurface deformation algebra** of §4 of
Ipek–Abedi–Caticha (arXiv:1803.07493, Eqs. 23–26) — the algebra of normal (`G_⊥`) and tangential (`G_i`) surface
deformations that any covariant local-time dynamics must represent (the path-independence / foliation-invariance
requirement of §5). In smeared form, with `H(N)` the normal generator (lapse `N`) and `P(v)` the tangential
generator (shift `v`), and the bracket the commutator (`collisionStar`), the Dirac algebra is

* `[P(v), P(w)] = P([v,w])` — tangential deformations close on the **vector-field Lie algebra** (Eq. 26);
* `[P(v), H(N)] = H(L_v N)` — the normal generator transforms as a **scalar** under tangential deformations
 (Eq. 25);
* `[H(N), H(M)] = P(𝔤(N∇M − M∇N))` — two normal deformations close on a **tangential** one, with a
 **metric-dependent** structure "constant" `𝔤` (Eq. 24).

The last relation's metric dependence is why the deformations form an *algebra* but not a *group* (the structure
"constants" depend on the surface metric). Here (`DHKTAlgebra`) these are the defining brackets, from which:

* the tangential bracket is **antisymmetric** `P([v,w]) = −P([w,v])` (`momentum_bracket_antisym`) and the
 normal–normal bracket likewise `P(𝔤(N,M)) = −P(𝔤(M,N))` (`hamiltonian_bracket_antisym`) — from the commutator
 antisymmetry;
* the generators satisfy the **Jacobi identity** (`dhkt_jacobi`) — the algebraic closure that is the
 foliation-invariance / path-independence consistency of §5.

So the DHKT algebra is realized as commutators of the smeared deformation generators, with the exact bracket
relations of Eqs. 24–26 and their antisymmetry / Jacobi consequences — the kinematic algebra that consistent
entropic dynamics must represent.

* **§A — the DHKT algebra** (`DHKTAlgebra`).
* **§B — antisymmetry of the brackets** (`momentum_bracket_antisym`, `hamiltonian_bracket_antisym`).
* **§C — the Jacobi identity (path independence)** (`dhkt_jacobi`).

The bracket relations (Eqs. 24–26) are the defining fields of the structure (reusing
`collisionStar` for the commutator); the antisymmetry and Jacobi consequences are exact `collisionStar` algebra.
The functional-`δ`/`∂_iδ(x,x')` realization of the generators and the explicit metric structure "constants"
(Eq. 24 RHS) are the intended reading, represented as the abstract `lie`, `lieDeriv`, `metricBracket` data. No new
axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §4 (Eqs. 23–26); P.A.M. Dirac; C. Teitelboim; K. Kuchař
 (hypersurface deformation algebra). Repo structure: `CollisionOperatorSl2.CollisionModular` (`collisionStar`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HypersurfaceDeformationDHKTAlgebra

variable {R : Type*} [Ring R]

/-! ## §A — the DHKT hypersurface deformation algebra -/

/-- **The DHKT hypersurface deformation algebra** (Ipek–Abedi–Caticha §4, Eqs. 24–26): smeared normal `H` (lapse)
and tangential `P` (shift) deformation generators in a ring `R`, with the commutator bracket `collisionStar`
satisfying the Dirac algebra — tangential closes on the vector-field Lie bracket, the normal transforms as a
scalar, and two normals close on a metric-dependent tangential deformation. -/
structure DHKTAlgebra (R : Type*) [Ring R] where
  /-- the normal (Hamiltonian) generator smeared by a lapse function. -/
  H : (ℝ → ℝ) → R
  /-- the tangential (momentum) generator smeared by a shift vector. -/
  P : (ℝ → ℝ) → R
  /-- the vector-field Lie bracket `[v,w]` of two shifts. -/
  lie : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  /-- the Lie derivative `L_v N` of the lapse along a shift. -/
  lieDeriv : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  /-- the metric-dependent tangential structure `𝔤(N∇M − M∇N)` of the normal–normal bracket. -/
  metricBracket : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  /-- **Eq. 26**: tangential deformations close on the vector-field Lie algebra. -/
  pp : ∀ v w, collisionStar (P v) (P w) = P (lie v w)
  /-- **Eq. 25**: the normal generator transforms as a scalar under tangential deformations. -/
  ph : ∀ v N, collisionStar (P v) (H N) = H (lieDeriv v N)
  /-- **Eq. 24**: two normal deformations close on a metric-dependent tangential deformation. -/
  hh : ∀ N M, collisionStar (H N) (H M) = P (metricBracket N M)

/-! ## §B — antisymmetry of the brackets -/

/-- **[The tangential bracket is antisymmetric] `P([v,w]) = −P([w,v])`.** From the antisymmetry of the commutator,
the vector-field Lie bracket represented by the momentum constraints is antisymmetric — the Lie-algebra property
of the tangential deformations (Eq. 26). -/
theorem momentum_bracket_antisym (D : DHKTAlgebra R) (v w : ℝ → ℝ) :
    D.P (D.lie v w) = -D.P (D.lie w v) := by
  rw [← D.pp v w, collisionStar_antisymm, D.pp w v]

/-- **[The normal–normal bracket is antisymmetric] `P(𝔤(N,M)) = −P(𝔤(M,N))`.** The metric-dependent tangential
deformation produced by two normal deformations is antisymmetric in the lapses — from the commutator antisymmetry
(Eq. 24). -/
theorem hamiltonian_bracket_antisym (D : DHKTAlgebra R) (N M : ℝ → ℝ) :
    D.P (D.metricBracket N M) = -D.P (D.metricBracket M N) := by
  rw [← D.hh N M, collisionStar_antisymm, D.hh M N]

/-! ## §C — the Jacobi identity (path independence) -/

/-- **[The deformation generators satisfy the Jacobi identity] `[a,[b,c]] + [b,[c,a]] + [c,[a,b]] = 0`.** The
commutator bracket of any generators obeys Jacobi — the algebraic closure of the DHKT algebra that is the
foliation-invariance / path-independence consistency requirement of §5 (two ways of composing three deformations
agree). -/
theorem dhkt_jacobi (a b c : R) :
    collisionStar a (collisionStar b c) + collisionStar b (collisionStar c a)
      + collisionStar c (collisionStar a b) = 0 := by
  unfold collisionStar; noncomm_ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HypersurfaceDeformationDHKTAlgebra

end
