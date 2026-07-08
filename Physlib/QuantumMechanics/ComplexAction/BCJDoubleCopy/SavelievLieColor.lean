/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator

/-!
# The BCJ color Jacobi from the Lie commutator: the gauge algebra and the `SL(2)` cover

Links `BCJDoubleCopy.ColorKinematicsDoubleCopy` to the Lie-theory of the covering groups (§7 `SL(2,ℂ)`, Appendix B
Pin) through the **Jacobi identity**, using the Saveliev linear-Boltzmann collision bracket
(`CollisionOperatorSl2.LinearBoltzmannOperator`, `collisionStar = ad`). The BCJ **color factors** are built from the
gauge Lie algebra's structure constants, and their **color Jacobi** `c_s + c_t + c_u = 0` is *literally* the
Lie-algebra Jacobi identity — the same identity that `collisionStar_jacobi` proves for the adjoint
(commutator) action `ad_a(b) = [a,b]`.

So the two halves of BCJ color–kinematics duality acquire genuine sources:

* the **color** Jacobi `c_s + c_t + c_u = 0` ← the Lie-algebra Jacobi of the gauge adjoint
  (`CollisionOperatorSl2.LinearBoltzmannOperator.collisionStar_jacobi`);
* the **kinematic** Jacobi `n_s + n_t + n_u = 0` ← the Maxwell–Faraday Bianchi identity
  (`PTSymmetricQFT.MaxwellFaraday.faraday_bianchi`, already used in `faradayBCJDuality`).

* **§A — the color Jacobi from the Lie commutator** (`savelievColorJacobi`). A color functional `φ` applied
  to the three cyclic adjoint terms `ad_a(ad_b c)` sums to zero — the scalar color Jacobi from the gauge
  Lie algebra's adjoint action.
* **§B — the full duality** (`savelievFaradayBCJDuality`). A `BCJColorKinematicsDuality` with color factors
  from the Saveliev/Lie commutator and kinematic numerators from the Maxwell Bianchi — both Jacobi
  identities proved from genuine repo theorems.
* **§C — the `sl(2)` of the `SL(2,ℂ)` cover** (`sl2BCJDuality`, `sl2BCJ_color_s`). Specializing the color
  Lie algebra to the Saveliev quadratic generators `∇², ∇v, v²`, which close into `sl(2) = Lie(SL(2,ℂ))`
  (the §7 covering group) under `[∇, v] = 1`. The `s`-channel color factor is computed through the `sl(2)`
  relations `[∇v, v²] = 2v²` and `[∇², v²] = 4∇v − 2` (`collisionStar_delVel_velSq`,
  `collisionStar_delSq_velSq`).

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, arXiv:0805.3993 (color–kinematics duality; color Jacobi from
  the gauge structure constants).
* Repo dependencies: `BCJDoubleCopy.ColorKinematicsDoubleCopy` (`BCJColorKinematicsDuality`, `faradayBCJDuality`);
  `CollisionOperatorSl2.LinearBoltzmannOperator` (`collisionStar`, `collisionStar_jacobi`, the `sl(2)` relations);
  `PTSymmetricQFT.MaxwellFaraday.faraday_bianchi`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SavelievLieColor

open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-! ## §A — the color Jacobi from the Lie commutator -/

/-- **[BCJ color Jacobi = Lie Jacobi] The gauge adjoint gives the color Jacobi.** For a color functional
`φ : R →ₗ[ℝ] ℝ` on the gauge Lie algebra, the three cyclic adjoint terms `ad_a(ad_b c)` (the structure of a
BCJ color factor) sum to zero — `φ` of the Lie-algebra Jacobi `collisionStar_jacobi`. -/
theorem savelievColorJacobi (φ : R →ₗ[ℝ] ℝ) (a b c : R) :
    φ (collisionStar a (collisionStar b c)) + φ (collisionStar b (collisionStar c a))
      + φ (collisionStar c (collisionStar a b)) = 0 := by
  rw [← map_add, ← map_add, collisionStar_jacobi, map_zero]

/-! ## §B — the full color–kinematics duality -/

/-- **[Full BCJ duality from genuine sources]** A `BCJColorKinematicsDuality` whose **color** factors come
from the gauge Lie algebra's adjoint (`collisionStar`, with color functional `φ`) and whose **kinematic**
numerators are the three cyclic Maxwell terms. The color Jacobi is the Lie-algebra Jacobi
(`savelievColorJacobi`); the kinematic Jacobi is the Maxwell–Faraday Bianchi identity (`faraday_bianchi`).
The defining BCJ statement — "the numerators obey the same Jacobi as the color factors" — with both Jacobi
identities proved from the repo. -/
noncomputable def savelievFaradayBCJDuality (φ : R →ₗ[ℝ] ℝ) (a b c : R)
    (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) : BCJColorKinematicsDuality where
  c_s := φ (collisionStar a (collisionStar b c))
  c_t := φ (collisionStar b (collisionStar c a))
  c_u := φ (collisionStar c (collisionStar a b))
  n_s := k lam * faraday k A μ ν
  n_t := k μ * faraday k A ν lam
  n_u := k ν * faraday k A lam μ
  color_jacobi := savelievColorJacobi φ a b c
  kinematic_jacobi := faraday_bianchi k A lam μ ν

/-! ## §C — the `sl(2)` of the `SL(2,ℂ)` covering group -/

/-- **[Color from `sl(2) = Lie(SL(2,ℂ))`]** The BCJ duality with color factors built from the Saveliev
quadratic generators `∇², ∇v, v²` — which close into the `sl(2)` algebra of the §7 `SL(2,ℂ)` covering group
under the canonical relation `[∇, v] = 1`. -/
noncomputable def sl2BCJDuality (φ : R →ₗ[ℝ] ℝ) (del vel : R)
    (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) : BCJColorKinematicsDuality :=
  savelievFaradayBCJDuality φ (del * del) (del * vel) (vel * vel) k A lam μ ν

/-- **[`s`-channel color via the `sl(2)` relations] `c_s = φ(2(4∇v − 2))`.** Reducing the cyclic adjoint
color factor through the `sl(2)` relations `[∇v, v²] = 2v²` (`collisionStar_delVel_velSq`) and
`[∇², v²] = 4∇v − 2` (`collisionStar_delSq_velSq`) of the covering group's Lie algebra. -/
theorem sl2BCJ_color_s (φ : R →ₗ[ℝ] ℝ) (del vel : R) (h : collisionStar del vel = 1)
    (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    (sl2BCJDuality φ del vel k A lam μ ν).c_s = φ (2 * (4 * (del * vel) - 2)) := by
  show φ (collisionStar (del * del) (collisionStar (del * vel) (vel * vel))) = _
  rw [collisionStar_delVel_velSq del vel h,
    show collisionStar (del * del) (2 * (vel * vel)) = 2 * collisionStar (del * del) (vel * vel) from by
      unfold collisionStar; noncomm_ring,
    collisionStar_delSq_velSq del vel h]

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SavelievLieColor

end
