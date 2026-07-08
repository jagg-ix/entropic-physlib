/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
public import Physlib.QuantumMechanics.ComplexAction.LienardMomentumDependentMass

/-!
# The isotonic Liénard ladder and Saveliev's collision `sl(2)`: a shared equispacing mechanism

Saveliev's linear Boltzmann collision operator is an `ad`-`*`-calculus: `collisionStar a b = ab − ba` is a
**derivation** in each slot (`collisionStar_leibniz`), and the quadratics `∇², ∇v, v²` of a canonical pair
`[∇,v] = collisionStar ∇ v = 1` close into the oscillator `sl(2)` (`LinearBoltzmannOperator`). The `η = −3/2`
Liénard oscillator (`LienardMomentumDependentMass`) is the isotonic system, whose spectrum-generating algebra is
the same `su(1,1) ≅ sl(2)` — and both have **equispaced** spectra for one and the same reason.

That reason is formalized here. Because `collisionStar H = ad_H` is a derivation, **ad-weights are additive under
products** (`collisionStar_weight_mul`): if `ad_H a = w_a·a` and `ad_H b = w_b·b` then `ad_H(ab) = (w_a+w_b)·ab`.
Hence a single weight-`w` raising element `a` builds an **arithmetic-progression ladder**
`ad_H(aⁿ) = (n·w)·aⁿ` (`collisionStar_weight_pow`) — an equispaced spectrum with spacing `w`. Both systems are
instances:

* **Boltzmann `sl(2)`** — with `H = ∇v` the Cartan and `v` the raising element (`ad_{∇v} v = v`, weight `1`), the
 ladder `vⁿ` includes the equispaced integer weights `n` (`collisionStar_sl2_ladder`); `v²` sits at weight `2`,
 recovering `collisionStar_delVel_velSq`.
* **Isotonic Liénard** — the energy levels `Ẽₙ = ½(ℓ+3/2)ω + n·ω` (`lienardEnergy_arithmetic`) are the same
 arithmetic progression, spacing `ω`, the `su(1,1)` ladder of the isotonic oscillator.

* **§A** — `collisionStar_one`, `collisionStar_weight_mul`, `collisionStar_weight_pow`,
 `collisionStar_ladder_spacing` (the derivation ⇒ additive-weight ⇒ equispaced-ladder mechanism).
* **§B** — `collisionStar_sl2_ladder` (Boltzmann instance).
* **§C** — `lienardEnergy_arithmetic` (Liénard/isotonic instance).

The mechanism (§A) and the Boltzmann instance (§B) are exact ring/`ad`-derivation identities;
the Liénard instance (§C) is the exact arithmetic-progression form of the paper's spectrum. This is a *structural*
link — the two systems share the `sl(2)` oscillator-ladder algebra and its equispacing mechanism; the Liénard
energies are **not** literally `collisionStar` of Boltzmann operators, but are the same abstract ad-weight ladder in
a different representation (the isotonic `su(1,1)`, whose Casimir is the `ℓ(ℓ+1)` of `lienard_ell_relation`).

## References

* V. Saveliev, *J. Math. Phys.* **37** (1996) 6139, §II–III; B. Bagchi, A. Ghose Choudhury, P. Guha,
 arXiv:1305.4566. Bridges `CollisionOperatorSl2.LinearBoltzmannOperator` and `LienardMomentumDependentMass`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
open Physlib.QuantumMechanics.ComplexAction.LienardMomentumDependentMass

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LienardIsotonicLadder

variable {R : Type*} [Ring R]

/-! ## §A — the derivation ⇒ additive-weight ⇒ equispaced-ladder mechanism -/

/-- **The identity has ad-weight zero** `ad_H 1 = 0` — a scalar commutes with everything. -/
theorem collisionStar_one (H : R) : collisionStar H 1 = 0 := by
  unfold collisionStar; simp

/-- **Ad-weights add under products** `ad_H a = w_a·a → ad_H b = w_b·b → ad_H(ab) = (w_a+w_b)·ab` — the
derivation (Leibniz) property of the collision bracket makes the weight a homomorphism to `(ℤ,+)`. -/
theorem collisionStar_weight_mul {H a b : R} {wa wb : ℤ}
    (ha : collisionStar H a = wa • a) (hb : collisionStar H b = wb • b) :
    collisionStar H (a * b) = (wa + wb) • (a * b) := by
  rw [collisionStar_leibniz, ha, hb, smul_mul_assoc, mul_smul_comm, ← add_smul]

/-- **A weight-`w` raising element builds an equispaced ladder** `ad_H(aⁿ) = (n·w)·a⁍` — iterating the raising
element multiplies its weight by `n`, giving an arithmetic progression of ad-weights (spacing `w`). -/
theorem collisionStar_weight_pow {H a : R} {w : ℤ} (ha : collisionStar H a = w • a) (n : ℕ) :
    collisionStar H (a ^ n) = ((n : ℤ) * w) • (a ^ n) := by
  induction n with
  | zero => simp [collisionStar_one]
  | succ n ih =>
    rw [pow_succ, collisionStar_weight_mul ih ha]
    congr 1
    push_cast; ring

/-- **The ladder spacing is constant** `(n+1)w − nw = w` — the equispacing of the ad-weight ladder. -/
theorem collisionStar_ladder_spacing (w : ℤ) (n : ℕ) :
    ((n + 1 : ℤ) * w) - ((n : ℤ) * w) = w := by ring

/-! ## §B — the Boltzmann `sl(2)` instance -/

/-- **The Boltzmann collision `sl(2)` ladder** `ad_{∇v}(vⁿ) = n·vⁿ` — with the canonical `[∇,v] = 1`, the velocity
`v` is the weight-`1` raising element of the Cartan `∇v`, so its powers include the equispaced integer weights `n`
(the harmonic ladder); `v²` at weight `2` is `collisionStar_delVel_velSq`. -/
theorem collisionStar_sl2_ladder (del vel : R) (h : collisionStar del vel = 1) (n : ℕ) :
    collisionStar (del * vel) (vel ^ n) = (n : ℤ) • (vel ^ n) := by
  have hw : collisionStar (del * vel) vel = (1 : ℤ) • vel := by
    rw [collisionStar_delVel_vel del vel h, one_smul]
  simpa using collisionStar_weight_pow hw n

/-! ## §C — the isotonic Liénard instance -/

/-- **The isotonic Liénard spectrum is an arithmetic progression** `Ẽₙ = ½(ℓ+3/2)ω + n·ω` — the same
equispaced ladder as the Boltzmann `sl(2)`, with spacing `ω`: the `su(1,1)` spectrum-generating algebra of the
momentum-dependent-mass isotonic oscillator is the collision `sl(2)` in its isotonic representation. -/
theorem lienardEnergy_arithmetic (n : ℕ) (ℓ ω : ℝ) :
    lienardEnergy n ℓ ω = (1 / 2) * (ℓ + 3 / 2) * ω + (n : ℝ) * ω := by
  unfold lienardEnergy; ring

end Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LienardIsotonicLadder
