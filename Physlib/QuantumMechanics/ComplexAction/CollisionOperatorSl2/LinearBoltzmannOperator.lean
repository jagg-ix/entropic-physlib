/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel

/-!
# The linear Boltzmann collision operator: full `*`-calculus and generator algebra (Saveliev 1996)

Full algebraic formalization of the linear Boltzmann collision operator of *V. Saveliev, "A temperature
and mass dependence of the linear Boltzmann collision operator from group theory point of view,"
J. Math. Phys. 37 (1996) 6139*. The `*`-map core (`collisionStar` = `ad`, `collisionDoubleStar`) and the
modular-flow link are in `CollisionOperatorSl2.CollisionModular`; this file completes the operator's algebra:

* **(Eq. 18–19) the `*` map is a Lie-algebra homomorphism** `[ad_a, ad_b] = ad_[a,b]` — the Jacobi
  identity for the collision bracket (`collisionStar_ad_hom`), plus the left/right Leibniz rules; this is
  the algebraic engine of the whole `*`-calculus.
* **(§III, mass dependence) the canonical pair and the quadratic generators' Lie algebra.** With the
  canonical commutation `[∇, v] = 1`, the quadratics `∇²`, `∇v`, `v²` (whose `*`-maps are the generators
  `Q₁, M, Q₃` of Saveliev's algebra, Eq. 32) close into the `sl(2)`-type oscillator algebra
  `[∇², ∇v] = 2∇²`, `[∇v, v²] = 2v²`, `[∇², v²] = 4∇v − 2`, all *derived* from `[∇, v] = 1`.
* **(§IV, Eq. 29–31) energy conservation** `v²∗ χ = 0` — the collision kernel `χ` commutes with `v²`
  (`energyConserving_iff_commute`); for constant collision frequency also `∇²∗ χ = 0` (Eq. 31).
* **the temperature generator** `(ad_∇)² = ∇∗∇∗` (Eq. 16) and the **mass generator** `(∇v)∗ = ad_{∇v}`
  (Eq. 24), the infinitesimal generators of Saveliev's temperature and mass semigroups.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

variable {R : Type*} [Ring R]


/-- **Left Leibniz rule** for the star map: `[a·b, c] = a·[b,c] + [a,c]·b` — `ad` differentiates the left
factor (companion to `collisionStar_leibniz`, the right-factor rule). -/
lemma collisionStar_leibniz_left (a b c : R) :
    collisionStar (a * b) c = a * collisionStar b c + collisionStar a c * b := by
  unfold collisionStar; noncomm_ring

/-- **[Saveliev Eq. 19] The star map is a Lie-algebra homomorphism** `[ad_a, ad_b] = ad_[a,b]` — the
Jacobi identity for the collision bracket. Concretely `a∗(b∗c) − b∗(a∗c) = (a∗b)∗c`: the commutator of two
star maps is the star map of their bracket. This is the algebraic foundation of Saveliev's `*`-calculus
(`â∗b̂∗ − b̂∗â∗ = [â,b̂]∗`). -/
lemma collisionStar_ad_hom (a b c : R) :
    collisionStar a (collisionStar b c) - collisionStar b (collisionStar a c)
      = collisionStar (collisionStar a b) c := by
  unfold collisionStar; noncomm_ring

/-- **The Jacobi identity** in cyclic form: `[a,[b,c]] + [b,[c,a]] + [c,[a,b]] = 0`. -/
lemma collisionStar_jacobi (a b c : R) :
    collisionStar a (collisionStar b c) + collisionStar b (collisionStar c a)
      + collisionStar c (collisionStar a b) = 0 := by
  unfold collisionStar; noncomm_ring


variable (del vel : R)

/-- **`[∇v, v] = v`** — from `[∇, v] = 1` (left Leibniz: `[∇v,v] = ∇[v,v] + [∇,v]v = v`). -/
lemma collisionStar_delVel_vel (h : collisionStar del vel = 1) :
    collisionStar (del * vel) vel = vel := by
  simp only [collisionStar_leibniz_left, collisionStar_self, h]; noncomm_ring

/-- **`[∇v, ∇] = −∇`** — from `[∇, v] = 1` (left Leibniz: `[∇v,∇] = ∇[v,∇] + [∇,∇]v = −∇`). Together with
`[∇v, v] = v`, this exhibits the mass generator `M = ∇v∗ = ad_{∇v}` as the **squeeze (dilation) generator**
acting on the canonical pair: `∇ ↦ −∇`, `v ↦ +v` (the `sl(2)` Cartan), whose exponential is a Bogoliubov
transformation. -/
lemma collisionStar_delVel_del (h : collisionStar del vel = 1) :
    collisionStar (del * vel) del = -del := by
  have hvd : collisionStar vel del = -1 := by
    have e : collisionStar vel del = -collisionStar del vel := by unfold collisionStar; noncomm_ring
    rw [e, h]
  rw [collisionStar_leibniz_left, collisionStar_self, hvd]; noncomm_ring

/-- **`[∇², v] = 2∇`** — from `[∇, v] = 1` (left Leibniz: `[∇²,v] = ∇[∇,v] + [∇,v]∇ = 2∇`). -/
lemma collisionStar_delSq_vel (h : collisionStar del vel = 1) :
    collisionStar (del * del) vel = 2 * del := by
  simp only [collisionStar_leibniz_left, h]; noncomm_ring

/-- **`[∇, v²] = 2v`** — from `[∇, v] = 1` (right Leibniz). -/
lemma collisionStar_del_velSq (h : collisionStar del vel = 1) :
    collisionStar del (vel * vel) = 2 * vel := by
  simp only [collisionStar_leibniz, h]; noncomm_ring

/-- **`[∇², v] = 0` is false; `∇²` commutes with `∇`: `[∇², ∇] = 0`.** -/
lemma collisionStar_delSq_del : collisionStar (del * del) del = 0 := by
  unfold collisionStar; noncomm_ring

/-- **[sl(2) relation] `[∇², ∇v] = 2∇²`** — derived from `[∇, v] = 1`. The quadratic generators close. -/
lemma collisionStar_delSq_delVel (h : collisionStar del vel = 1) :
    collisionStar (del * del) (del * vel) = 2 * (del * del) := by
  rw [collisionStar_leibniz (del * del) del vel, collisionStar_delSq_del del,
    collisionStar_delSq_vel del vel h]
  noncomm_ring

/-- **[sl(2) relation] `[∇v, v²] = 2v²`** — derived from `[∇, v] = 1`. -/
lemma collisionStar_delVel_velSq (h : collisionStar del vel = 1) :
    collisionStar (del * vel) (vel * vel) = 2 * (vel * vel) := by
  simp only [collisionStar_leibniz, collisionStar_delVel_vel del vel h]; noncomm_ring

/-- **[sl(2) relation] `[∇², v²] = 4∇v − 2`** — the closing relation of the quadratic generators, derived
from `[∇, v] = 1`. (The `−2` is the central term from `v∇ = ∇v − 1`.) -/
lemma collisionStar_delSq_velSq (h : collisionStar del vel = 1) :
    collisionStar (del * del) (vel * vel) = 4 * (del * vel) - 2 := by
  have key : collisionStar (del * del) vel = 2 * del := collisionStar_delSq_vel del vel h
  have h2 : del * vel - vel * del = 1 := h
  rw [collisionStar_leibniz (del * del) vel vel, key, ← sub_eq_zero]
  have hgap : 2 * del * vel + vel * (2 * del) - (4 * (del * vel) - 2)
      = -2 * (del * vel - vel * del) + 2 := by noncomm_ring
  rw [hgap, h2]; noncomm_ring


/-- **[Saveliev Eq. 29] Energy conservation**: the collision kernel `χ` satisfies `v²∗ χ = 0` — for
scattering on an infinitely heavy center the velocity squared is invariant, so `χ` commutes with `v²`. -/
def EnergyConserving (vsq chi : R) : Prop := collisionStar vsq chi = 0

/-- **Energy conservation ⟺ `χ` commutes with `v²`.** -/
lemma energyConserving_iff_commute (vsq chi : R) :
    EnergyConserving vsq chi ↔ vsq * chi = chi * vsq := by
  unfold EnergyConserving collisionStar; rw [sub_eq_zero]

/-- **The energy-conservation generator `v²∗` annihilates `v²`** (`v²` is its own invariant). -/
lemma energyConserving_self (vsq : R) : EnergyConserving vsq vsq := collisionStar_self vsq

/-- **[Saveliev Eq. 30] The collision kernel `χ` is stationary under the energy-conservation flow.** Since
the generator annihilates `χ` (`v²∗ χ = 0`, Eq. 29), every positive power of `v²∗` annihilates it,
`(v²∗)ⁿ χ = 0` for `n ≥ 1`. Hence the one-parameter flow `e^{α v²∗}` it generates acts as the identity on
`χ` — `χ` is a *stationary object* with respect to the group generated by `v²∗`, `e^{α v²∗} χ = χ`. The
same statement with the generator `∇²∗` gives the constant-frequency stationarity (Eq. 31). -/
lemma energyConserving_stationary {vsq chi : R} (h : EnergyConserving vsq chi)
    {n : ℕ} (hn : 1 ≤ n) : (collisionStar vsq)^[n] chi = 0 := by
  have h' : collisionStar vsq chi = 0 := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply, h']
  exact Function.iterate_fixed (by simp [CollisionOperatorSl2.CollisionModular.collisionStar]) m

/-- **[Saveliev Eq. 31] Constant-collision-frequency conservation**: for `ν = const` (`χ = χ(μ)`) the
kernel also satisfies `∇²∗ χ = 0`, i.e. `χ` commutes with `∇²` as well. -/
lemma constFrequency_iff_commute (delsq chi : R) :
    EnergyConserving delsq chi ↔ delsq * chi = chi * delsq := by
  unfold EnergyConserving collisionStar; rw [sub_eq_zero]


/-- **[Saveliev Eq. 16] The temperature generator** `(ad_∇)² = ∇∗∇∗` — the double star map generating the
temperature semigroup `exp((kT/2m)∇∗∇∗)` of the collision operator. -/
def temperatureGenerator (del x : R) : R := collisionDoubleStar del x

/-- **[Saveliev Eq. 24] The mass generator** `(∇v)∗ = ad_{∇v}` — the star map of `∇v` generating the mass
semigroup `exp(ln(1+m)·(∇v)∗)` of the collision operator. -/
def massGenerator (del vel x : R) : R := collisionStar (del * vel) x

/-- The temperature generator is the iterated star map: `temperatureGenerator a x = a∗(a∗x)`. -/
lemma temperatureGenerator_eq (del x : R) :
    temperatureGenerator del x = collisionStar del (collisionStar del x) := rfl

/-- The mass generator annihilates the velocity at the canonical point: `(∇v)∗ v = v`
(`collisionStar_delVel_vel`) — the mass flow shifts `v` consistently with `[∇, v] = 1`. -/
lemma massGenerator_vel (h : collisionStar del vel = 1) :
    massGenerator del vel vel = vel :=
  collisionStar_delVel_vel del vel h

end Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator

end
