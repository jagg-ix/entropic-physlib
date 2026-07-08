/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularGroup
public import Mathlib.Tactic.NoncommRing

/-!
# Saveliev's linear Boltzmann collision operator and the modular flow

This file formalizes the algebraic core of **Vladimir Saveliev's linear Boltzmann collision
operator** (*A temperature and mass dependence of the linear Boltzmann collision operator from
group theory point of view*, J. Math. Phys. 37 (1996) 6139 — the same paper whose
temperature/mass *semigroup* is formalized in `StatisticalMechanics.BoltzmannThermalOscillator`), and proves
its operator is **linked to the Tomita–Takesaki modular flow**
(`QuantumMechanics.FiniteTarget.ModularGroupData`).

## Saveliev's "star map" `â*` (the collision operator's building block)

Saveliev (Eq. 18) builds the collision operator from the **star map**

  `â* : b ↦ [â, b] = â·b − b·â`,

i.e. the **adjoint action** / inner derivation `ad_â`. The temperature generator of the
collision operator (Eqs. 16, 20) is the *double* star map `∇*∇* = ad_∇ ∘ ad_∇ = [∇,[∇,·]]`,
with the collision operator `Î = exp((kT/2m)∇*∇*)·Ĵ`. Here:

* `collisionStar a b = a·b − b·a` — the star map `â*` (Eq. 18); a derivation
  (`collisionStar_leibniz`), antisymmetric (`collisionStar_antisymm`), self-annihilating
  (`collisionStar_self`).
* `collisionDoubleStar a b = [a,[a,b]]` — the collision operator's temperature generator
  `∇*∇*` (Eq. 16).

## The link to the modular flow (Tomita–Takesaki)

The modular automorphism group `σ_t(a) = Δ^{it} a Δ^{-it} = u(t)·a·u(-t)`
(`ModularGroupData.ofGenerator H_θ`, `u(t) = exp(it H_θ)`) is the exponentiated **adjoint
action of the modular Hamiltonian** `H_θ` — the same star-map structure Saveliev uses. The
operator link is exact:

* `modularFlow_preserves_collisionStar` — **`σ_t([a,b]) = [σ_t a, σ_t b]`**: the modular flow is
  an automorphism of Saveliev's star map (the collision-operator bracket is modular-covariant).
* `modularFlow_preserves_collisionDoubleStar` — likewise for the collision operator's
  temperature generator `∇*∇*`: Saveliev's collision-operator generator is preserved by the
  modular flow.
* `modularFlow_fixes_generator` — **`σ_t(H_θ) = H_θ`**: the modular Hamiltonian is invariant
  under its own flow (KMS stationarity), i.e. `[H_θ, ·]` (the star map of `H_θ`) annihilates
  `H_θ` (`collisionStar_self`). This is the generator that, integrated, is the modular flow.

So Saveliev's collision-operator star map `â*` and the Tomita–Takesaki modular generator are the
same object — the adjoint action — and the modular flow is the one-parameter automorphism it
generates. Via Connes–Rovelli thermal time the modular flow *is* the temperature/thermal flow
(`QuantumInertialFrame.kmsThermalRate`), matching Saveliev's temperature semigroup
`exp((kT/2m)∇*∇*)` (`StatisticalMechanics.BoltzmannThermalOscillator.heatMode`).

## References

* V. Saveliev, J. Math. Phys. 37 (1996) 6139, Eqs. 16, 18, 20 (collision operator, star map).
* M. Takesaki, LNM 128 (1970) (Tomita–Takesaki modular theory); Connes–Rovelli 1994 (thermal
  time). `QuantumInertialFrameModularGroup`, `StatisticalMechanics.BoltzmannThermalOscillator` (this development).

-/

set_option autoImplicit false

@[expose] public section

open QuantumMechanics.FiniteTarget

namespace Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

/-! ## §A — Saveliev's collision-operator star map `â*` (Eq. 18) -/

variable {R : Type*} [Ring R]

/-- **Saveliev's star map** `â* : b ↦ [â, b] = â·b − b·â` (Eq. 18) — the adjoint action
`ad_â`, from which the linear Boltzmann collision operator is built. -/
def collisionStar (a b : R) : R := a * b - b * a

/-- `â*` annihilates `â`: `[a, a] = 0`. -/
@[simp] theorem collisionStar_self (a : R) : collisionStar a a = 0 := by
  unfold collisionStar; rw [sub_self]

/-- **`â*` is a derivation** (Leibniz rule): `[a, b·c] = [a,b]·c + b·[a,c]`. -/
theorem collisionStar_leibniz (a b c : R) :
    collisionStar a (b * c) = collisionStar a b * c + b * collisionStar a c := by
  unfold collisionStar; noncomm_ring

/-- **`â*` is antisymmetric**: `[a, b] = −[b, a]`. -/
theorem collisionStar_antisymm (a b : R) :
    collisionStar a b = -collisionStar b a := by
  unfold collisionStar; noncomm_ring

/-- **Conjugation by a unit preserves the star map**: `u·[a,b]·v = [u·a·v, u·b·v]` when
`v·u = 1`. The algebraic heart of modular covariance. -/
theorem conj_collisionStar {u v : R} (huv : v * u = 1) (a b : R) :
    u * collisionStar a b * v = collisionStar (u * a * v) (u * b * v) := by
  unfold collisionStar
  have hR : (u * a * v) * (u * b * v) - (u * b * v) * (u * a * v)
      = u * a * (v * u) * b * v - u * b * (v * u) * a * v := by noncomm_ring
  rw [hR, huv]
  noncomm_ring

/-- **The collision operator's temperature generator** `∇*∇* = [a,[a,·]]` (Saveliev Eq. 16) —
the double star map, generating the temperature semigroup `exp((kT/2m)∇*∇*)` (Eq. 20). -/
def collisionDoubleStar (a b : R) : R := collisionStar a (collisionStar a b)

/-! ## §B — the modular flow is a star-map automorphism (the operator link) -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- **The modular flow preserves Saveliev's star map**: `σ_t([a,b]) = [σ_t a, σ_t b]`. The
Tomita–Takesaki modular automorphism is an automorphism of the collision-operator bracket. -/
theorem modularFlow_preserves_collisionStar (H_θ : H →L[ℂ] H) (t : ℝ) (a b : H →L[ℂ] H) :
    (ModularGroupData.ofGenerator H_θ).σ t (collisionStar a b)
      = collisionStar ((ModularGroupData.ofGenerator H_θ).σ t a)
          ((ModularGroupData.ofGenerator H_θ).σ t b) := by
  show unitaryFlow H_θ t * collisionStar a b * unitaryFlow H_θ (-t)
      = collisionStar (unitaryFlow H_θ t * a * unitaryFlow H_θ (-t))
          (unitaryFlow H_θ t * b * unitaryFlow H_θ (-t))
  exact conj_collisionStar (unitaryFlow_neg_mul H_θ t) a b

/-- **The modular flow preserves the collision operator's temperature generator** `∇*∇*`:
`σ_t([a,[a,b]]) = [σ_t a, [σ_t a, σ_t b]]`. Saveliev's collision-operator generator is
modular-covariant. -/
theorem modularFlow_preserves_collisionDoubleStar (H_θ : H →L[ℂ] H) (t : ℝ) (a b : H →L[ℂ] H) :
    (ModularGroupData.ofGenerator H_θ).σ t (collisionDoubleStar a b)
      = collisionDoubleStar ((ModularGroupData.ofGenerator H_θ).σ t a)
          ((ModularGroupData.ofGenerator H_θ).σ t b) := by
  unfold collisionDoubleStar
  rw [modularFlow_preserves_collisionStar H_θ t a (collisionStar a b),
    modularFlow_preserves_collisionStar H_θ t a b]

/-- **The modular Hamiltonian is invariant under its own modular flow**: `σ_t(H_θ) = H_θ` (KMS
stationarity). Equivalently `[H_θ, ·]` (the star map of `H_θ`) is the flow's generator, with
`collisionStar H_θ H_θ = 0`. -/
theorem modularFlow_fixes_generator (H_θ : H →L[ℂ] H) (t : ℝ) :
    (ModularGroupData.ofGenerator H_θ).σ t H_θ = H_θ := by
  show unitaryFlow H_θ t * H_θ * unitaryFlow H_θ (-t) = H_θ
  have hc : Commute (unitaryFlow H_θ t) H_θ := by
    unfold unitaryFlow
    exact ((Commute.refl H_θ).smul_left _).exp_left
  rw [hc.eq, mul_assoc, unitaryFlow_mul_neg, mul_one]

end Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

end
