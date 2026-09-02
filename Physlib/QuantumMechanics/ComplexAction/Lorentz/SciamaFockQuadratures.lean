/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockAdjointness

/-!
# The quadratures `X, P` and the canonical commutator

The position/momentum **quadratures** of the single mode,

`X = (a + a†)/√2`,  `P = (a − a†)/(i√2)`,

the phase-space coordinates on which the clock hand of `SciamaFockCoherentEvolution` rotates.  Their canonical
commutator `[X, P] = i` (units `ℏ = 1`) is an immediate consequence of the CCR `[a, a†] = 1`
(`ccr_commutator`): expanding, `[X, P] = -i/2 · [a+a†, a−a†] = -i/2 · (−2[a,a†]) = i[a,a†] = i`.

* `quadX`, `quadP` — the quadrature operators on the algebraic Fock space.
* `ccr_commutator` — the CCR in commutator form `⁅a, a†⁆ = 1`.

Honest scope: the quadrature operators and the CCR in Lie-commutator form; the position/momentum commutator
`[X, P] = i` follows by ℂ-bilinearity of the commutator (the Robertson uncertainty `ΔXΔP ≥ ½` then follows by
Cauchy–Schwarz).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockQuadratures

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace

/-- **The position quadrature** `X = (a + a†)/√2`. -/
def quadX : Module.End ℂ (ℕ →₀ ℂ) := (Real.sqrt 2 : ℂ)⁻¹ • (annihilationOp + creationOp)

/-- **The momentum quadrature** `P = (a − a†)/(i√2) = −i(a − a†)/√2`. -/
def quadP : Module.End ℂ (ℕ →₀ ℂ) :=
  ((-Complex.I) * (Real.sqrt 2 : ℂ)⁻¹) • (annihilationOp - creationOp)

/-- **[CCR, commutator form] `⁅a, a†⁆ = a a† − a† a = 1`.**  The canonical commutation relation as a Lie
bracket — the seed of `[X, P] = i` and of the uncertainty relation `ΔXΔP ≥ ½`. -/
theorem ccr_commutator : ⁅annihilationOp, creationOp⁆ = (1 : Module.End ℂ (ℕ →₀ ℂ)) := ccr

/-- The CCR in ring form: `a a† − a† a = 1`. -/
theorem ccr_ring : annihilationOp * creationOp - creationOp * annihilationOp
    = (1 : Module.End ℂ (ℕ →₀ ℂ)) := ccr

/-- **[Abstract `[X, P] = i`]** In *any* `ℂ`-algebra, two elements `a, b` with `[a, b] = 1` yield quadratures
`X = (a+b)/√2`, `P = (a−b)/(i√2)` obeying `[X, P] = i`.  Proved generically — where the standard ring/module
rewrites work — so it instantiates at `Module.End ℂ (ℕ →₀ ℂ)` (whose own instances defeat those rewrites)
purely by definitional unfolding. -/
theorem xp_commutator_of_ccr {R : Type*} [Ring R] [Algebra ℂ R] (a b : R)
    (hab : a * b - b * a = 1) :
    ((Real.sqrt 2 : ℂ)⁻¹ • (a + b)) * (((-Complex.I) * (Real.sqrt 2 : ℂ)⁻¹) • (a - b))
      - (((-Complex.I) * (Real.sqrt 2 : ℂ)⁻¹) • (a - b)) * ((Real.sqrt 2 : ℂ)⁻¹ • (a + b))
      = Complex.I • (1 : R) := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  have hs2sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hop : (a + b) * (a - b) - (a - b) * (a + b) = (-2 : ℂ) • (a * b - b * a) := by
    have h1 : (a + b) * (a - b) - (a - b) * (a + b) = -(a * b - b * a) - (a * b - b * a) := by
      noncomm_ring
    rw [h1]; module
  have hsc : ((Real.sqrt 2 : ℂ)⁻¹ * ((-Complex.I) * (Real.sqrt 2 : ℂ)⁻¹)) * (-2) = Complex.I := by
    rw [show ((Real.sqrt 2 : ℂ)⁻¹ * ((-Complex.I) * (Real.sqrt 2 : ℂ)⁻¹)) * (-2)
        = (-Complex.I) * (-2) * ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) from by ring,
      ← mul_inv, hs2sq]
    ring
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul,
    mul_comm ((-Complex.I) * (Real.sqrt 2 : ℂ)⁻¹) ((Real.sqrt 2 : ℂ)⁻¹), ← smul_sub, hop, hab,
    smul_smul, hsc]

/-- **[Canonical commutation relation] `[X, P] = i`.**  The quadratures obey `XP − PX = i·1` — the Heisenberg
canonical commutator, seed of the uncertainty relation `ΔXΔP ≥ ½`.  Instantiates the abstract
`xp_commutator_of_ccr` at the Fock CCR. -/
theorem quad_commutator :
    quadX * quadP - quadP * quadX = Complex.I • (1 : Module.End ℂ (ℕ →₀ ℂ)) :=
  xp_commutator_of_ccr annihilationOp creationOp ccr_ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockQuadratures

end
