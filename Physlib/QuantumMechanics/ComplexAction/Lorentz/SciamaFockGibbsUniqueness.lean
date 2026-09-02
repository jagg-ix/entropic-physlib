/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

/-!
# Uniqueness of the Sciama thermal Gibbs state: the equilibrium is unique

The irreversible-equilibrium uniqueness mechanism of the LDDL one-level channel
(`OpenSystems.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt` /
`oneLevelChannel_fixedPoint_unique_all`) says a strictly-relative-entropy-contracting channel has a *unique*
fixed point.  That is a finite-dimensional (qubit) statement; here it is carried to the
**infinite-dimensional Sciama Fock oscillator** by its detailed-balance form: the Gibbs distribution is the
*only* normalized distribution on the number states whose Boltzmann ratio is `e^{−βE}`.

* `detailedBalance_pow` — any sequence with a constant ratio is a geometric sequence, `qₙ = rⁿ·q₀`.
* `thermalProbability_boltzmann_step` — the Gibbs distribution satisfies detailed balance,
  `p_{n+1} = e^{−βE}·pₙ` (non-vacuity: the equilibrium is itself a fixed point of the balance condition).
* `thermalProbability_unique` — **any** normalized `q : ℕ → ℝ` obeying detailed balance `q_{n+1} = e^{−βE}·qₙ`
  equals `thermalProbability β E`: the Sciama thermal Gibbs state is the *unique* detailed-balance equilibrium.

This is the infinite-dimensional complement of the one-level channel uniqueness: on the qubit the equilibrium
is pinned by a strictly contracting relative entropy; on the Fock oscillator it is pinned by detailed balance
plus normalization (both are the statement that the Gibbs state is the unique stationary state of the
irreversible relaxation).

Honest scope: the detailed-balance uniqueness of the c-number Gibbs distribution.  The full operator-level
statement that `ρ = e^{−βH}/Z` is the unique KMS / stationary state of a Fock-space Lindbladian is
contextualized (its qubit instance is `OneLevelChannelStrictArrow`), not built here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockGibbsUniqueness

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

/-- **[Detailed balance ⟹ geometric] `qₙ = rⁿ·q₀`.**  A sequence whose successive ratio is the constant `r`
is the geometric sequence with that ratio. -/
theorem detailedBalance_pow (r : ℝ) (q : ℕ → ℝ) (hq : ∀ n, q (n + 1) = r * q n) (n : ℕ) :
    q n = r ^ n * q 0 := by
  induction n with
  | zero => simp
  | succ k ih => rw [hq, ih]; ring

/-- **[Gibbs satisfies detailed balance] `p_{n+1} = e^{−βE}·pₙ`.**  The Sciama Gibbs distribution is a fixed
point of the Boltzmann balance condition — the equilibrium the uniqueness theorem singles out. -/
theorem thermalProbability_boltzmann_step (β E : ℝ) (n : ℕ) :
    thermalProbability β E (n + 1) = Real.exp (-(β * E)) * thermalProbability β E n := by
  rw [thermalProbability, thermalProbability, pow_succ]
  ring

/-- **[Uniqueness of the thermal equilibrium] the Gibbs state is the only detailed-balance distribution.**
Any normalized `q : ℕ → ℝ` with Boltzmann ratio `e^{−βE}` equals `thermalProbability β E`: the Sciama thermal
Gibbs state is the *unique* stationary state of the detailed-balance relaxation. -/
theorem thermalProbability_unique (β E : ℝ) (h : 0 < β * E) (q : ℕ → ℝ)
    (hdb : ∀ n, q (n + 1) = Real.exp (-(β * E)) * q n)
    (hnorm : ∑' n, q n = 1) : q = thermalProbability β E := by
  have hr0 : 0 < Real.exp (-(β * E)) := Real.exp_pos _
  have hr1 : Real.exp (-(β * E)) < 1 := exp_neg_lt_one β E h
  have hdne : (1 : ℝ) - Real.exp (-(β * E)) ≠ 0 := by linarith
  have hpow : ∀ n, q n = Real.exp (-(β * E)) ^ n * q 0 := detailedBalance_pow _ q hdb
  rw [show q = (fun n => Real.exp (-(β * E)) ^ n * q 0) from funext hpow, tsum_mul_right,
    tsum_geometric_of_lt_one hr0.le hr1] at hnorm
  have hq0 : q 0 = 1 - Real.exp (-(β * E)) := by
    field_simp at hnorm
    linarith
  funext n
  rw [hpow n, hq0, thermalProbability]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockGibbsUniqueness

end
