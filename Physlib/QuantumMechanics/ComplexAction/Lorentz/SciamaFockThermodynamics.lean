/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Thermodynamics of the Hartle–Hawking Gibbs state: entropy, energy, and the first law

The c-number Gibbs distribution `p_n = r^n(1−r)` (`r = e^{−βE}`) of `SciamaThermalDensityMatrix` is the
diagonal of the Hartle–Hawking thermal density matrix `ρ` restricted to the exterior region.  Because `ρ` is
diagonal in the number basis, its **von Neumann entropy** `S(ρ) = −Tr ρ ln ρ` is the Shannon entropy of the
Gibbs distribution, and the thermodynamics of the mode follows in closed form:

* `thermalEntropy_eq` — `S = −Σ_n p_n ln p_n = βE·n̄ − ln(1 − e^{−βE})` (`n̄ =` Bose–Einstein occupation).
* `thermalMeanEnergy_eq` — `U = Σ_n p_n·(nE) = E·n̄` (the mean energy is the occupation times the quantum).
* `thermalEntropy_eq_beta_energy_add_logZ` — **`S = βU + ln Z`**, the fundamental relation `S = β(U − F)` with
  free energy `F = −β⁻¹ ln Z`: entropy, energy, and the partition function of `SciamaThermalDensityMatrix`
  close into the first law.
* `thermalPurity_eq` — `Tr ρ² = Σ_n p_n² = (1 − e^{−βE})/(1 + e^{−βE})`, and `thermalPurity_lt_one` —
  `Tr ρ² < 1`: the thermal state is **mixed** (a proper density matrix, not a pure state), the hallmark of the
  Hawking/Unruh thermality.

This is the entropic-time program's thermal anchor: `S` is the **Boltzmann/Bekenstein entropy** of the Gibbs
state whose modular flow is the Connes–Rovelli thermal time of `SciamaFockCoherentEvolution` — the same
`β = 2π` KMS state whose mean occupation is Planckian (`thermal_mean_occupation`).  The first law
`S = βU + ln Z` is the statistical-mechanical shadow of the horizon first law `dU = T dS`.

Honest scope: the exact c-number thermodynamics of the diagonal Gibbs state (entropy, energy, first law,
purity); the operator `−Tr ρ ln ρ` coincides with `−Σ p_n ln p_n` because `ρ` is diagonal, which is
contextualized here rather than re-derived at the operator level.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermodynamics

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

/-- **The von Neumann entropy** of the diagonal Gibbs state, `S = −Σ_n p_n ln p_n`. -/
def thermalEntropy (β E : ℝ) : ℝ :=
  -∑' n : ℕ, thermalProbability β E n * Real.log (thermalProbability β E n)

/-- **The mean energy** `U = Σ_n p_n·(nE)` of the Gibbs state (level `n` carries energy `nE`). -/
def thermalMeanEnergy (β E : ℝ) : ℝ :=
  ∑' n : ℕ, thermalProbability β E n * ((n : ℝ) * E)

/-- **The purity** `Tr ρ² = Σ_n p_n²` of the Gibbs state. -/
def thermalPurity (β E : ℝ) : ℝ := ∑' n : ℕ, thermalProbability β E n ^ 2

/-- **[Von Neumann entropy] `S = −Σ_n p_n ln p_n = βE·n̄ − ln(1 − e^{−βE})`.**  The entropy of the
Hartle–Hawking Gibbs state in closed form; `n̄ = 1/(e^{βE}−1)` is the Bose–Einstein occupation. -/
theorem thermalEntropy_eq (β E : ℝ) (h : 0 < β * E) :
    thermalEntropy β E = β * E * boseEinstein β E - Real.log (1 - Real.exp (-(β * E))) := by
  have hr0 : 0 < Real.exp (-(β * E)) := Real.exp_pos _
  have hr1 : Real.exp (-(β * E)) < 1 := exp_neg_lt_one β E h
  have hdne : (1 : ℝ) - Real.exp (-(β * E)) ≠ 0 := by linarith
  have hrne : Real.exp (-(β * E)) ≠ 0 := ne_of_gt hr0
  have hnorm : ‖Real.exp (-(β * E))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0.le]; exact hr1
  have hsP : Summable (thermalProbability β E) := by
    unfold thermalProbability
    exact (summable_geometric_of_lt_one hr0.le hr1).mul_right _
  have hsNP : Summable (fun n : ℕ => (n : ℝ) * thermalProbability β E n) := by
    refine ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_right
      (1 - Real.exp (-(β * E)))).congr (fun n => ?_)
    rw [thermalProbability]; ring
  have hpt : ∀ n : ℕ, thermalProbability β E n * Real.log (thermalProbability β E n)
      = Real.log (Real.exp (-(β * E))) * ((n : ℝ) * thermalProbability β E n)
        + Real.log (1 - Real.exp (-(β * E))) * thermalProbability β E n := by
    intro n
    rw [show thermalProbability β E n = Real.exp (-(β * E)) ^ n * (1 - Real.exp (-(β * E))) from rfl,
      Real.log_mul (pow_ne_zero _ hrne) hdne, Real.log_pow]
    ring
  rw [thermalEntropy, tsum_congr hpt, (hsNP.mul_left _).tsum_add (hsP.mul_left _),
    tsum_mul_left, tsum_mul_left, thermal_mean_occupation β E h,
    thermalProbability_tsum_one β E h, Real.log_exp]
  ring

/-- **[Mean energy] `U = Σ_n p_n·(nE) = E·n̄`.**  The mean energy of the Gibbs state is the quantum `E` times
the Bose–Einstein occupation. -/
theorem thermalMeanEnergy_eq (β E : ℝ) (h : 0 < β * E) :
    thermalMeanEnergy β E = E * boseEinstein β E := by
  rw [thermalMeanEnergy, show (fun n : ℕ => thermalProbability β E n * ((n : ℝ) * E))
      = (fun n : ℕ => E * ((n : ℝ) * thermalProbability β E n)) from by funext n; ring,
    tsum_mul_left, thermal_mean_occupation β E h]

/-- **[First law] `S = βU + ln Z`.**  The entropy, mean energy, and partition function of the Gibbs state
close into the fundamental relation `S = β(U − F)` with free energy `F = −β⁻¹ ln Z` — the statistical shadow
of the horizon first law `dU = T dS`. -/
theorem thermalEntropy_eq_beta_energy_add_logZ (β E : ℝ) (h : 0 < β * E) :
    thermalEntropy β E
      = β * thermalMeanEnergy β E + Real.log (thermalPartitionFunction β E) := by
  rw [thermalEntropy_eq β E h, thermalMeanEnergy_eq β E h, thermalPartitionFunction, Real.log_inv]
  ring

/-- **[Purity] `Tr ρ² = Σ_n p_n² = (1 − e^{−βE})/(1 + e^{−βE})`.**  The purity of the Gibbs state in closed
form. -/
theorem thermalPurity_eq (β E : ℝ) (h : 0 < β * E) :
    thermalPurity β E
      = (1 - Real.exp (-(β * E))) / (1 + Real.exp (-(β * E))) := by
  have hr0 : 0 < Real.exp (-(β * E)) := Real.exp_pos _
  have hr1 : Real.exp (-(β * E)) < 1 := exp_neg_lt_one β E h
  have hr2 : Real.exp (-(β * E)) ^ 2 < 1 := by rw [pow_two]; nlinarith [hr0, hr1]
  have h1pr : (0 : ℝ) < 1 + Real.exp (-(β * E)) := by linarith
  have h1mr : (1 : ℝ) - Real.exp (-(β * E)) ≠ 0 := by linarith
  rw [thermalPurity, show (fun n : ℕ => thermalProbability β E n ^ 2)
      = (fun n : ℕ => (Real.exp (-(β * E)) ^ 2) ^ n * (1 - Real.exp (-(β * E))) ^ 2) from by
        funext n
        rw [thermalProbability, mul_pow, ← pow_mul, mul_comm n 2, pow_mul],
    tsum_mul_right, tsum_geometric_of_lt_one (by positivity) hr2,
    show (1 : ℝ) - Real.exp (-(β * E)) ^ 2
      = (1 - Real.exp (-(β * E))) * (1 + Real.exp (-(β * E))) from by ring]
  field_simp

/-- **[Mixed state] `Tr ρ² < 1`.**  The Hartle–Hawking Gibbs state is a *mixed* state — a genuine density
matrix, not a pure state — which is the signature of the Hawking/Unruh thermality. -/
theorem thermalPurity_lt_one (β E : ℝ) (h : 0 < β * E) : thermalPurity β E < 1 := by
  have hr0 : 0 < Real.exp (-(β * E)) := Real.exp_pos _
  have hr1 : Real.exp (-(β * E)) < 1 := exp_neg_lt_one β E h
  have h1pr : (0 : ℝ) < 1 + Real.exp (-(β * E)) := by linarith
  rw [thermalPurity_eq β E h, div_lt_one h1pr]
  linarith

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermodynamics

end
