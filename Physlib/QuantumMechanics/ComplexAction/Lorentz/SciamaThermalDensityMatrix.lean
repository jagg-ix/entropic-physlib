/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Sciama–Candelas–Deutsch §3 (alternative vacua): the Hartle–Hawking thermal density matrix

Section 3 shows that the alternative vacuum states (Boulware, Hartle–Hawking, Unruh) differ in their thermal
content, and that the Hartle–Hawking state `|H⟩` restricted to the exterior region I is a **thermal density
matrix** (Eq. 19):

`ρ_{2π/κ} = {Σ_m e^{−2π E_m/κ}}^{−1} Σ_m e^{−2π E_m/κ} |m,n⟩⟨m,n|`,

a Gibbs state at the Hawking temperature `κ/2π` (`β = 2π/κ`), with `⟨H|Ô|H⟩ = Tr(ρ Ô)` (Eq. 18).  Here the
c-number content of that Gibbs distribution is formalized: the Boltzmann weights, the partition function, its
normalization, and — the key link — that its **mean occupation is the Bose–Einstein `n(E)`**
(`SciamaFluctuationDissipation`), so the density-matrix and Bogoliubov routes to the thermality agree.

* `thermalWeight`, `thermalPartitionFunction`, `thermalProbability` — the Gibbs distribution `p_n = r^n(1−r)`.
* `thermalPartition_eq_tsum` — `Σ_n r^n = 1/(1−r)` (the partition function, `r = e^{−βE}`).
* `thermalProbability_tsum_one` — `Σ_n p_n = 1` (normalization / unit trace).
* `thermal_mean_occupation` — `Σ_n n·p_n = boseEinstein(β,E) = 1/(e^{βE}−1)` (the Gibbs mean is Planckian).
* `thermalProbability_detailedBalance` — `p_{n+1}/p_n = e^{−βE}` (the Boltzmann ratio).

Honest scope: the c-number Gibbs distribution and its Planckian mean; the Fock-space density operator (Eq. 19)
and the operator trace (Eq. 18) are contextualized, not built.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

/-- **The Boltzmann weight** `e^{−βE·n} = r^n` (`r = e^{−βE}`) for the `n`-th excited level. -/
def thermalWeight (β E : ℝ) (n : ℕ) : ℝ := Real.exp (-(β * E)) ^ n

/-- **The partition function** `Z = 1/(1 − e^{−βE})`. -/
def thermalPartitionFunction (β E : ℝ) : ℝ := (1 - Real.exp (-(β * E)))⁻¹

/-- **The Gibbs probability** `p_n = r^n(1 − r) = e^{−βEn}/Z`. -/
def thermalProbability (β E : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(β * E)) ^ n * (1 - Real.exp (-(β * E)))

theorem exp_neg_lt_one (β E : ℝ) (h : 0 < β * E) : Real.exp (-(β * E)) < 1 := by
  rw [← Real.exp_zero]; apply Real.exp_lt_exp.mpr; linarith

/-- **[Partition function] `Σ_n r^n = 1/(1 − r)`.**  The Gibbs partition function is the geometric sum of the
Boltzmann weights. -/
theorem thermalPartition_eq_tsum (β E : ℝ) (h : 0 < β * E) :
    ∑' n : ℕ, thermalWeight β E n = thermalPartitionFunction β E := by
  unfold thermalWeight thermalPartitionFunction
  exact tsum_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_lt_one β E h)

/-- **[Normalization] `Σ_n p_n = 1`.**  The Gibbs distribution is normalized — the density matrix has unit
trace. -/
theorem thermalProbability_tsum_one (β E : ℝ) (h : 0 < β * E) :
    ∑' n : ℕ, thermalProbability β E n = 1 := by
  have hd : (1 : ℝ) - Real.exp (-(β * E)) ≠ 0 := by have := exp_neg_lt_one β E h; linarith
  unfold thermalProbability
  rw [tsum_mul_right, tsum_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_lt_one β E h),
    inv_mul_cancel₀ hd]

/-- **[Planckian mean occupation] `Σ_n n·p_n = 1/(e^{βE} − 1)`.**  The mean number of quanta in the
Hartle–Hawking Gibbs state is the Bose–Einstein occupation — the density-matrix derivation of the thermality
agrees with the Bogoliubov one. -/
theorem thermal_mean_occupation (β E : ℝ) (h : 0 < β * E) :
    ∑' n : ℕ, (n : ℝ) * thermalProbability β E n = boseEinstein β E := by
  have hr1 : Real.exp (-(β * E)) < 1 := exp_neg_lt_one β E h
  have hd : (1 : ℝ) - Real.exp (-(β * E)) ≠ 0 := by linarith
  have hnorm : ‖Real.exp (-(β * E))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; exact hr1
  unfold thermalProbability
  rw [show (fun n : ℕ => (n : ℝ) * (Real.exp (-(β * E)) ^ n * (1 - Real.exp (-(β * E)))))
      = (fun n : ℕ => ((n : ℝ) * Real.exp (-(β * E)) ^ n) * (1 - Real.exp (-(β * E)))) from by
        funext n; ring,
    tsum_mul_right, tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  unfold boseEinstein
  rw [Real.exp_neg]
  have hE'_gt : 1 < Real.exp (β * E) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr h
  have hE'1 : Real.exp (β * E) - 1 ≠ 0 := by linarith
  have hE'0 : Real.exp (β * E) ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- **[Detailed balance] `p_{n+1}/p_n = e^{−βE}`.**  Successive Gibbs weights are in the Boltzmann ratio. -/
theorem thermalProbability_detailedBalance (β E : ℝ) (n : ℕ) (h : 0 < β * E) :
    thermalProbability β E (n + 1) / thermalProbability β E n = Real.exp (-(β * E)) := by
  have hd : (1 : ℝ) - Real.exp (-(β * E)) ≠ 0 := by have := exp_neg_lt_one β E h; linarith
  have hr : Real.exp (-(β * E)) ≠ 0 := Real.exp_ne_zero _
  unfold thermalProbability
  rw [pow_succ]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

end
