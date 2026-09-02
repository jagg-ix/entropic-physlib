/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelStrictArrow
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularFromState
public import Physlib.QuantumMechanics.NonHermitian.FermiDirac
meta import Zil

/-!
# The Gibbs–modular junction of the one-level carrier

When the stationary occupation is the Fermi function `f = 1/(1 + e^{βε})`, the one-level stationary
state is the **qubit Gibbs state** of the Hamiltonian with level energies `(0, ε)` at inverse
temperature `β`, and three time structures meet on this single carrier:

* **Gibbs form** (`stationaryState_gibbs_form`): `σ_f = Z⁻¹·diag(e^{-β·0}, e^{-βε})` with
  `Z = 1 + e^{-βε}` — the thermal state, not merely a fixed point.
* **Modular Hamiltonian identity** (`modularHamiltonian_stationaryState`): the Tomita–Takesaki
  generator of `σ_f` is affine in the system Hamiltonian, `K = -log σ_f = β·H_S + log Z·𝟙` — the
  textbook KMS relation between modular flow and thermal time, here an exact matrix identity.
* **Frozen modular clock vs strict entropic clock**: `K` commutes with `σ_f`
  (`modularHamiltonian_commute_stationaryState`) — the modular flow leaves the equilibrium invariant —
  while one step of the dissipative channel **strictly decreases** the quantum relative entropy to
  `σ_f` on every interior-occupation non-stationary state
  (`oneLevelChannel_qRelativeEnt_gibbs_strictLt`, the strict entropic arrow instantiated at the
  thermal reference, with the interiority and non-degeneracy hypotheses discharged from Fermi-function
  positivity and `βε ≠ 0`).

This closes the items "faithful thermal equilibrium", "modular generator `K = βH + log Z`", and
"strict entropic production toward it" of the constrained-carrier synthesis on one concrete carrier.
Honest scope: the remaining synthesis items — the Hamiltonian-constraint carrier
`(H_C + H_S + H_int)|Ψ⟩ = 0` and the Page–Wootters conditional GKSL generator — exist as the
`RelationalTime.PageWootters` skeleton (`HamiltonianConstraint`, `DissipativeConditionalClock`) on
continuous linear maps; identifying that operator-level clock with this matrix-level carrier is not
built here. The degenerate case `βε = 0` (infinite temperature, `f = 1/2`) stays excluded, as in the
strict arrow.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Physlib.QuantumMechanics.NonHermitian.FermiDirac (nhFermiDirac)
open QuantumMechanics.FiniteTarget (modularHamiltonianMat modularHamiltonianMat_mat)

/-! ## Fermi-function facts -/

theorem nhFermiDirac_zero_pos (β ε : ℝ) : 0 < nhFermiDirac β ε 0 0 := by
  simp only [nhFermiDirac]
  positivity

theorem nhFermiDirac_zero_lt_one (β ε : ℝ) : nhFermiDirac β ε 0 0 < 1 := by
  simp only [nhFermiDirac]
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (β * (ε + 0 - 0))]

/-- `1 - f = Z⁻¹` with `Z = 1 + e^{-βε}`: the ground-level Gibbs weight. -/
theorem one_sub_nhFermiDirac (β ε : ℝ) :
    1 - nhFermiDirac β ε 0 0 = (1 + Real.exp (-(β * ε)))⁻¹ := by
  have hE : 0 < Real.exp (β * ε) := Real.exp_pos _
  have h1 : (0:ℝ) < 1 + Real.exp (β * ε) := by linarith
  have hZ : (1:ℝ) + (Real.exp (β * ε))⁻¹ = (1 + Real.exp (β * ε)) / Real.exp (β * ε) := by
    rw [add_div, div_self hE.ne']
    ring
  simp only [nhFermiDirac, add_zero, sub_zero]
  rw [Real.exp_neg, hZ, inv_div, one_sub_div h1.ne',
    show (1 + Real.exp (β * ε) - 1) = Real.exp (β * ε) from by ring]

/-- `f = e^{-βε}·Z⁻¹`: the excited-level Gibbs weight. -/
theorem nhFermiDirac_eq_exp_mul (β ε : ℝ) :
    nhFermiDirac β ε 0 0 = Real.exp (-(β * ε)) * (1 + Real.exp (-(β * ε)))⁻¹ := by
  have hE : 0 < Real.exp (β * ε) := Real.exp_pos _
  have hZ : (1:ℝ) + (Real.exp (β * ε))⁻¹ = (1 + Real.exp (β * ε)) / Real.exp (β * ε) := by
    rw [add_div, div_self hE.ne']
    ring
  simp only [nhFermiDirac, add_zero, sub_zero]
  rw [Real.exp_neg, hZ, inv_div, ← mul_div_assoc, inv_mul_cancel₀ hE.ne']

/-- `-log(1 - f) = log Z`: the ground modular eigenvalue. -/
theorem neg_log_one_sub_nhFermiDirac (β ε : ℝ) :
    -Real.log (1 - nhFermiDirac β ε 0 0) = Real.log (1 + Real.exp (-(β * ε))) := by
  rw [one_sub_nhFermiDirac, Real.log_inv]
  ring

/-- `-log f = βε + log Z`: the excited modular eigenvalue. -/
theorem neg_log_nhFermiDirac (β ε : ℝ) :
    -Real.log (nhFermiDirac β ε 0 0) = β * ε + Real.log (1 + Real.exp (-(β * ε))) := by
  have hZ : (0:ℝ) < (1 + Real.exp (-(β * ε)))⁻¹ := by positivity
  rw [nhFermiDirac_eq_exp_mul, Real.log_mul (Real.exp_ne_zero _) hZ.ne', Real.log_exp,
    Real.log_inv]
  ring

/-! ## The stationary state is the qubit Gibbs state -/

/-- **The Gibbs form of the stationary state.** At the Fermi occupation the stationary state is
`Z⁻¹·diag(e^{-β·0}, e^{-βε})` — the thermal state of the level energies `(0, ε)`. -/
theorem stationaryState_gibbs_form (β ε : ℝ) (d : OneLevelChannelData)
    (hf : d.occupation = nhFermiDirac β ε 0 0) :
    d.stationaryState.m
      = Matrix.diagonal fun i =>
          ((Real.exp (-(β * (![0, ε] i))) * (1 + Real.exp (-(β * ε)))⁻¹ : ℝ) : ℂ) := by
  rw [stationaryState_m_diagonal]
  congr 1
  funext i
  fin_cases i
  · have h := one_sub_nhFermiDirac β ε
    rw [← hf] at h
    simp [h]
  · have h := nhFermiDirac_eq_exp_mul β ε
    rw [← hf] at h
    simp [h]

/-! ## The modular Hamiltonian is `βH + log Z` -/

/-- **The modular Hamiltonian of the stationary state, diagonalized.** At the Fermi occupation the
Tomita–Takesaki generator `K = -log σ_f` has eigenvalues `β·E_i + log Z` over the level energies
`E = (0, ε)`. -/
theorem modularHamiltonian_stationaryState_mat (β ε : ℝ) (d : OneLevelChannelData)
    (hf : d.occupation = nhFermiDirac β ε 0 0) :
    (modularHamiltonianMat d.stationaryState).mat
      = Matrix.diagonal fun i =>
          ((β * (![0, ε] i) + Real.log (1 + Real.exp (-(β * ε))) : ℝ) : ℂ) := by
  have hfun : (fun i => -(Real.log (![1 - d.occupation, d.occupation] i)))
      = fun i => β * (![0, ε] i) + Real.log (1 + Real.exp (-(β * ε))) := by
    funext i
    fin_cases i
    · have h := neg_log_one_sub_nhFermiDirac β ε
      rw [← hf] at h
      simpa using h
    · have h := neg_log_nhFermiDirac β ε
      rw [← hf] at h
      simpa using h
  rw [modularHamiltonianMat_mat, stationaryState_M_log d, HermitianMat.diagonal_mat,
    Matrix.diagonal_neg]
  congr 1
  funext i
  have hi := congrFun hfun i
  rw [← hi]
  norm_cast

/-- **The KMS affine relation `K = β·H_S + log Z·𝟙`** (od5's modular-generator identity): the modular
Hamiltonian of the thermal stationary state is the system Hamiltonian rescaled by the inverse
temperature, shifted by the log-partition function. -/
theorem modularHamiltonian_stationaryState (β ε : ℝ) (d : OneLevelChannelData)
    (hf : d.occupation = nhFermiDirac β ε 0 0) :
    (modularHamiltonianMat d.stationaryState).mat
      = (β : ℂ) • Matrix.diagonal (fun i => ((![0, ε] i : ℝ) : ℂ))
        + ((Real.log (1 + Real.exp (-(β * ε))) : ℝ) : ℂ) • 1 := by
  rw [modularHamiltonian_stationaryState_mat β ε d hf]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp only [Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul]
    push_cast
    ring
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- **The modular clock is frozen at equilibrium**: the modular Hamiltonian commutes with the
stationary state (both diagonal), so the modular flow leaves the equilibrium carrier invariant —
in contrast with the strict entropic decrease of the dissipative step. Holds for every stationary
occupation. -/
theorem modularHamiltonian_commute_stationaryState (d : OneLevelChannelData) :
    Commute (modularHamiltonianMat d.stationaryState).mat d.stationaryState.m := by
  rw [modularHamiltonianMat_mat, stationaryState_M_log d, HermitianMat.diagonal_mat,
    Matrix.diagonal_neg, stationaryState_m_diagonal]
  exact Matrix.commute_diagonal _ _

/-! ## The strict entropic arrow toward the thermal state -/

/-- **The strict entropic arrow at the Gibbs reference.** For a thermal stationary occupation
(`f = 1/(1+e^{βε})`, `βε ≠ 0`) and positive damping, one channel step strictly decreases the quantum
relative entropy to the thermal state on every interior-occupation qubit state other than the thermal
state itself — the interiority and non-degeneracy hypotheses of the strict arrow are exactly the
Fermi-function facts. -/
theorem oneLevelChannel_qRelativeEnt_gibbs_strictLt (β ε : ℝ) (hβε : β * ε ≠ 0)
    (d : OneLevelChannelData) (hf : d.occupation = nhFermiDirac β ε 0 0)
    (hd0 : 0 < d.damping) (ρ : MState Qubit)
    (hN0 : 0 < excitedOccupation ρ) (hN1 : excitedOccupation ρ < 1)
    (hne : ρ ≠ d.stationaryState) :
    qRelativeEnt (oneLevelChannel d ρ) d.stationaryState
      < qRelativeEnt ρ d.stationaryState := by
  refine oneLevelChannel_qRelativeEnt_strictLt_of_ne d ?_ ?_ ?_ hd0 ρ hN0 hN1 hne
  · rw [hf]; exact nhFermiDirac_zero_pos β ε
  · rw [hf]; exact nhFermiDirac_zero_lt_one β ε
  · rw [hf]
    intro hc
    simp only [nhFermiDirac] at hc
    have h2 : (0:ℝ) < 1 + Real.exp (β * (ε + 0 - 0)) := by positivity
    rw [div_eq_iff h2.ne'] at hc
    have hE1 : Real.exp (β * (ε + 0 - 0)) = 1 := by linarith
    have hz : β * (ε + 0 - 0) = 0 := Real.exp_eq_exp.mp (by rw [hE1, Real.exp_zero])
    exact hβε (by linarith [hz])

end LindbladDrivenLeads
end QuantumMechanics

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.stationaryState_gibbs_form where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:at-the-fermi-occupation-the-one-level-stationary-state-is-the-qubit-gibbs-state-of-the-level-energies-zero-and-epsilon-at-inverse-temperature-beta",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.modularHamiltonian_stationaryState where
  formalizes @ "claim:the-tomita-takesaki-modular-hamiltonian-of-the-thermal-one-level-stationary-state-is-beta-times-the-system-hamiltonian-plus-log-partition-function-times-identity",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.modularHamiltonianMat",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.modularHamiltonian_commute_stationaryState where
  supported_by @ "lean:HermitianMat.diagonal_mat",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.modularHamiltonianMat_mat",
  formalizes @ "claim:the-modular-hamiltonian-commutes-with-the-stationary-state-so-the-modular-clock-is-frozen-at-equilibrium-while-the-dissipative-entropic-clock-strictly-flows",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_gibbs_strictLt where
  formalizes @ "claim:one-channel-step-strictly-decreases-the-quantum-relative-entropy-to-the-thermal-gibbs-state-on-every-interior-occupation-qubit-state-other-than-the-thermal-state-with-the-hypotheses-discharged-from-fermi-function-facts",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt_of_ne",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.modularHamiltonian_stationaryState",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-closes-the-thermal-equilibrium-modular-generator-and-strict-production-items-of-the-constrained-carrier-synthesis-on-one-carrier-the-hamiltonian-constraint-and-page-wootters-conditional-gksl-generator-identification-with-this-matrix-carrier-remain-open-and-infinite-temperature-beta-epsilon-zero-stays-excluded"

/- ZIL-END -/
