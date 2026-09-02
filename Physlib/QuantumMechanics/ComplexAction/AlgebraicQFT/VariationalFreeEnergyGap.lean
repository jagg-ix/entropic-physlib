/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
meta import Zil

/-!
# The variational free-energy gap: relative entropy as the Lyapunov free-energy gap

Abstract carrier extracting the Gibbs–Bogoliubov–Feynman free-energy structure of
`AlgebraicQFT.FiniteArakiRelativeEntropy` into a single reusable Lyapunov functional — the
**free-energy gap** `ΔF = (1/β)·S(p‖q)`. This is the object the open-system decoherence,
AQFT-modular passivity, and non-Hermitian dissipation sectors all need: the relative entropy is
exactly `β` times the excess of a trial free energy over the Gibbs free energy, so it is
nonnegative (the variational principle), vanishes at the Gibbs state (the minimizer), and any
dynamics that does not increase the relative entropy does not increase the gap (the abstract
H-theorem descent).

* `freeEnergyGap p q β = S(p‖q)/β` — the free-energy gap.
* `freeEnergyGap_nonneg` — the Lyapunov nonnegativity (Klein's inequality).
* **`trialFreeEnergy_sub_gibbs_eq_gap`** — the *sharp* variational principle: the excess of a trial
  free energy over the Gibbs free energy is exactly the free-energy gap,
  `F_trial[p] − F_Gibbs = (1/β)·S(p‖e^{−βE}/Z)` — an equality, not merely the inequality
  `finite_gibbs_variational_upper_bound`.
* `trialFreeEnergy_ge_gibbs` — the resulting variational bound `F_Gibbs ≤ F_trial`, now with the
  deficit identified as a relative entropy.
* `gibbsState_saturates` — the Gibbs state has zero gap: it is the variational minimizer.
* `freeEnergyGap_lyapunov_descent` — the H-theorem interface: a relative-entropy-non-increasing
  step is a free-energy-gap-non-increasing step (the finite Spohn descent hook for CPTP/Lindblad
  dynamics).

**Honest layering.** Every result is an exact identity or an inequality on the finite probability
simplex, reusing the proven finite-Gibbs API (`finiteRelativeEntropy_nonneg`,
`finiteRelativeEntropy_gibbs_free_energy`). The novel content is the *equality*
`excess = (1/β)·relative entropy`, which sharpens the existing variational *inequality* and exposes
the gap as the Lyapunov functional the descent interface consumes. No dynamics is built here — the
descent theorem is stated as a hypothesis on the relative-entropy step, so it is the interface a
Lindblad/CPTP monotonicity result plugs into.

## References

* The Gibbs–Bogoliubov–Feynman variational principle; the free energy as relative entropy (Klein's
  inequality). Built on `AlgebraicQFT.FiniteArakiRelativeEntropy` (`finiteRelativeEntropy`,
  `finiteTrialFreeEnergy`, `gibbsFreeEnergy`, `finite_gibbs_variational_upper_bound`).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap

variable {ι : Type*} [Fintype ι]

/-- The **free-energy gap** `ΔF = (1/β)·S(p‖q)` — the reciprocal-temperature-scaled relative
entropy, the Lyapunov functional of the variational free-energy principle. -/
noncomputable def freeEnergyGap (p q : ι → ℝ) (β : ℝ) : ℝ := finiteRelativeEntropy p q / β

/-- **The free-energy gap is a nonnegative Lyapunov functional** `ΔF ≥ 0` — from Klein's inequality
(`finiteRelativeEntropy_nonneg`) and `β > 0`: the trial free energy never lies below the Gibbs free
energy. -/
theorem freeEnergyGap_nonneg (p q : ι → ℝ) (β : ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hmass : ∑ i, p i = ∑ i, q i) (hβ : 0 < β) : 0 ≤ freeEnergyGap p q β :=
  div_nonneg (finiteRelativeEntropy_nonneg p q hp hq hmass) hβ.le

/-- **[The relative entropy of a state with itself vanishes]** `S(q‖q) = 0`. -/
lemma finiteRelativeEntropy_self (q : ι → ℝ) : finiteRelativeEntropy q q = 0 := by
  unfold finiteRelativeEntropy
  apply Finset.sum_eq_zero
  intro i _
  rcases eq_or_ne (q i) 0 with h | h
  · rw [h, zero_mul]
  · rw [div_self h, Real.log_one, mul_zero]

/-- **The variational excess is the free-energy gap** `F_trial[p] − F_Gibbs = (1/β)·S(p‖e^{−βE}/Z)`:
the amount by which a trial state's free energy exceeds the true Gibbs free energy is *exactly* the
free-energy gap (the scaled relative entropy). This equality sharpens the Gibbs variational
*inequality* `finite_gibbs_variational_upper_bound`: the deficit is not merely nonnegative, it is a
relative entropy. -/
theorem trialFreeEnergy_sub_gibbs_eq_gap (p E : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hZ : 0 < Z) (hnorm : ∑ i, p i = 1) (hβ : 0 < β) :
    finiteTrialFreeEnergy p E β - gibbsFreeEnergy Z β
      = freeEnergyGap p (fun i => Real.exp (-(β * E i)) / Z) β := by
  have hβ' : β ≠ 0 := hβ.ne'
  unfold freeEnergyGap
  rw [finiteRelativeEntropy_gibbs_free_energy p E β Z hp hZ hnorm]
  unfold finiteTrialFreeEnergy gibbsFreeEnergy
  field_simp
  ring

/-- **The sharp variational principle** `F_Gibbs ≤ F_trial[p]` — the Gibbs free energy is the
minimum over trial states, now with the deficit identified (via `trialFreeEnergy_sub_gibbs_eq_gap`)
as the nonnegative free-energy gap. -/
theorem trialFreeEnergy_ge_gibbs (p E : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hZ : 0 < Z) (hnorm : ∑ i, p i = 1) (hβ : 0 < β)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    gibbsFreeEnergy Z β ≤ finiteTrialFreeEnergy p E β := by
  have hq : ∀ i, 0 < Real.exp (-(β * E i)) / Z := fun i => div_pos (Real.exp_pos _) hZ
  have hqnorm : ∑ i, Real.exp (-(β * E i)) / Z = 1 := by
    rw [← Finset.sum_div, hpartition, div_self hZ.ne']
  have hgap := trialFreeEnergy_sub_gibbs_eq_gap p E β Z hp hZ hnorm hβ
  have hnn := freeEnergyGap_nonneg p (fun i => Real.exp (-(β * E i)) / Z) β hp hq
    (hnorm.trans hqnorm.symm) hβ
  linarith [hgap, hnn]

/-- **The Gibbs state saturates the variational bound** `F_trial[e^{−βE}/Z] = F_Gibbs` — the
free-energy gap vanishes exactly at the Gibbs state, so the Gibbs state is the variational
minimizer (finite vacuum passivity: no free energy can be extracted from the equilibrium state). -/
theorem gibbsState_saturates (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z) (hβ : 0 < β)
    (hpartition : ∑ i, Real.exp (-(β * E i)) = Z) :
    finiteTrialFreeEnergy (fun i => Real.exp (-(β * E i)) / Z) E β = gibbsFreeEnergy Z β := by
  have hq : ∀ i, 0 < Real.exp (-(β * E i)) / Z := fun i => div_pos (Real.exp_pos _) hZ
  have hqnorm : ∑ i, Real.exp (-(β * E i)) / Z = 1 := by
    rw [← Finset.sum_div, hpartition, div_self hZ.ne']
  have hgap := trialFreeEnergy_sub_gibbs_eq_gap (fun i => Real.exp (-(β * E i)) / Z) E β Z hq hZ
    hqnorm hβ
  rw [freeEnergyGap, finiteRelativeEntropy_self, zero_div] at hgap
  linarith

/-- **The H-theorem descent interface** — a step that does not increase the relative entropy does
not increase the free-energy gap: `S(p'‖q) ≤ S(p‖q) ⟹ ΔF[p'] ≤ ΔF[p]`. This is the abstract
Lyapunov-descent hook: a Lindblad/CPTP monotonicity result (data processing) supplies the
hypothesis, and the free energy then descends monotonically toward the steady state — the finite
form of Spohn's quantum H-theorem. -/
theorem freeEnergyGap_lyapunov_descent (p p' q : ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hstep : finiteRelativeEntropy p' q ≤ finiteRelativeEntropy p q) :
    freeEnergyGap p' q β ≤ freeEnergyGap p q β := by
  unfold freeEnergyGap
  gcongr

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.freeEnergyGap_nonneg where
  formalizes @ "claim:the-free-energy-gap-is-a-nonnegative-lyapunov-functional-the-variational-principle",
  supported_by @ "paper:gibbs-bogoliubov-feynman-variational-principle"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.trialFreeEnergy_sub_gibbs_eq_gap where
  formalizes @ "claim:the-trial-minus-gibbs-free-energy-excess-is-exactly-the-scaled-relative-entropy-the-sharp-variational-principle",
  requires @ "claim:the-free-energy-gap-is-a-nonnegative-lyapunov-functional-the-variational-principle",
  supported_by @ "paper:gibbs-bogoliubov-feynman-variational-principle",
  caveat @ "claim:equality-sharpening-the-existing-variational-inequality-the-deficit-is-a-relative-entropy"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.gibbsState_saturates where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.trialFreeEnergy_sub_gibbs_eq_gap",
  formalizes @ "claim:the-gibbs-state-has-zero-free-energy-gap-it-is-the-variational-minimizer-finite-passivity",
  requires @ "claim:the-trial-minus-gibbs-free-energy-excess-is-exactly-the-scaled-relative-entropy-the-sharp-variational-principle"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.freeEnergyGap_lyapunov_descent where
  formalizes @ "claim:a-relative-entropy-non-increasing-step-is-a-free-energy-gap-non-increasing-step-the-h-theorem-descent-interface",
  requires @ "claim:the-free-energy-gap-is-a-nonnegative-lyapunov-functional-the-variational-principle",
  caveat @ "claim:the-descent-hypothesis-is-the-interface-a-lindblad-cptp-monotonicity-result-supplies-no-dynamics-built-here"

zil_file_contract physlib.variationalFreeEnergyGap where
  promises "The variational free-energy gap: the free-energy gap is the reciprocal-temperature-scaled relative entropy, a nonnegative Lyapunov functional; the excess of a trial free energy over the Gibbs free energy is exactly that gap (the sharp variational principle, an equality); the Gibbs state saturates it as the minimizer (finite passivity); and a relative-entropy-non-increasing step descends the gap (the abstract Spohn H-theorem interface)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.freeEnergyGap",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy.finiteRelativeEntropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy.finiteTrialFreeEnergy"]
  forbids_substitutes ["any open-system dynamics, the descent is stated as a hypothesis interface not a derived semigroup",
    "the strict equality case of Klein's inequality, only the saturation at the Gibbs state is shown"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.freeEnergyGap_nonneg,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.trialFreeEnergy_sub_gibbs_eq_gap,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.gibbsState_saturates,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.freeEnergyGap_lyapunov_descent]

/- ZIL-END -/
