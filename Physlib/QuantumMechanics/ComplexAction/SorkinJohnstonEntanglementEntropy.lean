/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entanglement entropy of the Sorkin–Johnston region vacuum

The Sorkin–Johnston vacuum restricted to a subregion is a quasi-free (Gaussian) state, so its
**entanglement entropy** is a sum over the eigenvalues `λ_k ∈ [0,1]` of the reduced fermionic
two-point (correlation) function of the single-mode entropies. Each mode contributes the **binary
entropy** of its occupation,

 `S(λ) = −λ ln λ − (1−λ) ln(1−λ) = binEntropy(λ)`,

the von Neumann entropy of a fermionic occupation `λ`. This module builds that entropy on Mathlib's
`Real.binEntropy` and links it to the modular (KMS) Fermi–Dirac occupation of
`ComplexFermionicOscillator`, closing the loop from the SJ region state
(`SorkinJohnstonRegionState`) to entropic time.

* **§A — the single-mode SJ entropy** `S(λ) = binEntropy λ`. Non-negativity on `[0,1]`
 (`sjModeEntropy_nonneg`), the maximum `ln 2` (`sjModeEntropy_le_log_two`), purity at empty/full modes
 (`sjModeEntropy_pure`, `_empty`, `_full`), and the maximum at half-filling
 (`sjModeEntropy_maximal`, `λ = ½`).
* **§B — the occupation is Pauli-bounded** `0 < λ < 1` for a thermal fermionic mode
 (`fermiDirac_pos`, `fermiDirac_lt_one`) — the reduced correlation eigenvalue lies in the unit
 interval, so the entropy is well-defined and non-negative.
* **§C — the modular (KMS) thermal entropy.** At the modular occupation `λ = fermiDirac(βε)` (the
 Bisognano–Wichmann/Unruh temperature of the region vacuum), the SJ entanglement entropy is the
 thermal entropy `sjThermalEntropy` — non-negative and bounded by `ln 2`.
* **§D — the von Neumann / Boltzmann form.** `sjModeEntropy_eq_negMulLog`: `S(λ) = negMulLog λ +
 negMulLog(1−λ)`, the `−x ln x` Boltzmann form — the entropic-weight `−log` of the mode occupation.

Proven: all the entropy bounds and identities, the Pauli bound of the thermal
occupation, and the thermal-entropy non-negativity/bound. Interpretive: the reduction of the SJ region
state to its per-mode occupations `λ_k` (a Gaussian/quasi-free diagonalization) is the datum; the total
region entropy is the sum `Σ_k S(λ_k)` of these single-mode contributions.

## References

* R. D. Sorkin, "Expressing entropy globally in terms of (4D) field correlations", J. Phys. Conf. Ser.
 484, 012004 (2014); N. Afshordi, S. Aslanbeigi, R. D. Sorkin, JHEP 08 (2012) 137. Reuses
 `Real.binEntropy` (Mathlib), `SorkinJohnstonRegionState`, and
 `ComplexOscillator.ComplexFermionicOscillator` (`fermiDirac`).

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonEntanglementEntropy

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-! ## §A — the single-mode Sorkin–Johnston entanglement entropy -/

/-- **The single-mode SJ entanglement entropy** `S(λ) = binEntropy λ = −λ ln λ − (1−λ) ln(1−λ)`, the
von Neumann entropy of a reduced fermionic mode with occupation `λ ∈ [0,1]`. -/
noncomputable def sjModeEntropy (lam : ℝ) : ℝ := Real.binEntropy lam

/-- **The mode entropy is non-negative** on the physical range `λ ∈ [0,1]`. -/
theorem sjModeEntropy_nonneg (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : 0 ≤ sjModeEntropy lam :=
  Real.binEntropy_nonneg h0 h1

/-- **The mode entropy is bounded by `ln 2`** — one fermionic mode records at most one bit. -/
theorem sjModeEntropy_le_log_two (lam : ℝ) : sjModeEntropy lam ≤ Real.log 2 :=
  Real.binEntropy_le_log_two

/-- **A mode is pure (unentangled) iff it is empty or full** `S(λ) = 0 ↔ λ = 0 ∨ λ = 1`. -/
theorem sjModeEntropy_pure (lam : ℝ) : sjModeEntropy lam = 0 ↔ lam = 0 ∨ lam = 1 :=
  Real.binEntropy_eq_zero

/-- **An empty mode has no entropy** `S(0) = 0`. -/
theorem sjModeEntropy_empty : sjModeEntropy 0 = 0 := Real.binEntropy_zero

/-- **A full mode has no entropy** `S(1) = 0`. -/
theorem sjModeEntropy_full : sjModeEntropy 1 = 0 := Real.binEntropy_one

/-- **Half-filling is maximally entangled** `S(½) = ln 2`: the reduced mode is maximally mixed. -/
theorem sjModeEntropy_maximal : sjModeEntropy (1 / 2) = Real.log 2 :=
  Real.binEntropy_eq_log_two.mpr (by norm_num)

/-! ## §B — the occupation is Pauli-bounded -/

/-- **The thermal fermionic occupation is positive** `0 < fermiDirac x`. -/
theorem fermiDirac_pos (x : ℝ) : 0 < fermiDirac x := by
  unfold fermiDirac; positivity

/-- **The thermal fermionic occupation is below one** `fermiDirac x < 1` (Pauli exclusion): the reduced
correlation eigenvalue lies strictly inside the unit interval. -/
theorem fermiDirac_lt_one (x : ℝ) : fermiDirac x < 1 := by
  unfold fermiDirac
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos x]

/-! ## §C — the modular (KMS) thermal entropy -/

/-- **The modular thermal SJ entropy** `S(fermiDirac(βε))`: the entanglement entropy of the SJ region
vacuum at the modular (Bisognano–Wichmann/Unruh) Fermi–Dirac occupation. -/
noncomputable def sjThermalEntropy (β ε : ℝ) : ℝ := sjModeEntropy (fermiDirac (β * ε))

/-- **The thermal SJ entropy is non-negative** — the modular occupation is Pauli-bounded in `[0,1]`. -/
theorem sjThermalEntropy_nonneg (β ε : ℝ) : 0 ≤ sjThermalEntropy β ε :=
  sjModeEntropy_nonneg _ (fermiDirac_pos _).le (fermiDirac_lt_one _).le

/-- **The thermal SJ entropy is bounded by `ln 2`** — one bit per mode, at any temperature. -/
theorem sjThermalEntropy_le_log_two (β ε : ℝ) : sjThermalEntropy β ε ≤ Real.log 2 :=
  sjModeEntropy_le_log_two _

/-! ## §D — the von Neumann / Boltzmann form -/

/-- **The mode entropy in Boltzmann form** `S(λ) = negMulLog λ + negMulLog(1−λ) = −λ ln λ − (1−λ)ln(1−λ)`
— the `−x ln x` von Neumann/entropic-weight form of the reduced occupation. -/
theorem sjModeEntropy_eq_negMulLog (lam : ℝ) :
    sjModeEntropy lam = Real.negMulLog lam + Real.negMulLog (1 - lam) :=
  Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub lam

end Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonEntanglementEntropy
