/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.GaussianEntanglement.EntanglementTemperatureThreshold

/-!
# The single-mode thermal von Neumann entropy of a squeezed thermal state

Ports `lean4/QCDVortex/VonNeumann.lean` of the qcd-vortex-entanglement tree (Lean layer own
authorship; Martín Alonso, Zenodo 10.5281/zenodo.18353640): the bosonic single-mode thermal
entropy in bits, `S(n̄) = ((n̄+1)·log(n̄+1) − n̄·log n̄)/log 2` (well-defined at `n̄ = 0` by
`Real.log 0 = 0`):

* `tmstModeEntropy_zero` / `_one` — vacuum carries zero entropy, `n̄ = 1` carries two bits;
* `tmstModeEntropy_nonneg` / `_pos` — nonnegativity via the decomposition
  `n̄·log((n̄+1)/n̄) + log(n̄+1)` of the numerator;
* `tmstModeEntropy_eq_zero_iff` and `tmstModeEntropy_zero_iff_T_zero` — the entropy vanishes
  exactly on the vacuum, equivalently exactly at zero temperature through the Bose–Einstein
  occupation.

**Honest layering.**  Exact real analysis on the closed-form entropy; the identification of
`S(n̄)` with the von Neumann entropy of the reduced thermal mode is the standard Gaussian-state
computation, cited not re-proven (the matrix-level von Neumann entropy lives in
`QuantumInfo.Entropy.VonNeumann`).

## References

* Source: `lean4/QCDVortex/VonNeumann.lean` (own authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.GaussianEntanglement.SqueezedThermalModeEntropy

open Real Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal
open Physlib.QuantumMechanics.GaussianEntanglement.EntanglementTemperatureThreshold

-- ─────────────────────────────────────────────────────────────────────────────
-- § Definition
-- ─────────────────────────────────────────────────────────────────────────────

/-- Single-mode bosonic von Neumann entropy in bits for a thermal state with
    mean occupation n̄ ≥ 0:

        S(n̄) = ((n̄+1)·ln(n̄+1) − n̄·ln n̄) / ln 2

    We use Lean's convention `Real.log 0 = 0`, so S(0) = 0 automatically.

    Source: `EntanglementMeasures._entropy_gaussian` in entanglement_detection.py,
    with substitution n̄ = symplectic_eigenvalue − ½. -/
noncomputable def tmstModeEntropy (n_bar : ℝ) : ℝ :=
  ((n_bar + 1) * log (n_bar + 1) - n_bar * log n_bar) / log 2

-- ─────────────────────────────────────────────────────────────────────────────
-- § Basic evaluations
-- ─────────────────────────────────────────────────────────────────────────────

/-- Vacuum state has zero entropy: S(0) = 0. -/
@[simp]
theorem tmstModeEntropy_zero : tmstModeEntropy 0 = 0 := by
  simp [tmstModeEntropy, Real.log_one]

/-- At n̄ = 1: S(1) = 2 bits. -/
theorem tmstModeEntropy_one : tmstModeEntropy 1 = 2 := by
  have hlog2 : log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  simp only [tmstModeEntropy, Real.log_one]
  field_simp [hlog2]
  ring

-- ─────────────────────────────────────────────────────────────────────────────
-- § Nonnegativity
-- ─────────────────────────────────────────────────────────────────────────────

/-- Key decomposition: for n̄ > 0,
        (n̄+1)·log(n̄+1) − n̄·log n̄ = n̄·log((n̄+1)/n̄) + log(n̄+1)
    Both summands are nonneg for n̄ > 0. -/
private lemma entropy_numer_decomp {n_bar : ℝ} (hn : 0 < n_bar) :
    (n_bar + 1) * log (n_bar + 1) - n_bar * log n_bar =
    n_bar * log ((n_bar + 1) / n_bar) + log (n_bar + 1) := by
  rw [Real.log_div (by linarith) (ne_of_gt hn)]
  ring

/-- The numerator (n̄+1)·log(n̄+1) − n̄·log n̄ is nonneg for n̄ ≥ 0. -/
lemma entropy_numer_nonneg {n_bar : ℝ} (hn : 0 ≤ n_bar) :
    0 ≤ (n_bar + 1) * log (n_bar + 1) - n_bar * log n_bar := by
  rcases eq_or_lt_of_le hn with rfl | hn_pos
  · simp [Real.log_one]
  · rw [entropy_numer_decomp hn_pos]
    have hdiv_gt : 1 < (n_bar + 1) / n_bar := by
      rw [lt_div_iff₀ hn_pos]; linarith
    have h1 : 0 ≤ n_bar * log ((n_bar + 1) / n_bar) :=
      mul_nonneg hn_pos.le (Real.log_pos hdiv_gt).le
    have h2 : 0 ≤ log (n_bar + 1) :=
      Real.log_nonneg (by linarith)
    linarith

/-- **Nonnegativity**: S(n̄) ≥ 0 for all n̄ ≥ 0. -/
theorem tmstModeEntropy_nonneg {n_bar : ℝ} (hn : 0 ≤ n_bar) :
    0 ≤ tmstModeEntropy n_bar := by
  apply div_nonneg (entropy_numer_nonneg hn)
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

-- ─────────────────────────────────────────────────────────────────────────────
-- § Zero entropy characterisation
-- ─────────────────────────────────────────────────────────────────────────────

/-- Strict positivity of the numerator for n̄ > 0. -/
private lemma entropy_numer_pos {n_bar : ℝ} (hn : 0 < n_bar) :
    0 < (n_bar + 1) * log (n_bar + 1) - n_bar * log n_bar := by
  rw [entropy_numer_decomp hn]
  have hlog_n1 : 0 < log (n_bar + 1) := Real.log_pos (by linarith)
  have hlog_frac : 0 ≤ log ((n_bar + 1) / n_bar) := by
    apply le_of_lt; apply Real.log_pos
    have h2 : 0 < 1 / n_bar := div_pos one_pos hn
    linarith [show (n_bar + 1) / n_bar = 1 + 1 / n_bar from by field_simp [hn.ne']]
  linarith [mul_nonneg hn.le hlog_frac]

/-- S(n̄) > 0 for n̄ > 0. -/
theorem tmstModeEntropy_pos {n_bar : ℝ} (hn : 0 < n_bar) :
    0 < tmstModeEntropy n_bar :=
  div_pos (entropy_numer_pos hn) (Real.log_pos (by norm_num))

/-- **Zero-entropy characterisation**: S(n̄) = 0 ↔ n̄ = 0 (for n̄ ≥ 0). -/
theorem tmstModeEntropy_eq_zero_iff {n_bar : ℝ} (hn : 0 ≤ n_bar) :
    tmstModeEntropy n_bar = 0 ↔ n_bar = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < n_bar := lt_of_le_of_ne hn (Ne.symm hne)
    linarith [tmstModeEntropy_pos hpos]
  · rintro rfl
    exact tmstModeEntropy_zero

-- ─────────────────────────────────────────────────────────────────────────────
-- § Connection to temperature
-- ─────────────────────────────────────────────────────────────────────────────

/-- The TMST mode entropy at temperature T is zero iff T = 0
    (for ω > 0): S(n̄(T,ω)) = 0 ↔ T = 0. -/
theorem tmstModeEntropy_zero_iff_T_zero {T ω : ℝ} (hT : 0 ≤ T) (hω : 0 < ω) :
    tmstModeEntropy (boseEinstein T ω) = 0 ↔ T = 0 := by
  rw [tmstModeEntropy_eq_zero_iff]
  · -- Goal: boseEinstein T ω = 0 ↔ T = 0
    constructor
    · intro h
      by_contra hne
      have hT_pos : 0 < T := lt_of_le_of_ne hT (Ne.symm hne)
      linarith [boseEinstein_pos hT_pos hω]
    · rintro rfl
      simp [boseEinstein]
  · -- boseEinstein T ω ≥ 0
    rcases eq_or_lt_of_le hT with rfl | hT_pos
    · simp [boseEinstein]
    · exact le_of_lt (boseEinstein_pos hT_pos hω)

end Physlib.QuantumMechanics.GaussianEntanglement.SqueezedThermalModeEntropy

end
