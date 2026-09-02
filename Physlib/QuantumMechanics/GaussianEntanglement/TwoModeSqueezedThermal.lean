/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Two-mode squeezed thermal states: the entanglement threshold

Ports `lean4/QCDVortex/TMST.lean` of the qcd-vortex-entanglement tree (the Lean layer is own
authorship; physics context: Martín Alonso, *Entanglement Dominance in the Zero-Temperature
Limit*, Zenodo 10.5281/zenodo.18353640, Theorem 4.3.1).

For a two-mode squeezed thermal state (TMST) with squeezing `r` and mean thermal occupation
`n̄ ≥ 0`, the minimum symplectic eigenvalue of the partially transposed covariance matrix is
`ν₋(r, n̄) = (n̄ + ½)·e^{−2r}`, and the Simon/PPT criterion reads `ν₋ ≤ ½`:

* `theorem_4_3_1` — the separability boundary: `ν₋ ≤ ½ ↔ r ≥ r_c(n̄)` with the critical
  squeezing `r_c(n̄) = ½·log(2n̄+1)`;
* `nu_at_threshold`, `theorem_4_3_1_strict`, `nu_strictMono_neg_r` — the boundary is tight,
  the strict version, and strict monotonicity in the squeezing;
* `entangled_iff_above_threshold` — positive logarithmic negativity `E_N > 0 ↔ r > r_c(n̄)`.

**Honest layering.**  Exact real analysis on the symplectic-eigenvalue formula; the formula
`ν₋ = (n̄+½)e^{−2r}` itself is the standard TMST computation (performed on the covariance
carrier in `SymplecticCovariance`), and the identification of `ν₋ < ½` with entanglement is
the Simon PPT criterion, cited not re-proven.

## References

* R. Simon, *Peres–Horodecki separability criterion for continuous variable systems*,
  Phys. Rev. Lett. **84** (2000) 2726.
* Source: `lean4/QCDVortex/TMST.lean` (own authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal

open Real

-- ─────────────────────────────────────────────────────────────────────────────
-- § Definitions
-- ─────────────────────────────────────────────────────────────────────────────

/-- Mean thermal occupation number n̄(T, ω) = 1 / (exp(ω/T) - 1).
    Returns 0 at T = 0 (continuous extension from above). -/
noncomputable def boseEinstein (T ω : ℝ) : ℝ :=
  if T = 0 then 0 else 1 / (exp (ω / T) - 1)

/-- Minimum symplectic eigenvalue of the partially-transposed covariance matrix
    for a two-mode squeezed thermal state (TMST):

        nu_minus(r, n̄) = (n̄ + ½) · exp(-2r)

    Entanglement criterion (Simon/PPT): nu_minus < ½  ↔  state is entangled.

    Source: `min_symplectic_eigenvalue` in tmst_threshold.py -/
noncomputable def nu_minus (r n_bar : ℝ) : ℝ :=
  (n_bar + 1/2) * exp (-2 * r)

/-- Critical squeezing threshold (Theorem 4.3.1):

        r_c(n̄) = ½ · ln(2·n̄ + 1)

    This is the unique squeezing at which nu_minus = ½.

    Source: `critical_squeezing` in tmst_threshold.py -/
noncomputable def r_c (n_bar : ℝ) : ℝ :=
  (1/2) * log (2 * n_bar + 1)

/-- Logarithmic Negativity for a TMST:

        E_N(r, n̄) = max(0, -log₂(2·nu_minus(r, n̄)))

    where log₂(x) = log(x) / log(2).

    Source: `log_negativity` in tmst_threshold.py -/
noncomputable def E_N (r n_bar : ℝ) : ℝ :=
  max 0 (-(log (2 * nu_minus r n_bar) / log 2))

-- ─────────────────────────────────────────────────────────────────────────────
-- § Supporting lemma
-- ─────────────────────────────────────────────────────────────────────────────

/-- Key identity: exp(-log x) = x⁻¹  for x > 0. -/
private lemma exp_neg_log {x : ℝ} (hx : 0 < x) :
    exp (-(log x)) = x⁻¹ := by
  rw [exp_neg, exp_log hx]

-- ─────────────────────────────────────────────────────────────────────────────
-- § Theorem 4.3.1 (separability boundary)
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Theorem 4.3.1** — Separability boundary for a TMST.

    For n̄ ≥ 0, the following are equivalent:
    * `r ≥ r_c(n̄)` (squeezing meets or exceeds the critical threshold)
    * `nu_minus(r, n̄) ≤ ½`  (Simon/PPT entanglement criterion)

    The proof uses the chain:

        r ≥ ½·log(2n̄+1)
        ↔  exp(-2r) ≤ exp(-log(2n̄+1)) = (2n̄+1)⁻¹     [exp monotone; exp_neg_log]
        ↔  (n̄+½)·exp(-2r) ≤ (n̄+½)/(2n̄+1) = ½         [scale by n̄+½ > 0] -/
theorem theorem_4_3_1 {r n_bar : ℝ} (hn : 0 ≤ n_bar) :
    r ≥ r_c n_bar ↔ nu_minus r n_bar ≤ 1/2 := by
  have h2n1 : (0 : ℝ) < 2 * n_bar + 1 := by linarith
  have hnh  : (0 : ℝ) < n_bar + 1/2   := by linarith
  simp only [r_c, nu_minus, ge_iff_le]
  constructor
  · -- Forward: ½·log(2n̄+1) ≤ r  →  (n̄+½)·exp(-2r) ≤ ½
    intro h
    -- Step 1: exp(-2r) ≤ (2n̄+1)⁻¹
    have h_exp : exp (-2 * r) ≤ (2 * n_bar + 1)⁻¹ := by
      have : (2 * n_bar + 1)⁻¹ = exp (-(log (2 * n_bar + 1))) :=
        (exp_neg_log h2n1).symm
      rw [this, exp_le_exp]
      linarith
    -- Step 2: scale by (n̄+½), then simplify
    calc (n_bar + 1/2) * exp (-2 * r)
        ≤ (n_bar + 1/2) * (2 * n_bar + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left h_exp hnh.le
      _ = 1/2 := by
          field_simp [ne_of_gt h2n1]
  · -- Backward: (n̄+½)·exp(-2r) ≤ ½  →  ½·log(2n̄+1) ≤ r
    intro h
    -- Step 1: show (2n̄+1)·exp(-2r) ≤ 1
    have h_prod : (2 * n_bar + 1) * exp (-2 * r) ≤ 1 := by nlinarith
    have hprod_pos : (0 : ℝ) < (2 * n_bar + 1) * exp (-2 * r) := by positivity
    -- Step 2: take log, then expand
    have h_log : log ((2 * n_bar + 1) * exp (-2 * r)) ≤ 0 := by
      calc _ ≤ log 1 := Real.log_le_log hprod_pos h_prod
           _ = 0     := Real.log_one
    rw [Real.log_mul (ne_of_gt h2n1) (exp_pos _).ne', Real.log_exp] at h_log
    linarith

-- ─────────────────────────────────────────────────────────────────────────────
-- § Corollary: boundary is tight
-- ─────────────────────────────────────────────────────────────────────────────

/-- At the critical threshold the symplectic eigenvalue is exactly ½. -/
theorem nu_at_threshold (n_bar : ℝ) (hn : 0 ≤ n_bar) :
    nu_minus (r_c n_bar) n_bar = 1/2 := by
  have h2n1 : (0 : ℝ) < 2 * n_bar + 1 := by linarith
  simp only [nu_minus, r_c]
  rw [show -2 * ((1/2) * log (2 * n_bar + 1)) = -(log (2 * n_bar + 1)) by ring]
  rw [exp_neg_log h2n1]
  field_simp [ne_of_gt h2n1]

/-- Simple base case: r_c(0) = 0. -/
@[simp]
theorem r_c_zero : r_c 0 = 0 := by
  simp [r_c, log_one]

/-- Simple base case: nu_minus(0, 0) = ½  (vacuum at zero squeezing is on boundary). -/
@[simp]
theorem nu_zero_zero : nu_minus 0 0 = 1/2 := by
  simp [nu_minus, exp_zero]

-- ─────────────────────────────────────────────────────────────────────────────
-- § Corollary: E_N > 0 ↔ r > r_c
-- ─────────────────────────────────────────────────────────────────────────────

/-- nu_minus is strictly positive for n̄ ≥ 0. -/
lemma nu_pos {r n_bar : ℝ} (hn : 0 ≤ n_bar) : 0 < nu_minus r n_bar := by
  simp only [nu_minus]
  exact mul_pos (by linarith) (exp_pos _)

/-- nu_minus is strictly decreasing in r (for n̄ ≥ 0). -/
lemma nu_strictMono_neg_r {n_bar : ℝ} (hn : 0 ≤ n_bar) :
    StrictAntiOn (fun r => nu_minus r n_bar) Set.univ := by
  intro r₁ _ r₂ _ hr
  simp only [nu_minus]
  apply mul_lt_mul_of_pos_left _ (by linarith)
  exact exp_lt_exp.mpr (by linarith)

/-- **Strict version of Theorem 4.3.1**:
    For n̄ ≥ 0,  r > r_c(n̄)  ↔  nu_minus(r, n̄) < ½. -/
theorem theorem_4_3_1_strict {r n_bar : ℝ} (hn : 0 ≤ n_bar) :
    r > r_c n_bar ↔ nu_minus r n_bar < 1/2 := by
  have hnh : (0 : ℝ) < n_bar + 1/2 := by linarith
  constructor
  · -- Forward: r > r_c → nu_minus < ½
    intro h
    rcases lt_or_eq_of_le ((theorem_4_3_1 hn).mp h.le) with hlt | heq
    · exact hlt
    · -- nu_minus(r, n̄) = ½ = nu_minus(r_c, n̄) → r = r_c, contradicts r > r_c
      exfalso
      have hbnd := nu_at_threshold n_bar hn
      have heq2 : nu_minus r n_bar = nu_minus (r_c n_bar) n_bar := heq.trans hbnd.symm
      simp only [nu_minus] at heq2
      have h_exp := mul_left_cancel₀ (ne_of_gt hnh) heq2
      linarith [Real.exp_injective h_exp]
  · -- Backward: nu_minus < ½ → r > r_c
    intro h
    rcases lt_or_eq_of_le ((theorem_4_3_1 hn).mpr h.le) with hlt | heq
    · exact hlt
    · -- r_c = r → nu_minus(r, n̄) = nu_minus(r_c, n̄) = ½, contradicts nu_minus < ½
      exfalso
      have hbnd := nu_at_threshold n_bar hn
      rw [heq] at hbnd  -- nu_minus r n_bar = 1/2
      linarith

/-- **Corollary**: The TMST is entangled (E_N > 0) iff r strictly exceeds r_c.

    Depends on `theorem_4_3_1_strict` (proved modulo function injectivity). -/
theorem entangled_iff_above_threshold {r n_bar : ℝ} (hn : 0 ≤ n_bar) :
    E_N r n_bar > 0 ↔ r > r_c n_bar := by
  have hnu_pos : 0 < nu_minus r n_bar := nu_pos hn
  have h2nu_pos : 0 < 2 * nu_minus r n_bar := by linarith
  have hlog2_pos : 0 < log 2 := log_pos (by norm_num)
  rw [theorem_4_3_1_strict hn]
  simp only [E_N, gt_iff_lt]
  -- Goal: 0 < max 0 (-(log(2nu_minus)/log 2))  ↔  nu_minus < ½
  rw [lt_max_iff]
  simp only [lt_irrefl, false_or]
  constructor
  · -- -log₂(2nu_minus) > 0  →  nu_minus < ½
    intro h
    have hq : log (2 * nu_minus r n_bar) / log 2 < 0 := neg_pos.mp h
    have hlog_neg : log (2 * nu_minus r n_bar) < 0 := by
      rcases div_neg_iff.mp hq with ⟨_, hlt⟩ | ⟨h, _⟩
      · linarith  -- first case: log 2 < 0, contradicts hlog2_pos
      · exact h   -- second case: log(2·nu) < 0 ✓
    have h2nu_lt1 : 2 * nu_minus r n_bar < 1 := by
      by_contra hge
      push Not at hge
      linarith [Real.log_nonneg hge]
    linarith
  · -- nu_minus < ½  →  -log₂(2nu_minus) > 0
    intro h
    rw [neg_pos, div_neg_iff]
    exact Or.inr ⟨Real.log_neg h2nu_pos (by linarith), hlog2_pos⟩

end Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal

end
