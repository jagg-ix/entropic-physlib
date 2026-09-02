/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal

/-!
# The entanglement temperature threshold of a squeezed thermal state

Ports `lean4/QCDVortex/ThresholdTemp.lean` of the qcd-vortex-entanglement tree (Lean layer
own authorship; Martín Alonso, Zenodo 10.5281/zenodo.18353640): the dual thresholds of
`TwoModeSqueezedThermal.theorem_4_3_1` in the thermal variables.

* `n_c r = (e^{2r} − 1)/2`, `T_c r ω = ω / log((e^{2r}+1)/(e^{2r}−1))` — critical occupation
  and critical temperature; `r_c_n_c`/`n_c_r_c` prove `r_c` and `n_c` are mutual inverses;
* `entangled_iff_below_nc` — `E_N > 0 ↔ n̄ < n_c(r)` (the occupation dual of the squeezing
  threshold);
* `boseEinstein_lt_nc` — the Bose–Einstein occupation crosses `n_c` exactly at `T_c`
  (the substantive cross-multiplication/log chain);
* `entanglement_temperature_threshold` — `E_N(r, n̄(T,ω)) > 0 ↔ T < T_c(r,ω)`: a squeezed
  thermal mode pair stays entangled exactly below the critical temperature.

**Honest layering.**  Exact real analysis; physical readings as in the parent module.

## References

* Source: `lean4/QCDVortex/ThresholdTemp.lean` (own authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.GaussianEntanglement.EntanglementTemperatureThreshold

open Real Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal

-- ─────────────────────────────────────────────────────────────────────────────
-- § Definitions
-- ─────────────────────────────────────────────────────────────────────────────

/-- Critical thermal occupation at squeezing r:
        n_c(r) = (exp(2r) - 1) / 2
    This is the unique n̄ ≥ 0 satisfying r_c(n̄) = r (for r ≥ 0).
    The TMST is entangled iff n̄ < n_c(r). -/
noncomputable def n_c (r : ℝ) : ℝ := (exp (2 * r) - 1) / 2

/-- Critical temperature at squeezing r and mode frequency ω:
        T_c(r, ω) = ω / log((exp(2r)+1)/(exp(2r)-1))
    The TMST is entangled iff T < T_c (for r > 0, ω > 0, T > 0). -/
noncomputable def T_c (r ω : ℝ) : ℝ :=
  ω / log ((exp (2 * r) + 1) / (exp (2 * r) - 1))

-- ─────────────────────────────────────────────────────────────────────────────
-- § Supporting lemmas
-- ─────────────────────────────────────────────────────────────────────────────

/-- For r > 0, exp(2r) > 1, so n_c(r) > 0. -/
lemma n_c_pos {r : ℝ} (hr : 0 < r) : 0 < n_c r := by
  simp only [n_c]
  have : 1 < exp (2 * r) := by
    calc (1 : ℝ) = exp 0 := (exp_zero).symm
      _ < exp (2 * r) := exp_lt_exp.mpr (by linarith)
  linarith

/-- n_c is the dual of r_c: r_c(n_c(r)) = r for r ≥ 0. -/
lemma r_c_n_c (r : ℝ) : r_c (n_c r) = r := by
  simp only [r_c, n_c]
  rw [show 2 * ((exp (2 * r) - 1) / 2) + 1 = exp (2 * r) by ring]
  rw [Real.log_exp]
  ring

/-- n_c is the dual of r_c: n_c(r_c(n̄)) = n̄ for n̄ ≥ 0. -/
lemma n_c_r_c {n_bar : ℝ} (hn : 0 ≤ n_bar) : n_c (r_c n_bar) = n_bar := by
  simp only [n_c, r_c]
  have h2n1 : (0 : ℝ) < 2 * n_bar + 1 := by linarith
  rw [show 2 * ((1/2) * log (2 * n_bar + 1)) = log (2 * n_bar + 1) by ring]
  rw [exp_log h2n1]
  ring

/-- For r > 0, the fraction (exp(2r)+1)/(exp(2r)-1) > 1, so log > 0. -/
lemma log_T_c_denom_pos {r : ℝ} (hr : 0 < r) :
    0 < log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) := by
  apply Real.log_pos
  have hexp : 1 < exp (2 * r) := by
    rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  have hA1 : 0 < exp (2 * r) - 1 := by linarith
  have h2 : 0 < 2 / (exp (2 * r) - 1) := div_pos two_pos hA1
  linarith [show (exp (2 * r) + 1) / (exp (2 * r) - 1) =
            1 + 2 / (exp (2 * r) - 1) from by field_simp; ring]

/-- For r > 0 and ω > 0, T_c > 0. -/
lemma T_c_pos {r ω : ℝ} (hr : 0 < r) (hω : 0 < ω) : 0 < T_c r ω := by
  simp only [T_c]
  exact div_pos hω (log_T_c_denom_pos hr)

/-- Bose-Einstein at T > 0 equals 1/(exp(ω/T)-1) (drops the if-branch). -/
lemma boseEinstein_eq_of_pos {T ω : ℝ} (hT : 0 < T) :
    boseEinstein T ω = 1 / (exp (ω / T) - 1) := by
  simp [boseEinstein, ne_of_gt hT]

/-- For ω > 0 and T > 0, exp(ω/T) > 1, so the denominator is positive. -/
lemma exp_omega_T_gt_one {T ω : ℝ} (hT : 0 < T) (hω : 0 < ω) :
    1 < exp (ω / T) := by
  rw [← exp_zero]
  exact exp_lt_exp.mpr (by positivity)

/-- For ω > 0 and T > 0, boseEinstein T ω > 0. -/
lemma boseEinstein_pos {T ω : ℝ} (hT : 0 < T) (hω : 0 < ω) :
    0 < boseEinstein T ω := by
  rw [boseEinstein_eq_of_pos hT]
  apply div_pos one_pos
  linarith [exp_omega_T_gt_one hT hω]

-- ─────────────────────────────────────────────────────────────────────────────
-- § n-bar threshold (dual of Theorem 4.3.1)
-- ─────────────────────────────────────────────────────────────────────────────

/-- **n̄-threshold** (dual perspective on entanglement):
    For r > 0 and n̄ ≥ 0, the TMST is entangled iff n̄ < n_c(r).

    Proof sketch:
        E_N > 0  ↔  r > r_c(n̄)
                 ↔  r > ½·log(2n̄+1)
                 ↔  2r > log(2n̄+1)
                 ↔  exp(2r) > 2n̄+1    [exp monotone]
                 ↔  n̄ < (exp(2r)-1)/2 = n_c(r) -/
theorem entangled_iff_below_nc {r n_bar : ℝ} (hn : 0 ≤ n_bar) :
    E_N r n_bar > 0 ↔ n_bar < n_c r := by
  rw [entangled_iff_above_threshold hn]
  simp only [r_c, n_c, gt_iff_lt]
  have h2n1 : (0 : ℝ) < 2 * n_bar + 1 := by linarith
  constructor
  · -- r > ½·log(2n̄+1) → n̄ < (exp(2r)-1)/2
    intro h
    have hlog : log (2 * n_bar + 1) < 2 * r := by linarith
    have hexp : 2 * n_bar + 1 < exp (2 * r) := by
      calc 2 * n_bar + 1
          = exp (log (2 * n_bar + 1)) := (exp_log h2n1).symm
        _ < exp (2 * r)               := exp_lt_exp.mpr hlog
    linarith
  · -- n̄ < (exp(2r)-1)/2 → r > ½·log(2n̄+1)
    intro h
    have hexp : 2 * n_bar + 1 < exp (2 * r) := by linarith
    have hlog : log (2 * n_bar + 1) < 2 * r := by
      calc log (2 * n_bar + 1)
          < log (exp (2 * r)) := Real.log_lt_log h2n1 hexp
        _ = 2 * r             := Real.log_exp _
    linarith

-- ─────────────────────────────────────────────────────────────────────────────
-- § Temperature threshold
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Temperature threshold**:
    For T > 0, r > 0, ω > 0: n̄(T, ω) < n_c(r)  ↔  T < T_c(r, ω).

    Proof sketch (let A = exp(2r)):
        1/(exp(ω/T)-1) < (A-1)/2
        ↔  2 < (A-1)·(exp(ω/T)-1)          [mult by 2·(exp(ω/T)-1) > 0]
        ↔  (A+1)/(A-1) < exp(ω/T)           [rearrange: 2/(A-1)+1 = (A+1)/(A-1)]
        ↔  log((A+1)/(A-1)) < ω/T           [log monotone; (A+1)/(A-1) > 1]
        ↔  T < ω/log((A+1)/(A-1)) = T_c     [mult by T > 0, divide by log > 0] -/
theorem boseEinstein_lt_nc {T r ω : ℝ} (hT : 0 < T) (hr : 0 < r) (hω : 0 < ω) :
    boseEinstein T ω < n_c r ↔ T < T_c r ω := by
  have hA  : (1 : ℝ) < exp (2 * r) := by
    rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  have hA1 : (0 : ℝ) < exp (2 * r) - 1 := by linarith
  have hfrac : (1 : ℝ) < (exp (2 * r) + 1) / (exp (2 * r) - 1) := by
    have h2 : 0 < 2 / (exp (2 * r) - 1) := div_pos two_pos hA1
    linarith [show (exp (2 * r) + 1) / (exp (2 * r) - 1) =
              1 + 2 / (exp (2 * r) - 1) from by field_simp [ne_of_gt hA1]; ring]
  have hlog_pos : 0 < log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) :=
    Real.log_pos hfrac
  have hET : 0 < exp (ω / T) - 1 := by linarith [exp_omega_T_gt_one hT hω]
  rw [boseEinstein_eq_of_pos hT]
  simp only [n_c, T_c]
  -- Goal: 1/(exp(ω/T)-1) < (exp(2r)-1)/2  ↔  T < ω/log(...)
  -- Local abbreviations for readability (used inline, not as tactic)
  -- A = exp(2r)-1 > 0,  E = exp(ω/T)-1 > 0,  L = log((exp(2r)+1)/(exp(2r)-1)) > 0
  constructor
  · -- Forward: 1/E < A/2  →  T < ω/L
    intro h
    -- 1. 2 < A * E  (cross-multiply h by E)
    have hmul : 2 < (exp (2 * r) - 1) * (exp (ω / T) - 1) := by
      have hm := mul_lt_mul_of_pos_right h hET
      -- hm : 1/(exp(ω/T)-1) * (exp(ω/T)-1) < (exp(2r)-1)/2 * (exp(ω/T)-1)
      have hs1 : 1 / (exp (ω / T) - 1) * (exp (ω / T) - 1) = 1 := by
        field_simp [ne_of_gt hET]
      rw [hs1] at hm  -- hm : 1 < (exp(2r)-1)/2 * (exp(ω/T)-1)
      have heq : (exp (2 * r) - 1) * (exp (ω / T) - 1) =
                 2 * ((exp (2 * r) - 1) / 2 * (exp (ω / T) - 1)) := by ring
      linarith
    -- 2. (exp(2r)+1)/(exp(2r)-1) < exp(ω/T)  from: A+1 < exp(ω/T)*(A-1), mult by (A-1)⁻¹
    have hineq : (exp (2 * r) + 1) / (exp (2 * r) - 1) < exp (ω / T) := by
      have hprod : exp (2 * r) + 1 < exp (ω / T) * (exp (2 * r) - 1) := by nlinarith
      have step := mul_lt_mul_of_pos_right hprod (inv_pos.mpr hA1)
      rw [show (exp (2 * r) + 1) * (exp (2 * r) - 1)⁻¹ =
              (exp (2 * r) + 1) / (exp (2 * r) - 1) from (div_eq_mul_inv _ _).symm,
          show exp (ω / T) * (exp (2 * r) - 1) * (exp (2 * r) - 1)⁻¹ = exp (ω / T) from by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hA1), mul_one]] at step
      exact step
    -- 3. log(...) < ω/T
    have hlog_ineq : log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) < ω / T :=
      calc log ((exp (2 * r) + 1) / (exp (2 * r) - 1))
          < log (exp (ω / T)) := Real.log_lt_log (by linarith) hineq
        _ = ω / T             := Real.log_exp _
    -- 4. T * log < ω
    have hTlog : T * log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) < ω := by
      have hm2 := mul_lt_mul_of_pos_left hlog_ineq hT
      -- hm2 : T * log < T * (ω/T)
      have hs3 : T * (ω / T) = ω := by field_simp [ne_of_gt hT]
      linarith
    -- 5. T < ω / log
    have step5 := mul_lt_mul_of_pos_right hTlog (inv_pos.mpr hlog_pos)
    -- step5 : T * L * L⁻¹ < ω * L⁻¹
    rw [show (T * log ((exp (2 * r) + 1) / (exp (2 * r) - 1))) *
            (log ((exp (2 * r) + 1) / (exp (2 * r) - 1)))⁻¹ =
            T from by field_simp [ne_of_gt hlog_pos],
        show ω * (log ((exp (2 * r) + 1) / (exp (2 * r) - 1)))⁻¹ =
             ω / log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) from
             (div_eq_mul_inv ω _).symm] at step5
    exact step5
  · -- Backward: T < ω/L  →  1/E < A/2
    intro h
    -- 1. T * log < ω  (from T < ω/L, multiply by L)
    have hTlog : T * log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) < ω := by
      have hm3 := mul_lt_mul_of_pos_right h hlog_pos
      -- hm3 : T * L < (ω/L) * L
      have hs4 : ω / log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) *
                 log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) = ω := by
        field_simp [ne_of_gt hlog_pos]
      linarith
    -- 2. log < ω/T  (from T*L < ω, multiply by T⁻¹)
    have hlog_lt : log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) < ω / T := by
      have step2 := mul_lt_mul_of_pos_right hTlog (inv_pos.mpr hT)
      -- step2 : T * L * T⁻¹ < ω * T⁻¹
      rw [show (T * log ((exp (2 * r) + 1) / (exp (2 * r) - 1))) * T⁻¹ =
              log ((exp (2 * r) + 1) / (exp (2 * r) - 1)) from by
              field_simp [ne_of_gt hT],
          show ω * T⁻¹ = ω / T from (div_eq_mul_inv ω T).symm] at step2
      exact step2
    -- 3. (exp(2r)+1)/(exp(2r)-1) < exp(ω/T)
    have hfrac_lt : (exp (2 * r) + 1) / (exp (2 * r) - 1) < exp (ω / T) :=
      calc _ = exp (log ((exp (2 * r) + 1) / (exp (2 * r) - 1))) :=
              (Real.exp_log (div_pos (by linarith [exp_pos (2*r)]) hA1)).symm
        _ < exp (ω / T) := exp_lt_exp.mpr hlog_lt
    -- 4. 2 < A*E  (from A+2 < F*A, i.e., hfrac_lt)
    have hmul : 2 < (exp (2 * r) - 1) * (exp (ω / T) - 1) := by
      have hs8 : (exp (2 * r) + 1) / (exp (2 * r) - 1) * (exp (2 * r) - 1) =
                 exp (2 * r) + 1 := by field_simp [ne_of_gt hA1]
      have hm4 := mul_lt_mul_of_pos_right hfrac_lt hA1
      -- hm4: (exp(2r)+1)/(exp(2r)-1) * (exp(2r)-1) < exp(ω/T) * (exp(2r)-1)
      -- i.e., exp(2r)+1 < exp(ω/T) * (exp(2r)-1)
      nlinarith [hm4, hs8, mul_pos hA1 hET]
    -- 5. 1/E < A/2: multiply h9 : 1 < (A/2)*E by (1/E) > 0, then simplify
    have h9 : 1 < (exp (2 * r) - 1) / 2 * (exp (ω / T) - 1) := by
      have : (exp (2 * r) - 1) * (exp (ω / T) - 1) =
             2 * ((exp (2 * r) - 1) / 2 * (exp (ω / T) - 1)) := by ring
      linarith
    have hEdiv_pos : 0 < 1 / (exp (ω / T) - 1) := div_pos one_pos hET
    have hfinal := mul_lt_mul_of_pos_right h9 hEdiv_pos
    -- hfinal : 1 * (1/E) < (A/2) * E * (1/E)
    have hrhs : (exp (2 * r) - 1) / 2 * (exp (ω / T) - 1) * (1 / (exp (ω / T) - 1)) =
                (exp (2 * r) - 1) / 2 := by field_simp [ne_of_gt hET]
    linarith [one_mul (1 / (exp (ω / T) - 1))]

-- ─────────────────────────────────────────────────────────────────────────────
-- § Main corollary: entanglement ↔ T < T_c
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Entanglement temperature threshold** (Corollary of Theorem 4.3.1):

    For r > 0, ω > 0, T > 0:
        E_N(r, n̄(T,ω)) > 0  ↔  T < T_c(r,ω).

    The TMST is entangled if and only if the temperature is below the
    critical temperature T_c(r, ω) = ω / log((exp(2r)+1)/(exp(2r)-1)). -/
theorem entanglement_temperature_threshold {r ω T : ℝ}
    (hr : 0 < r) (hω : 0 < ω) (hT : 0 < T) :
    E_N r (boseEinstein T ω) > 0 ↔ T < T_c r ω := by
  have hn : 0 ≤ boseEinstein T ω := le_of_lt (boseEinstein_pos hT hω)
  rw [entangled_iff_below_nc hn]
  exact boseEinstein_lt_nc hT hr hω

-- ─────────────────────────────────────────────────────────────────────────────
-- § Simple checks
-- ─────────────────────────────────────────────────────────────────────────────

/-- n_c(0) = 0: at zero squeezing the only entangled state is n̄ = −ε < 0,
    which is unphysical (vacuum is on the boundary). -/
@[simp]
theorem n_c_zero : n_c 0 = 0 := by simp [n_c]

end Physlib.QuantumMechanics.GaussianEntanglement.EntanglementTemperatureThreshold

end
