/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Thermodynamic cycles — Carnot bound

Phase-5 optional follow-up (B5).  A `CarnotCycle` structure captures the
data of a heat engine running between a hot reservoir `T_h` and a cold
reservoir `T_c` (with `T_c < T_h`), absorbing heat `Q_h > 0` from the
hot reservoir and rejecting `Q_c ≥ 0` to the cold reservoir.  The
**entropy balance** field encodes the second law for the cycle:

  `Q_h · T_c  ≤  Q_c · T_h`

(equivalent to `Q_h / T_h ≤ Q_c / T_c`, the Clausius inequality
specialised to cyclic processes, stated in multiplicative form to
avoid division-of-positivity housekeeping in proofs).

From this single inequality the Carnot efficiency bound follows as
direct algebra:

  `efficiency  =  W / Q_h  =  1 − Q_c/Q_h  ≤  1 − T_c/T_h  =  carnotBound`.

The **equality case** is the reversible Carnot limit, where efficiency
saturates the bound — the frozen-LRF / zero-entropy-production reading.

## Theorems

* **`efficiency_le_carnot_bound` (B5)** — Carnot inequality.
* **`efficiency_eq_carnot_at_reversible`** — equality case at the
  reversible / frozen-LRF limit.
* **`carnotBound_pos`** — the Carnot bound is positive when `T_c < T_h`.

All theorems std-3 clean.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.Cycles

/-- **Carnot-cycle structure.**  A cyclic heat engine between two reservoirs
with the Clausius inequality `Q_h · T_c ≤ Q_c · T_h` (entropy delivered
to cold ≥ entropy absorbed from hot) as a structural field. -/
structure CarnotCycle where
  /-- Hot-reservoir temperature. -/
  T_h : ℝ
  /-- Cold-reservoir temperature. -/
  T_c : ℝ
  /-- Heat absorbed from the hot reservoir per cycle. -/
  Q_h : ℝ
  /-- Heat rejected to the cold reservoir per cycle. -/
  Q_c : ℝ
  /-- Hot reservoir is hotter than cold. -/
  T_c_lt_T_h : T_c < T_h
  /-- Cold temperature is positive. -/
  T_c_pos : 0 < T_c
  /-- Heat absorbed is positive. -/
  Q_h_pos : 0 < Q_h
  /-- Heat rejected is non-negative. -/
  Q_c_nonneg : 0 ≤ Q_c
  /-- **Clausius inequality for cycles** (multiplicative form). -/
  entropy_balance : Q_h * T_c ≤ Q_c * T_h

namespace CarnotCycle

variable (C : CarnotCycle)

/-- Hot temperature is positive. -/
theorem T_h_pos : 0 < C.T_h := lt_trans C.T_c_pos C.T_c_lt_T_h

/-- **Work done per cycle**: `W = Q_h − Q_c`. -/
def workDone : ℝ := C.Q_h - C.Q_c

/-- **Cycle efficiency**: `η = W / Q_h`. -/
def efficiency : ℝ := C.workDone / C.Q_h

/-- **Carnot bound**: the maximum efficiency, `η_max = 1 − T_c/T_h`. -/
def carnotBound : ℝ := 1 - C.T_c / C.T_h

theorem efficiency_eq_one_minus_ratio :
    C.efficiency = 1 - C.Q_c / C.Q_h := by
  unfold efficiency workDone
  have hQh : C.Q_h ≠ 0 := ne_of_gt C.Q_h_pos
  field_simp

/-- The Carnot bound is strictly positive when `T_c < T_h`. -/
theorem carnotBound_pos : 0 < C.carnotBound := by
  unfold carnotBound
  have hTh : 0 < C.T_h := C.T_h_pos
  have : C.T_c / C.T_h < 1 := by
    rw [div_lt_one hTh]
    exact C.T_c_lt_T_h
  linarith

/-- **B5 — Carnot efficiency bound.**  The cycle's efficiency is at
most the Carnot bound `1 − T_c/T_h`.  Direct algebraic consequence of
the (multiplicative) Clausius inequality `Q_h · T_c ≤ Q_c · T_h`. -/
theorem efficiency_le_carnot_bound : C.efficiency ≤ C.carnotBound := by
  rw [C.efficiency_eq_one_minus_ratio]
  unfold carnotBound
  -- Goal: 1 − Q_c/Q_h ≤ 1 − T_c/T_h, i.e., T_c/T_h ≤ Q_c/Q_h.
  have hTh : 0 < C.T_h := C.T_h_pos
  have hQh : 0 < C.Q_h := C.Q_h_pos
  have hkey : C.T_c / C.T_h ≤ C.Q_c / C.Q_h := by
    rw [div_le_div_iff₀ hTh hQh]
    -- Goal: T_c * Q_h ≤ Q_c * T_h.
    -- From entropy_balance: Q_h * T_c ≤ Q_c * T_h.
    have h := C.entropy_balance
    linarith
  linarith

/-- **Equality case at the reversible Carnot cycle.**  When the
entropy-balance inequality holds with equality (`Q_h · T_c = Q_c · T_h`),
the cycle is reversible and its efficiency *saturates* the Carnot
bound. -/
theorem efficiency_eq_carnot_at_reversible
    (h_rev : C.Q_h * C.T_c = C.Q_c * C.T_h) :
    C.efficiency = C.carnotBound := by
  rw [C.efficiency_eq_one_minus_ratio]
  unfold carnotBound
  have hTh : 0 < C.T_h := C.T_h_pos
  have hQh : 0 < C.Q_h := C.Q_h_pos
  have hkey : C.T_c / C.T_h = C.Q_c / C.Q_h := by
    field_simp
    linarith
  linarith

/-- **iff strengthening**: efficiency equals the Carnot bound iff the
cycle is reversible. -/
theorem efficiency_eq_carnot_iff_reversible :
    C.efficiency = C.carnotBound ↔ C.Q_h * C.T_c = C.Q_c * C.T_h := by
  have hTh : 0 < C.T_h := C.T_h_pos
  have hQh : 0 < C.Q_h := C.Q_h_pos
  have hTh_ne : C.T_h ≠ 0 := ne_of_gt hTh
  have hQh_ne : C.Q_h ≠ 0 := ne_of_gt hQh
  constructor
  · intro hEff
    rw [C.efficiency_eq_one_minus_ratio] at hEff
    unfold carnotBound at hEff
    have hratio : C.Q_c / C.Q_h = C.T_c / C.T_h := by linarith
    -- multiply both sides by Q_h * T_h to clear denominators
    have : C.Q_c * C.T_h = C.T_c * C.Q_h := by
      have := hratio
      field_simp at this
      linarith
    linarith
  · intro hEq
    exact C.efficiency_eq_carnot_at_reversible hEq

end CarnotCycle

end Physlib.Thermodynamics.Cycles

end
