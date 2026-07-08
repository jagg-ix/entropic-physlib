/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.HyperbolicBoost
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Bell ↔ hyperbolic-regime classification

A scalar representative for the **Bell ↔ hyperbolic-eccentricity** correspondence
of the entropic statistical framework: an eccentricity-parameterised
classification of Bell regimes (`classical | parabolic | hyperbolic` by
`e <, =, > 1`) plus the scalar **entropy-production rate**
`S[e] = e² − 1` along a hyperbolic trajectory.

The eccentricity structure is `Physlib.Relativity.Special.HyperbolicOrbit`
(the GR escape orbit at `e > 1`); the Bell-regime correspondence reads
the same `e` as a correlation-length parameter, with `e > 1` the open /
decoherent (Bell-violating) regime.

## Contents

* `entropyProductionRate e = e² − 1` with the load-bearing characterisation
  `0 ≤ entropyProductionRate e ↔ e ≤ −1 ∨ 1 ≤ e`.
* `BellRegime` — inductive `classical | parabolic | hyperbolic`.
* `regimeOfEccentricity` — selector by `e <, =, > 1`.
* `regime_classical_iff` / `regime_parabolic_iff` / `regime_hyperbolic_iff`
  — dichotomy theorems.
* `orbit_is_hyperbolicRegime` — the existing `HyperbolicOrbit` structure
  (with `e > 1`) lands in the hyperbolic Bell regime.

Tsirelson's `|S_CHSH| ≤ 2√2` is **not** included as a structure field — its
derivation requires QM operator-algebra machinery beyond this scalar layer.


## References

- **Bell 1964** — *On the Einstein-Podolsky-Rosen paradox*
- **Grosche 1993** — *Path integrals, hyperbolic spaces, Selberg trace formulae*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Bell

open Physlib.Relativity.Special

/-! ## §1 — Entropy-production rate `S[e] = e² − 1` -/

/-- **Entropy-production rate along a hyperbolic trajectory**:
`S[e] = e² − 1`.  Vanishes at `e = ±1` (parabolic boundary), positive in
the hyperbolic regime `|e| > 1`. -/
def entropyProductionRate (e : ℝ) : ℝ := e ^ 2 - 1

/-- **Entropy-production rate non-negativity iff** the eccentricity is
out of the elliptic range: `0 ≤ S[e] ↔ e ≤ −1 ∨ 1 ≤ e`. -/
theorem entropyProductionRate_nonneg_iff (e : ℝ) :
    0 ≤ entropyProductionRate e ↔ e ≤ -1 ∨ 1 ≤ e := by
  unfold entropyProductionRate
  constructor
  · intro h
    by_contra hc
    have ⟨h1, h2⟩ : -1 < e ∧ e < 1 := by
      refine ⟨?_, ?_⟩ <;> by_contra hk
      · exact hc (Or.inl (not_lt.mp hk))
      · exact hc (Or.inr (not_lt.mp hk))
    nlinarith
  · rintro (h | h)
    · nlinarith
    · nlinarith

/-- For `1 ≤ e` (in particular the hyperbolic regime `e > 1`), the
entropy-production rate is non-negative. -/
theorem entropyProductionRate_nonneg_of_e_ge_one
    (e : ℝ) (h : 1 ≤ e) : 0 ≤ entropyProductionRate e :=
  (entropyProductionRate_nonneg_iff e).mpr (Or.inr h)

/-- For the strict hyperbolic regime `e > 1`, the entropy-production rate
is strictly positive. -/
theorem entropyProductionRate_pos_of_e_gt_one
    (e : ℝ) (h : 1 < e) : 0 < entropyProductionRate e := by
  unfold entropyProductionRate
  nlinarith

/-- At `e = 1` the entropy-production rate vanishes. -/
theorem entropyProductionRate_at_one : entropyProductionRate 1 = 0 := by
  unfold entropyProductionRate; norm_num

/-- At `e = −1` the entropy-production rate vanishes. -/
theorem entropyProductionRate_at_neg_one : entropyProductionRate (-1) = 0 := by
  unfold entropyProductionRate; norm_num

/-! ## §2 — Bell regime classification -/

/-- **Bell regime by eccentricity.**

* `classical` — `e < 1` (elliptic, local-realistic-bounded);
* `parabolic` — `e = 1` (saturation boundary);
* `hyperbolic` — `e > 1` (open / decoherent / Bell-violating). -/
inductive BellRegime
  | classical
  | parabolic
  | hyperbolic
  deriving DecidableEq, Repr

/-- Regime selector by eccentricity range. -/
noncomputable def regimeOfEccentricity (e : ℝ) : BellRegime :=
  if e < 1 then BellRegime.classical
  else if e = 1 then BellRegime.parabolic
  else BellRegime.hyperbolic

/-- Classical regime ↔ `e < 1`. -/
theorem regime_classical_iff (e : ℝ) :
    regimeOfEccentricity e = BellRegime.classical ↔ e < 1 := by
  unfold regimeOfEccentricity
  split_ifs with h1 h2
  · exact iff_of_true rfl h1
  · exact iff_of_false (by simp) (by linarith)
  · exact iff_of_false (by simp) h1

/-- Parabolic regime ↔ `e = 1`. -/
theorem regime_parabolic_iff (e : ℝ) :
    regimeOfEccentricity e = BellRegime.parabolic ↔ e = 1 := by
  unfold regimeOfEccentricity
  split_ifs with h1 h2
  · exact iff_of_false (by simp) (by linarith)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by simp) h2

/-- Hyperbolic regime ↔ `1 < e`. -/
theorem regime_hyperbolic_iff (e : ℝ) :
    regimeOfEccentricity e = BellRegime.hyperbolic ↔ 1 < e := by
  unfold regimeOfEccentricity
  split_ifs with h1 h2
  · exact iff_of_false (by simp) (by linarith)
  · exact iff_of_false (by simp) (by linarith)
  · refine iff_of_true rfl ?_
    have h1' : 1 ≤ e := not_lt.mp h1
    exact lt_of_le_of_ne h1' (Ne.symm h2)

/-! ## §3 — `HyperbolicOrbit` lands in the hyperbolic Bell regime -/

/-- **Cross-domain link**: a `HyperbolicOrbit` (GR escape orbit with
`e > 1`) lands in the **hyperbolic Bell regime** under the
eccentricity → Bell-regime classification. -/
theorem orbit_is_hyperbolicRegime (O : HyperbolicOrbit) :
    regimeOfEccentricity O.e = BellRegime.hyperbolic :=
  (regime_hyperbolic_iff O.e).mpr O.e_gt_one

/-- A `HyperbolicOrbit` has strictly positive entropy production. -/
theorem orbit_entropyProductionRate_pos (O : HyperbolicOrbit) :
    0 < entropyProductionRate O.e :=
  entropyProductionRate_pos_of_e_gt_one O.e O.e_gt_one

end Physlib.QuantumMechanics.Bell

end
