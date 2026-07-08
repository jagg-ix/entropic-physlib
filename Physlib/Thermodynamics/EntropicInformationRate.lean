/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Landauer information rate from entropic rate (Eq 43)

Port of equation (43) from
`entropic-time/.../CAT_EPT_Extended_Part2.wl`:

  `dI/dt = λ / ln 2`

where `λ` is the entropy-production rate (in nats per unit time)
and `I` is the information (in bits per unit time).

This is the **Landauer information conversion**: entropy in nats
(units of `k_B`) is converted to information in bits by dividing
by `ln 2`.

## Derivation chain (Wolfram source)

* `dS_gen/dt = k_B · λ` (entropy production rate in J/K per unit
  time).
* `I = S / (k_B · ln 2)` (Landauer's bit-entropy bridge).
* Combining: `dI/dt = (k_B · λ) / (k_B · ln 2) = λ / ln 2`.

## Contents

* `landauerInfoRate lam := lam / Real.log 2` — Eq (43).
* `landauerInfoRate_eq` — definitional.
* `landauerInfoRate_pos` — positivity at positive `λ`.
* `landauerInfoRate_chainRule` — the derivation
  `(k_B · λ) / (k_B · ln 2) = λ / ln 2`.

## Cross-references

* physlib's existing `Physlib/Thermodynamics/Landauer.lean` —
  Landauer bound `E_erase ≥ k_B · T · ln 2`.
* `Physlib/Thermodynamics/LandauerShannonDuality.lean` —
  entropy-information duality.
* `QuantumInertialFrame.entropicRate` — the QIF entropic rate `λ`
  per unit coordinate time.


## References

* Landauer 1961 — *Irreversibility and heat generation in the
  computing process*, IBM J. Res. Dev. 5, 183.
* Shannon 1948 — *A mathematical theory of communication*, Bell
  Syst. Tech. J. 27, 379.  Information in bits per symbol.
* `entropic-time/.../CAT_EPT_Extended_Part2.wl` Eq (43).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

/-! ## §1 — Landauer information rate -/

/-- **Landauer information rate** (Eq 43):

  `dI/dt := λ / ln 2`.

Converts the entropy-production rate `λ` (in nats per unit time)
to the information rate (in bits per unit time) by dividing by
`ln 2 ≈ 0.693`.

This is the Landauer / Shannon conversion: `1 nat = (1/ln 2) bits`. -/
def landauerInfoRate (lam : ℝ) : ℝ := lam / Real.log 2

/-- Definitional unfolding of `landauerInfoRate`. -/
theorem landauerInfoRate_def (lam : ℝ) :
    landauerInfoRate lam = lam / Real.log 2 := rfl

/-! ## §2 — Positivity -/

/-- `ln 2 > 0`. -/
theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

/-- **The Landauer information rate is positive** at positive entropy
production rate. -/
theorem landauerInfoRate_pos {lam : ℝ} (h : 0 < lam) :
    0 < landauerInfoRate lam := by
  unfold landauerInfoRate
  exact div_pos h log_two_pos

/-! ## §3 — Chain rule derivation (Eq 43 content) -/

/-- **Chain rule derivation** of `dI/dt = λ/ln 2`:

  `dI/dt = (dS_gen/dt) / (k_B · ln 2) = (k_B · λ) / (k_B · ln 2) =
  λ / ln 2`.

At positive Boltzmann constant `k_B`, the `k_B`-factor cancels and
the information rate depends only on the entropy production rate. -/
theorem landauerInfoRate_chainRule
    {kB lam : ℝ} (hkB : 0 < kB) :
    (kB * lam) / (kB * Real.log 2) = landauerInfoRate lam := by
  unfold landauerInfoRate
  have hkB_ne : kB ≠ 0 := ne_of_gt hkB
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  field_simp

end Physlib.Thermodynamics

end
