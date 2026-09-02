/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

/-!
# Sciama–Candelas–Deutsch Appendix C: the Minkowski vacuum is thermal in the Fulling quantization

Appendix C ("Thermal relationship between the Minkowski and Fulling vacua") derives, via a Bogoliubov
transformation, that the Minkowski vacuum contains a *thermal* distribution of Fulling (Rindler) quanta.  The
analytic Minkowski modes (C8) `v_ν = [1 − e^{−2πν}]^{−1/2}(u^{+}_ν + e^{−πν}u^{−}_ν*)` give the Bogoliubov
transformation (C11)

`b̂_ν = [1 − e^{−2πν}]^{−1/2}(â_ν − e^{−πν} â_ν†)`,

so the Minkowski annihilation operator is `α_ν â − β_ν â†` with

`α_ν = [1 − e^{−2πν}]^{−1/2},   β_ν = e^{−πν}[1 − e^{−2πν}]^{−1/2}`.

The Minkowski vacuum is then a two-mode squeezed (thermofield-double) state `|M⟩ ∝ ∏ Σ_n e^{−πnν}|n⟩^{+}|n⟩^{−}`
(C14), and expectation values are a thermal trace `⟨M|Ô|M⟩ = Tr(ρ_{2π/κ}Ô)` (C16).  The c-number core:

* `bogoliubovAlpha`, `bogoliubovBeta` — the coefficients.
* `bogoliubov_normalization` — `|α_ν|² − |β_ν|² = 1` (canonical commutation / unitarity).
* `bogoliubov_beta_sq_thermal` — `|β_ν|² = n(ν) = 1/(e^{2πν} − 1)`: the Fulling-particle content of the
  Minkowski vacuum is the **Bose–Einstein occupation at the Unruh temperature** `β = 2π`.
* `bogoliubov_detailedBalance` — `|β_ν|²/|α_ν|² = e^{−2πν}` (the Boltzmann factor).

Honest scope: the c-number Bogoliubov coefficients, their normalization, and the thermal occupation; the
Fock-space thermofield-double state (C14) and density-matrix trace (C16) are contextualized, not built.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaMinkowskiFullingBogoliubov

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

/-- **The Bogoliubov coefficient** `α_ν = [1 − e^{−2πν}]^{−1/2}` (C11). -/
def bogoliubovAlpha (ν : ℝ) : ℝ := 1 / Real.sqrt (1 - Real.exp (-(2 * Real.pi * ν)))

/-- **The Bogoliubov coefficient** `β_ν = e^{−πν}[1 − e^{−2πν}]^{−1/2}` (C11). -/
def bogoliubovBeta (ν : ℝ) : ℝ :=
  Real.exp (-(Real.pi * ν)) / Real.sqrt (1 - Real.exp (-(2 * Real.pi * ν)))

/-- `1 − e^{−2πν} > 0` for `ν > 0`. -/
theorem one_sub_exp_pos (ν : ℝ) (hν : 0 < ν) : 0 < 1 - Real.exp (-(2 * Real.pi * ν)) := by
  have h : Real.exp (-(2 * Real.pi * ν)) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have : 0 < 2 * Real.pi * ν := by positivity
    linarith
  linarith

/-- `α_ν² = 1/(1 − e^{−2πν})`. -/
theorem bogoliubovAlpha_sq (ν : ℝ) (hν : 0 < ν) :
    bogoliubovAlpha ν ^ 2 = 1 / (1 - Real.exp (-(2 * Real.pi * ν))) := by
  unfold bogoliubovAlpha
  rw [div_pow, one_pow, Real.sq_sqrt (one_sub_exp_pos ν hν).le]

/-- `β_ν² = e^{−2πν}/(1 − e^{−2πν})`. -/
theorem bogoliubovBeta_sq (ν : ℝ) (hν : 0 < ν) :
    bogoliubovBeta ν ^ 2 = Real.exp (-(2 * Real.pi * ν)) / (1 - Real.exp (-(2 * Real.pi * ν))) := by
  unfold bogoliubovBeta
  rw [div_pow, Real.sq_sqrt (one_sub_exp_pos ν hν).le,
    show Real.exp (-(Real.pi * ν)) ^ 2 = Real.exp (-(2 * Real.pi * ν)) from by
      rw [sq, ← Real.exp_add]; ring_nf]

/-- **[Bogoliubov normalization] `|α_ν|² − |β_ν|² = 1`.**  The canonical commutation / unitarity of the
transformation — the analogue of `cosh² − sinh² = 1` for the squeezing. -/
theorem bogoliubov_normalization (ν : ℝ) (hν : 0 < ν) :
    bogoliubovAlpha ν ^ 2 - bogoliubovBeta ν ^ 2 = 1 := by
  rw [bogoliubovAlpha_sq ν hν, bogoliubovBeta_sq ν hν, div_sub_div_same,
    div_self (one_sub_exp_pos ν hν).ne']

/-- **[Thermal occupation] `|β_ν|² = 1/(e^{2πν} − 1)`.**  The number of Fulling quanta in the Minkowski
vacuum is the Bose–Einstein occupation at the Unruh inverse temperature `β = 2π` — this *is* the thermality
of the Minkowski vacuum with respect to the Rindler observer. -/
theorem bogoliubov_beta_sq_thermal (ν : ℝ) (hν : 0 < ν) :
    bogoliubovBeta ν ^ 2 = boseEinstein (2 * Real.pi) ν := by
  rw [bogoliubovBeta_sq ν hν, boseEinstein, Real.exp_neg]
  set e := Real.exp (2 * Real.pi * ν) with he
  have he_gt : 1 < e := by
    rw [he, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have : 0 < 2 * Real.pi * ν := by positivity
    linarith
  have hex : e ≠ 0 := by rw [he]; exact Real.exp_ne_zero _
  have he1 : e - 1 ≠ 0 := by linarith
  field_simp

/-- **[Detailed balance] `|β_ν|²/|α_ν|² = e^{−2πν}`.**  The Boltzmann factor between the Bogoliubov
coefficients — the ratio of the vacuum's `−` and `+` mode content. -/
theorem bogoliubov_detailedBalance (ν : ℝ) (hν : 0 < ν) :
    bogoliubovBeta ν ^ 2 / bogoliubovAlpha ν ^ 2 = Real.exp (-(2 * Real.pi * ν)) := by
  rw [bogoliubovBeta_sq ν hν, bogoliubovAlpha_sq ν hν]
  have hd : (1 - Real.exp (-(2 * Real.pi * ν))) ≠ 0 := (one_sub_exp_pos ν hν).ne'
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaMinkowskiFullingBogoliubov

end
