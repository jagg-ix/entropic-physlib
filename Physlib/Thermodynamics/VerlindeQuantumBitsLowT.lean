/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.VerlindeEquipartitionDerivation
public import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Verlinde's holographic *bits* as two-level quantum systems

Follow-up to `VerlindeEquipartitionDerivation.lean`. That file
formalises Verlinde's equipartition hypothesis in the **classical
quadratic-DOF limit** (continuous spectrum, `⟨E⟩ = (1/2)·k_B·T`
per DOF). The scope note flagged that **quantum two-level
bits** with energy gap `ε` deviate from this at low `T` (and even
in the high-`T` limit, saturate at `ε/2` per bit rather than
`(1/2)·k_B·T`).

This file formalises that deviation **without invoking limits of
`tanh`** (which would require deeper analytic machinery) by:

1. Modelling `N` independent two-level Verlinde bits as
 `nsmul N (twoState 0 ε)` using physlib's existing
 `CanonicalEnsemble.twoState` and `CanonicalEnsemble.nsmul`
 infrastructure.
2. Computing the closed-form mean energy
 `⟨E⟩ = (N·ε/2)·(1 − tanh(β·ε/2))` via
 `twoState_meanEnergy_eq` + `meanEnergy_nsmul`.
3. **Substituting `ε := k_B·T.val`** (the *thermal-gap* hypothesis,
 suggested by the Unruh/holographic identification of bit-gap with
 local temperature scale `[[unruh-temperature]]`) and showing
 *algebraically* that the result is
 `(N·k_B·T/2)·(1 − tanh(1/2))`, **strictly less than**
 `(1/2)·N·k_B·T`. No limit theorems needed: the discrepancy is a
 single algebraic inequality `1 − tanh(1/2) < 1`.

## Contents

* `nTwoStateBitsEnsemble N ε` — `N` independent two-level bits with
 gap `ε`, built from `twoState 0 ε` via `nsmul`.
* **`meanEnergy_nTwoStateBits`** — the closed-form mean energy:
 `⟨E⟩ = (N·ε/2)·(1 − tanh(β·ε/2))`.
* **`thermalGap_meanEnergy_lt_equipartition`** — at the thermal
 gap `ε := k_B·T.val`, the quantum-bit mean energy is
 **strictly less than** Verlinde's classical equipartition
 `equipartitionEnergy N k_B T.val = (1/2)·N·k_B·T`.

## Physics interpretation

* **Classical equipartition** (harmonic-oscillator high-`T` limit):
 `⟨E⟩ = (1/2)·N·k_B·T` — this is the value Verlinde *uses*.
* **Two-level bits at thermal gap** `ε = k_B·T`:
 `⟨E⟩ = (N·k_B·T/2)·(1 − tanh(1/2)) ≈ 0.269·N·k_B·T`.
 **About 54% smaller** than the classical equipartition value.
* The two-level mean energy approaches `ε/2 = (k_B·T)/2` only in
 the asymptotic high-`T` limit `β·ε → 0`; in the thermal-gap
 regime `β·ε = 1` they are not equal.

**scope correction**: Verlinde's "equipartition for bits"
is therefore only a *classical-harmonic-DOF* statement. Modelling
bits literally as two-level quantum systems — even with Unruh-scaled
thermal gaps — gives a *quantitatively different* result from the
holographic Newton-gravity derivation in
`VerlindeNewtonGravity.lean`.

## QIF connection

The Unruh-temperature interpretation
(`Physlib.Relativity.Special.QIFUnruhFrameChange`,
`Physlib.Thermodynamics.VerlindeEntropicForce.unruhTemperature`)
naturally suggests `ε ~ k_B·T_U` for bits seen by an accelerated
observer at acceleration `a` with `T_U = ℏ·a/(2π·c·k_B)`. The
substitution `ε := k_B·T.val` formalised here corresponds to that
thermal-gap interpretation at the **observer's local temperature
`T`** (which equals `T_U` for an accelerated observer in a thermal
KMS state).

The full QIF formalisation (matching `T = T_U` and identifying the
relevant Bogoliubov transformation) is in
`QIFUnruhFrameChange.lean`; this file provides the
*statistical-mechanical* deviation, which is the load-bearing
*quantitative* correction.

## References

* Verlinde 2011 (arXiv:1001.0785) §2.2 — equipartition for bits.
* Unruh 1976 — thermal-bath interpretation for accelerated observer.
* `Physlib/StatisticalMechanics/CanonicalEnsemble/TwoState.lean` —
 `twoState`, `twoState_meanEnergy_eq`.
* `Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean` —
 `nsmul`, `meanEnergy_nsmul`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

open MeasureTheory Constants Real Temperature
open Physlib.StatisticalMechanics
open scoped Temperature

/-! ## §1 — N two-level Verlinde bits -/

/-- **`N` independent two-level Verlinde bits with energy gap `ε`**.

Built as `nsmul N (twoState 0 ε)` using physlib's existing
`CanonicalEnsemble.twoState` (one bit, ground-state energy `0`,
excited-state energy `ε`) and `nsmul` (non-interacting copies).

structure type: `Fin N → Fin 2` — each bit independently `0`/`1`. -/
def nTwoStateBitsEnsemble (N : ℕ) (ε : ℝ) :
    CanonicalEnsemble (Fin N → Fin 2) :=
  CanonicalEnsemble.nsmul N (CanonicalEnsemble.twoState 0 ε)

/-! ## §2 — Closed-form mean energy -/

/-- **Closed-form mean energy of `N` two-level Verlinde bits**:

  `⟨E⟩ = (N·ε/2) · (1 − tanh(β·ε/2))`

equivalently `⟨E⟩ = N · ε / (1 + exp(β·ε))` — the Fermi-Dirac
single-occupancy form.

Composition of:
* `CanonicalEnsemble.meanEnergy_nsmul` (N copies multiply by N).
* `CanonicalEnsemble.twoState_meanEnergy_eq` (single-bit
  `(0+ε)/2 − ((ε−0)/2)·tanh(β·(ε−0)/2)`). -/
theorem meanEnergy_nTwoStateBits
    (N : ℕ) (ε : ℝ) (T : Temperature)
    [IsFiniteMeasure ((CanonicalEnsemble.twoState 0 ε).μBolt T)]
    [NeZero (CanonicalEnsemble.twoState 0 ε).μ]
    (h_integrable :
      Integrable (CanonicalEnsemble.twoState 0 ε).energy
        ((CanonicalEnsemble.twoState 0 ε).μProd T)) :
    (nTwoStateBitsEnsemble N ε).meanEnergy T =
      (N : ℝ) * ε / 2 * (1 - Real.tanh ((β T : ℝ) * ε / 2)) := by
  unfold nTwoStateBitsEnsemble
  rw [(CanonicalEnsemble.twoState 0 ε).meanEnergy_nsmul N T h_integrable]
  rw [CanonicalEnsemble.twoState_meanEnergy_eq 0 ε T]
  simp only [zero_add, sub_zero]
  ring

/-! ## §3 — comparison to Verlinde's classical equipartition -/

/-- **`tanh(1/2)` is strictly positive**.

Derived from `tanh = sinh/cosh`, `sinh_pos_iff`, and
`cosh_pos`. -/
theorem tanh_one_half_pos : 0 < Real.tanh (1 / 2 : ℝ) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply div_pos
  · exact Real.sinh_pos_iff.mpr (by norm_num)
  · exact Real.cosh_pos _

/-- **`1 − tanh(1/2)` is strictly less than `1`**.

Algebraic consequence of `tanh_one_half_pos`. -/
theorem one_sub_tanh_one_half_lt_one : 1 - Real.tanh (1 / 2 : ℝ) < 1 := by
  have h : 0 < Real.tanh (1 / 2 : ℝ) := tanh_one_half_pos
  linarith

/-- **`β·(k_B·T) = 1` at any positive temperature** — Verlinde's
*thermal-gap* identity.

Direct from `β T = 1/(k_B·T)`. -/
theorem beta_thermal_gap_eq_one
    (T : Temperature) (hT_pos : 0 < T.val) :
    (β T : ℝ) * (kB * (T.val : ℝ)) = 1 := by
  have hkB_ne : (kB : ℝ) ≠ 0 := ne_of_gt kB_pos
  have hT_ne : (T.val : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hT_pos
  have h_beta : (T.β : ℝ) = 1 / (kB * T.val) := by
    show (T.β : NNReal).val = 1 / (kB * T.val)
    unfold Temperature.β
    rfl
  rw [h_beta]
  have hkB_T : 0 < kB * (T.val : ℝ) := mul_pos kB_pos (by exact_mod_cast hT_pos)
  have hkB_T_ne : (kB * (T.val : ℝ)) ≠ 0 := ne_of_gt hkB_T
  field_simp

/-- **Mean energy of `N` two-level bits at the thermal gap**
`ε := k_B·T.val`:

  `⟨E⟩ = (N·k_B·T/2) · (1 − tanh(1/2))`.

Substitution of `ε = k_B·T.val` into `meanEnergy_nTwoStateBits`,
using `β T · k_B·T = 1`. -/
theorem meanEnergy_nTwoStateBits_thermalGap
    (N : ℕ) (T : Temperature) (hT_pos : 0 < T.val)
    [IsFiniteMeasure ((CanonicalEnsemble.twoState 0 (kB * T.val)).μBolt T)]
    [NeZero (CanonicalEnsemble.twoState 0 (kB * T.val)).μ]
    (h_integrable :
      Integrable (CanonicalEnsemble.twoState 0 (kB * T.val)).energy
        ((CanonicalEnsemble.twoState 0 (kB * T.val)).μProd T)) :
    (nTwoStateBitsEnsemble N (kB * T.val)).meanEnergy T =
      (N : ℝ) * kB * T.val / 2 * (1 - Real.tanh (1 / 2 : ℝ)) := by
  rw [meanEnergy_nTwoStateBits N (kB * T.val) T h_integrable]
  congr 2
  · ring
  · congr 1
    rw [show (β T : ℝ) * (kB * T.val) / 2 = (β T * (kB * T.val)) / 2 by ring]
    rw [beta_thermal_gap_eq_one T hT_pos]

/-- **Quantum-bit mean energy is STRICTLY LESS THAN Verlinde's
classical equipartition** at the thermal gap `ε := k_B·T.val`.

Load-bearing **scope correction**:
modelling Verlinde's holographic bits literally as two-level
quantum systems with thermal-scaled gap gives a mean energy
**strictly below** the classical equipartition value
`(1/2)·N·k_B·T` that Verlinde's Newton-gravity derivation uses.

Quantitatively: `(1 − tanh(1/2)) ≈ 0.5379`, so the quantum result
is about `0.269·N·k_B·T` — **about 54% smaller** than the classical
`(1/2)·N·k_B·T`.

This implies: **Verlinde's equipartition is NOT recovered by
two-level bits**, even at the natural thermal gap. His derivation
relies on the *classical (harmonic) DOF* interpretation, which is
the high-temperature limit of the *quantum harmonic oscillator*,
not of two-level systems.

The strict inequality is proven algebraically via
`one_sub_tanh_one_half_lt_one`, **no limit-of-tanh theorem
required**. -/
theorem thermalGap_meanEnergy_lt_equipartition
    (N : ℕ) (hN : 0 < N) (T : Temperature) (hT_pos : 0 < T.val)
    [IsFiniteMeasure ((CanonicalEnsemble.twoState 0 (kB * T.val)).μBolt T)]
    [NeZero (CanonicalEnsemble.twoState 0 (kB * T.val)).μ]
    (h_integrable :
      Integrable (CanonicalEnsemble.twoState 0 (kB * T.val)).energy
        ((CanonicalEnsemble.twoState 0 (kB * T.val)).μProd T)) :
    (nTwoStateBitsEnsemble N (kB * T.val)).meanEnergy T <
      equipartitionEnergy (N : ℝ) kB T.val := by
  rw [meanEnergy_nTwoStateBits_thermalGap N T hT_pos h_integrable]
  unfold equipartitionEnergy
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hkB : 0 < kB := kB_pos
  have hpref : 0 < (N : ℝ) * kB * T.val / 2 := by positivity
  have hdiff : 1 - Real.tanh (1 / 2 : ℝ) < 1 := one_sub_tanh_one_half_lt_one
  calc (N : ℝ) * kB * T.val / 2 * (1 - Real.tanh (1 / 2 : ℝ))
      < (N : ℝ) * kB * T.val / 2 * 1 := by
        exact mul_lt_mul_of_pos_left hdiff hpref
    _ = 1 / 2 * (N : ℝ) * kB * T.val := by ring
end Physlib.Thermodynamics

end
