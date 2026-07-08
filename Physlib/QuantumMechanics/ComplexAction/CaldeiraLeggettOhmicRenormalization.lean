/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Discretizing the Caldeira–Leggett model: the Ohmic bath and frequency renormalization (Nishimura–Watanabe 2408.16627)

The companion to `ComplexSaddleDecoherence` (same paper, arXiv:2408.16627): before the complex-saddle evaluation
of the decoherence structure (Eqs. 18–30), Nishimura & Watanabe set up the discretized Caldeira–Leggett model
(Eqs. 1–8) — a system oscillator `x` coupled to a bath of `N_ℰ` oscillators `q^k` with an **Ohmic** spectral
density. This module formalizes the exact-algebra core of that setup.

**The Ohmic spectrum (Eqs. 2–3).** Reproducing the Ohmic bath requires the mode frequencies
`ω_k = ω_cut (k/N_ℰ)^{1/3}`; equivalently `ω_k² = ω_cut² (k/N_ℰ)^{2/3}` and `1/ω_k² = ω_cut⁻² (N_ℰ/k)^{2/3}`.

**Completing the square (Eq. 4).** The bilinear coupling `L_int = c x Σ q^k` is absorbed per bath mode by shifting
`q^k → q^k − (c/ω_k²)x`, leaving a residual `+ (c²/2ω_k²)x²` that renormalizes the system frequency:

`−½ω_k²(q^k)² + c x q^k = −½ω_k²(q^k − (c/ω_k²)x)² + (c²/2ω_k²)x²`.

**Frequency renormalization (Eqs. 5–7).** Summing the residuals shifts the bare frequency to
`ω_r² = ω_b² − c² Σ_k 1/ω_k²` (Eq. 5). The coupling constant is fixed at finite `N_ℰ` by
`c² = (4γ/π) ω_cut³ / (Σ_k (N_ℰ/k)^{2/3})` (Eq. 7) — chosen **precisely** so that the reciprocal-frequency sum
cancels exactly and the renormalization collapses to the closed form `ω_r² = ω_b² − 4γω_cut/π` (Eq. 6), for
*every* `N_ℰ`. The dissipation coefficient `γ` here is the same `γ` that sets the Caldeira–Leggett decoherence
rate `∝ γ/β = γT` (`ComplexSaddleDecoherence.gammaOffdiagLinear`,
`CaldeiraLeggettDecoherence.caldeiraLeggett_fluctuation_dissipation`).

* **§A — the Ohmic spectrum (Eqs. 2–3).** `ohmicFreq`, `ohmicFreq_sq`, `ohmicFreq_inv_sq`.
* **§B — completing the square (Eq. 4).** `completeSquare_mode`.
* **§C — the reciprocal-frequency sum (bridge to §D).** `ohmicReciprocalSum`, `ohmicShapeSum`,
 **`ohmicReciprocalSum_eq`** (`Σ 1/ω_k² = ω_cut⁻² Σ (N_ℰ/k)^{2/3}`).
* **§D — coupling and frequency renormalization (Eqs. 5–7).** `couplingSq` (Eq. 7); **`coupling_reciprocalSum_cancel`**
 (`c² Σ 1/ω_k² = 4γω_cut/π`, the exact cancellation); `renormFreqSq` (Eq. 5); **`renormFreqSq_eq_closed`** (Eq. 6).

Exact `ring` / `field_simp` / `Real.rpow` identities for the Ohmic frequencies, the
completing-the-square shift, and the coupling-constant cancellation. The discretized real-time action (Eq. 8), the
imaginary-time bath action (Eq. 12), the Gaussian path integral over `Dx Dq Dq̃` and the resulting complex saddle
`X̄ = M⁻¹C` with `det M` prefactor (Eqs. 13–21) are the paper's calculation, recorded not re-derived; the
closed-form model-setup identities they rest on are formalized here. The Ohmic condition `(dg/dκ)⁻¹ ∝ g²` (Eq. 2)
selecting `g(κ) ∝ κ^{1/3}` — a differential-equation statement — and the `N_ℰ → ∞` limit are not formalized.

## References

* J. Nishimura, H. Watanabe, arXiv:2408.16627, Eqs. 1–8. Companion to `ComplexSaddleDecoherence` (the
 decoherence structure of the same model).

No new axioms.
-/

set_option autoImplicit false

open scoped Real BigOperators
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization

/-! ## §A — the Ohmic spectrum (Eqs. 2–3) -/

/-- The **Ohmic bath mode frequency** `ω_k = ω_cut (k/N_ℰ)^{1/3}` (Eq. 3) — the spectrum reproducing the Ohmic
spectral density (`(dg/dκ)⁻¹ ∝ ω² = g²`, Eq. 2, forces `g(κ) ∝ κ^{1/3}`). -/
noncomputable def ohmicFreq (ωcut NE k : ℝ) : ℝ := ωcut * (k / NE) ^ ((1 : ℝ) / 3)

/-- **The squared Ohmic frequency** `ω_k² = ω_cut² (k/N_ℰ)^{2/3}`. -/
theorem ohmicFreq_sq (ωcut NE k : ℝ) (h : 0 ≤ k / NE) :
    ohmicFreq ωcut NE k ^ 2 = ωcut ^ 2 * (k / NE) ^ ((2 : ℝ) / 3) := by
  rw [ohmicFreq, mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((k / NE) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul h]
  norm_num

/-- **The reciprocal squared Ohmic frequency** `1/ω_k² = ω_cut⁻² (N_ℰ/k)^{2/3}` — the summand of the frequency
renormalization (Eq. 5), rewritten with the ratio inverted. -/
theorem ohmicFreq_inv_sq (ωcut NE k : ℝ) (hk : 0 < k) (hNE : 0 < NE) :
    1 / ohmicFreq ωcut NE k ^ 2 = (1 / ωcut ^ 2) * (NE / k) ^ ((2 : ℝ) / 3) := by
  have hkNE : 0 < k / NE := div_pos hk hNE
  rw [ohmicFreq_sq ωcut NE k hkNE.le, one_div, mul_inv]
  congr 1
  · rw [one_div]
  · rw [← Real.inv_rpow hkNE.le, inv_div]

/-! ## §B — completing the square (Eq. 4) -/

/-- **Completing the square per bath mode (Eq. 4)** — the bilinear coupling `c x q^k` in
`L = −½ω_k²(q^k)² + c x q^k` is absorbed by the shift `q^k → q^k − (c/ω_k²)x`, leaving the residual
`(c²/2ω_k²)x²` that renormalizes the system frequency (Eq. 5). -/
theorem completeSquare_mode (ωk c x q : ℝ) (hωk : ωk ≠ 0) :
    -(1 / 2) * ωk ^ 2 * q ^ 2 + c * x * q
      = -(1 / 2) * ωk ^ 2 * (q - (c / ωk ^ 2) * x) ^ 2 + c ^ 2 * x ^ 2 / (2 * ωk ^ 2) := by
  field_simp
  ring

/-! ## §C — the reciprocal-frequency sum (bridge to §D) -/

/-- The **reciprocal-frequency sum** `Σ_{k=1}^{n} 1/ω_k²` appearing in the frequency renormalization (Eq. 5). -/
noncomputable def ohmicReciprocalSum (ωcut NE : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / ohmicFreq ωcut NE (k : ℝ) ^ 2

/-- The **Ohmic shape sum** `Σ_{k=1}^{n} (N_ℰ/k)^{2/3}` — the frequency-independent factor whose inverse fixes the
coupling constant (Eq. 7). -/
noncomputable def ohmicShapeSum (NE : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (NE / (k : ℝ)) ^ ((2 : ℝ) / 3)

/-- **The reciprocal-frequency sum factors** `Σ 1/ω_k² = ω_cut⁻² Σ (N_ℰ/k)^{2/3}` — the `ω_cut` scale pulls out,
leaving the pure shape sum. -/
theorem ohmicReciprocalSum_eq (ωcut NE : ℝ) (n : ℕ) (hNE : 0 < NE) :
    ohmicReciprocalSum ωcut NE n = (1 / ωcut ^ 2) * ohmicShapeSum NE n := by
  rw [ohmicReciprocalSum, ohmicShapeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
  exact ohmicFreq_inv_sq ωcut NE (k : ℝ) hkpos hNE

/-! ## §D — coupling and frequency renormalization (Eqs. 5–7) -/

/-- The **coupling constant** `c² = (4γ/π) ω_cut³ / (Σ (N_ℰ/k)^{2/3})` (Eq. 7) — fixed at finite `N_ℰ` so the
frequency renormalization collapses to its `N_ℰ`-independent closed form (Eq. 6). -/
noncomputable def couplingSq (γ ωcut S : ℝ) : ℝ := 4 * γ / π * ωcut ^ 3 * S⁻¹

/-- **The coupling constant is chosen so the reciprocal-frequency sum cancels exactly (Eqs. 5–7)**
`c² Σ 1/ω_k² = 4γω_cut/π` — the finite bath sum `Σ (N_ℰ/k)^{2/3}` divides out completely, for *every* `N_ℰ`.
This is the exact identity behind the `N_ℰ`-independent renormalized frequency (Eq. 6). -/
theorem coupling_reciprocalSum_cancel (γ ωcut NE : ℝ) (n : ℕ)
    (hωcut : ωcut ≠ 0) (hNE : 0 < NE) (hS : ohmicShapeSum NE n ≠ 0) :
    couplingSq γ ωcut (ohmicShapeSum NE n) * ohmicReciprocalSum ωcut NE n = 4 * γ * ωcut / π := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [ohmicReciprocalSum_eq ωcut NE n hNE, couplingSq]
  field_simp

/-- The **renormalized system frequency** `ω_r² = ω_b² − c² Σ 1/ω_k²` (Eq. 5) — the bare frequency `ω_b` shifted by
the environment via the completing-the-square residuals (`completeSquare_mode`). -/
noncomputable def renormFreqSq (ωb γ ωcut NE : ℝ) (n : ℕ) : ℝ :=
  ωb ^ 2 - couplingSq γ ωcut (ohmicShapeSum NE n) * ohmicReciprocalSum ωcut NE n

/-- **The renormalized frequency in closed form (Eq. 6)** `ω_r² = ω_b² − 4γω_cut/π` — independent of `N_ℰ` and of
the bath shape sum, by the exact cancellation `coupling_reciprocalSum_cancel`. The shift `∝ γω_cut` is set by the
dissipation coefficient `γ` (the same `γ` driving Caldeira–Leggett decoherence). -/
theorem renormFreqSq_eq_closed (ωb γ ωcut NE : ℝ) (n : ℕ)
    (hωcut : ωcut ≠ 0) (hNE : 0 < NE) (hS : ohmicShapeSum NE n ≠ 0) :
    renormFreqSq ωb γ ωcut NE n = ωb ^ 2 - 4 * γ * ωcut / π := by
  rw [renormFreqSq, coupling_reciprocalSum_cancel γ ωcut NE n hωcut hNE hS]

end Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization
