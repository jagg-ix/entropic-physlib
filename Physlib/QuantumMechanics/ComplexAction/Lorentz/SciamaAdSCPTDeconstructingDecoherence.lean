/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence

/-!
# Deconstructing decoherence: the simple rules of thumb are toy-model artifacts (Anglin–Paz–Zurek, arXiv:quant-ph/9611045)

Anglin, Paz & Zurek show that the standard "rules of thumb" of decoherence — a *single* universal decoherence
timescale, and a decoherence rate `∝ a²` (the square of the branch separation) that grows without bound — are
artifacts of exactly-solvable linear/Ohmic toy models, and fail in the general mesoscopic regime.  This module
formalizes the two cleanest deconstructions and uses them to *honestly scope* the decoherence idealization used
across this arc: the transport interference visibility `exp(−Γt)`
(`SciamaAdSCPTTransportDecoherenceInterference`), the confinement weight `exp(−σA)`
(`SciamaAdSCPTConfinementColourDecoherence`), and the Caldeira–Leggett factor `exp(−φ)`
(`CaldeiraLeggettDecoherence`) are all the *simple late-time, linear, unsaturated* regime.

The decoherence exponent enters as `W_int(t) = e^{−D(t)} W_int(0)` (Eq. 11); the repo's
`caldeiraLeggettDecoherence M γ k_B T τ ξ = 2Mγk_BT τ ξ²` is exactly the high-temperature Ohmic late-time form
`D ∝ a²·t` (Eqs. 12–14), with `ξ = a` the branch separation.

* **§1 — the `a²` rule** (`decoherence_scales_as_separation_squared`): doubling the branch separation quadruples
  the Caldeira–Leggett decoherence exponent, `D(2a) = 4·D(a)` — Zurek's `∝ a²` rule of thumb.
* **§2 — no universal timescale** (`decoherence_early_late_ratio`, `decoherence_regimes_cross_at_gamma_inverse`):
  the early-time exponent is *quadratic* in time, `D_early ∝ a²·Γτ²` (Eq. 15), while the late-time one is
  *linear*, `D_late ∝ a²·τ` (Eq. 13); their ratio is `Γτ`, not a constant, so the two regimes have different
  time-scalings (the timescales scale as `1/a` vs `1/a²`) — there is no single universal `τ_dec`.  They cross at
  `τ = 1/Γ`.
* **§3 — saturation at long range** (`decoherence_saturates`, `saturatingDecoherence_nonneg`): for a *quasi-local*
  interaction (finite range `a₀`) the exponent plateaus, `D_sat(a) = D_∞(1 − e^{−a²/a₀²}) ≤ D_∞` — bounded, not
  the unbounded `a²` law; the `∝ a²` rule breaks at long range (Anglin–Paz–Zurek §IV, the "mattress model").

So the visibility/confinement/Caldeira–Leggett decoherence weights used in this arc are the honest *late-time,
linear, short-range* idealization; the general decoherence is regime-dependent (early `t²`) and saturating.

Honest scope: the `a²` doubling law is an exact reuse of `caldeiraLeggettDecoherence`; the early/late ratio and
the saturation bound are the two exact deconstructions.  The full preparation-dependence (Anglin–Paz–Zurek §III)
and the field-theoretic saturation (§IV.B) are contextualised, not formalized.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDeconstructingDecoherence

open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettDecoherence

/-! ## §1. The `a²` rule of thumb (Zurek) -/

/-- **[The `∝ a²` rule] `D(2a) = 4·D(a)`.**  Doubling the branch separation `ξ = a` quadruples the
Caldeira–Leggett decoherence exponent — the "rate increases with the square of the branch separation" rule of
thumb (Anglin–Paz–Zurek, putative principle 3). -/
theorem decoherence_scales_as_separation_squared (M γ kB T τ ξ : ℝ) :
    caldeiraLeggettDecoherence M γ kB T τ (2 * ξ) = 4 * caldeiraLeggettDecoherence M γ kB T τ ξ := by
  unfold caldeiraLeggettDecoherence
  ring

/-! ## §2. No universal decoherence timescale (early `t²` vs late `t`) -/

/-- The early-time decoherence exponent `D_early ∝ a²·Γτ²` (Anglin–Paz–Zurek Eq. 15) — *quadratic* in time,
unlike the late-time linear `caldeiraLeggettDecoherence`. -/
def earlyTimeDecoherence (M γ kB T Γ τ ξ : ℝ) : ℝ := 2 * M * γ * kB * T * Γ * τ ^ 2 * ξ ^ 2

/-- **[The early and late exponents are not proportional] `D_early / D_late = Γτ`.**  The ratio grows with time,
so the two decoherence regimes have different time-scalings — no single rescaling `t/τ_dec` captures both:
there is no universal decoherence timescale (Anglin–Paz–Zurek, putative principle 1 deconstructed). -/
theorem decoherence_early_late_ratio {M γ kB T Γ τ ξ : ℝ}
    (hM : M ≠ 0) (hγ : γ ≠ 0) (hkB : kB ≠ 0) (hT : T ≠ 0) (hτ : τ ≠ 0) (hξ : ξ ≠ 0) :
    earlyTimeDecoherence M γ kB T Γ τ ξ / caldeiraLeggettDecoherence M γ kB T τ ξ = Γ * τ := by
  unfold earlyTimeDecoherence caldeiraLeggettDecoherence
  field_simp

/-- **[The regimes cross at `τ = 1/Γ`]** — the early (`t²`) and late (`t`) exponents coincide at the bath
correlation time `Γ⁻¹`, the crossover between the quadratic and linear regimes. -/
theorem decoherence_regimes_cross_at_gamma_inverse (M γ kB T Γ ξ : ℝ) (hΓ : Γ ≠ 0) :
    earlyTimeDecoherence M γ kB T Γ (1 / Γ) ξ = caldeiraLeggettDecoherence M γ kB T (1 / Γ) ξ := by
  unfold earlyTimeDecoherence caldeiraLeggettDecoherence
  field_simp

/-! ## §3. Saturation of the `a²` rule at long range (quasi-local interaction) -/

/-- The saturating decoherence exponent of a *quasi-local* interaction of range `a₀`: `D_∞(1 − e^{−a²/a₀²})`
(Anglin–Paz–Zurek §IV, "mattress model") — quadratic `∝ a²` at short range, but *bounded* at long range. -/
def saturatingDecoherence (Dinf a a0 : ℝ) : ℝ := Dinf * (1 - Real.exp (-(a ^ 2 / a0 ^ 2)))

/-- **[The `a²` rule saturates] `D_sat(a) ≤ D_∞`.**  For a quasi-local interaction the decoherence exponent
plateaus at `D_∞` — it does *not* grow without bound as `a²`, so the `∝ a²` rule breaks at long range
(Anglin–Paz–Zurek, putative principle 3 deconstructed). -/
theorem decoherence_saturates (Dinf a a0 : ℝ) (hD : 0 ≤ Dinf) :
    saturatingDecoherence Dinf a a0 ≤ Dinf := by
  unfold saturatingDecoherence
  have h1 : 1 - Real.exp (-(a ^ 2 / a0 ^ 2)) ≤ 1 := by
    have := Real.exp_pos (-(a ^ 2 / a0 ^ 2)); linarith
  calc Dinf * (1 - Real.exp (-(a ^ 2 / a0 ^ 2))) ≤ Dinf * 1 := mul_le_mul_of_nonneg_left h1 hD
    _ = Dinf := mul_one Dinf

/-- **[The saturating exponent is non-negative]** `0 ≤ D_sat(a)` — decoherence still only suppresses. -/
theorem saturatingDecoherence_nonneg (Dinf a a0 : ℝ) (hD : 0 ≤ Dinf) :
    0 ≤ saturatingDecoherence Dinf a a0 := by
  unfold saturatingDecoherence
  apply mul_nonneg hD
  have h : Real.exp (-(a ^ 2 / a0 ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  linarith

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTDeconstructingDecoherence

end
