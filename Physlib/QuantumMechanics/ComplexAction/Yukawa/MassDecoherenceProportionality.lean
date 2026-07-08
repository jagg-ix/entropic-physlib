/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Yukawa double role: mass, decoherence width, and entropy-production rate are proportional

In the complex-action reading of the Yukawa sector (CAT/EPT), a *single* Yukawa coupling `y_f` sets two
quantities at once: the inertial mass from the real (Higgs) sector and the decoherence rate from the
imaginary (entropic) sector,

  `m_f = y_f v / √2`        (`yukawaMass`, Higgs VEV `v`),
  `Γ_f = y_f ω₀ / ℏ`        (`yukawaDecoherenceWidth`, entropic frequency `ω₀`).

This file formalizes the **proportionality those two relations force**, and links it to the resonance hub.
It is explicitly *conditional* on the two Yukawa relations: it does **not** derive `y_f` (which the source
material never does — `y_f` stays a free parameter), only the structure that follows once both relations are
assumed.

* `yukawaWidth_eq_widthFromRate_entropyRate`: `Γ_f = widthFromRate (Γ_f/2)` — the Yukawa decoherence width is
  a Bender entropy-production width, with rate `Ṡ_I = Γ_f/2` (`yukawaEntropyRate`); so `Γ_f = 2 Ṡ_I` ties
  directly to `BenderIdentity`/`EntropicTime.EntropyProductionDecay`.
* `yukawaWidth_div_mass`: `Γ_f / m_f = √2 ω₀ / (ℏ v)` — the ratio is **independent of `y_f`** (it cancels):
  heavier ⟹ proportionally faster decoherence.
* `yukawaEntropyRate_eq_const_mul_mass`: `Ṡ_I = (√2 ω₀ / (2 ℏ v)) · m_f` — the **entropy-production rate is
  proportional to the (Yukawa-generated) mass**, with a `y_f`-independent constant. This is the "mass–entropy
  duality" `m ↔ Ṡ_I` made into an equality through the shared `y_f`.
* `yukawa_massless_no_entropy`: `y_f = 0 ⟹ m_f = Γ_f = Ṡ_I = 0` — a massless particle has no decoherence and
  no entropy production (the reversible limit; matches `Θ̇ = 0` for massless fields).

## References

* CAT/EPT Yukawa–entropic duality: the same `y_f` fixing `m_f = y_f v/√2` (Higgs) and `Γ_f = y_f ω₀/ℏ`
  (decoherence). `Physlib` (`BenderIdentity.widthFromRate`, `EntropicTime.EntropyProductionDecay`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality

/-- **The inertial mass from the Yukawa coupling** `m_f = y v/√2` (Higgs VEV `v`). -/
noncomputable def yukawaMass (y v : ℝ) : ℝ := y * v / Real.sqrt 2

/-- **The decoherence width from the same Yukawa coupling** `Γ_f = y ω₀/ℏ` (entropic frequency `ω₀`). -/
noncomputable def yukawaDecoherenceWidth (y ω₀ ℏ : ℝ) : ℝ := y * ω₀ / ℏ

/-- **The entropy-production rate** `Ṡ_I = Γ_f/2` of the Yukawa decoherence (since `Γ = 2 Ṡ_I`). -/
noncomputable def yukawaEntropyRate (y ω₀ ℏ : ℝ) : ℝ := yukawaDecoherenceWidth y ω₀ ℏ / 2

/-- **[Yukawa width is a Bender entropy-production width]** `Γ_f = widthFromRate (Γ_f/2)`: the Yukawa
decoherence width is exactly the resonance width `2 Ṡ_I` of its own entropy-production rate, tying the Yukawa
sector to `BenderIdentity`/`EntropicTime.EntropyProductionDecay`. -/
theorem yukawaWidth_eq_widthFromRate_entropyRate (y ω₀ ℏ : ℝ) :
    yukawaDecoherenceWidth y ω₀ ℏ = widthFromRate (yukawaEntropyRate y ω₀ ℏ) := by
  unfold yukawaEntropyRate widthFromRate
  ring

/-- **[The decoherence/mass ratio is `y_f`-independent]** `Γ_f / m_f = √2 ω₀ / (ℏ v)`: the Yukawa coupling
cancels, so a heavier particle decoheres proportionally faster — independent of how the mass was set. -/
theorem yukawaWidth_div_mass (y v ω₀ ℏ : ℝ) (hy : y ≠ 0) (hv : v ≠ 0) (hℏ : ℏ ≠ 0) :
    yukawaDecoherenceWidth y ω₀ ℏ / yukawaMass y v = Real.sqrt 2 * ω₀ / (ℏ * v) := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold yukawaDecoherenceWidth yukawaMass
  field_simp

/-- **[Entropy-production rate ∝ mass]** `Ṡ_I = (√2 ω₀ / (2 ℏ v)) · m_f`: the entropy-production rate is
proportional to the Yukawa-generated mass, with a `y_f`-independent constant. This is the "mass–entropy
duality" `m ↔ Ṡ_I` as an equality forced by the single shared coupling. -/
theorem yukawaEntropyRate_eq_const_mul_mass (y v ω₀ ℏ : ℝ) (hv : v ≠ 0) (hℏ : ℏ ≠ 0) :
    yukawaEntropyRate y ω₀ ℏ = (Real.sqrt 2 * ω₀ / (2 * ℏ * v)) * yukawaMass y v := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold yukawaEntropyRate yukawaDecoherenceWidth yukawaMass
  field_simp

/-- **[Massless ⟹ no decoherence, no entropy production]** at `y_f = 0` the mass, decoherence width, and
entropy-production rate all vanish — the reversible limit (`Θ̇ = 0` for a massless field). -/
@[simp] theorem yukawa_massless_no_entropy (v ω₀ ℏ : ℝ) :
    yukawaMass 0 v = 0 ∧ yukawaDecoherenceWidth 0 ω₀ ℏ = 0 ∧ yukawaEntropyRate 0 ω₀ ℏ = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [yukawaMass, yukawaDecoherenceWidth, yukawaEntropyRate]

/-! ## §B — recovering the coupling from the mass (inversion + parameter reduction)

This is the *only* "derivation" of `y_f` the source material actually supplies: an **inversion of the measured
mass**, `y_f = √2 m_f/v`. It is circular as a first-principles derivation — no formula giving `y_f` from
geometry, topology, information, or `δS = 0` exists in the files (`y_f` stays free). What is genuine is the
**parameter reduction**: because one coupling sets both sectors, recovering it from the mass *predicts* the
decoherence width and entropy-production rate (they are no longer independent inputs). -/

/-- **The Yukawa coupling recovered from the mass** `y_f = √2 m_f/v` — the inversion of `m_f = y_f v/√2`.
Not a first-principles derivation (it uses the *measured* mass); a legitimate inversion. -/
noncomputable def yukawaCoupling (m v : ℝ) : ℝ := Real.sqrt 2 * m / v

/-- **[The recovery reproduces the mass]** `yukawaMass (yukawaCoupling m v) v = m` (`v ≠ 0`) — the inversion
is consistent. -/
theorem yukawaMass_yukawaCoupling (m v : ℝ) (hv : v ≠ 0) :
    yukawaMass (yukawaCoupling m v) v = m := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold yukawaMass yukawaCoupling
  field_simp

/-- **[The decoherence width is determined by the mass — parameter reduction]** once `y_f` is fixed from the
mass, the width is no longer a free input: `Γ_f = √2 m_f ω₀ / (ℏ v)`. This is the real content behind
"deriving the Yukawa coupling": not a value for `y_f`, but that the single shared coupling makes the mass
*predict* the entropic decoherence width. -/
theorem yukawaDecoherenceWidth_yukawaCoupling (m v ω₀ ℏ : ℝ) :
    yukawaDecoherenceWidth (yukawaCoupling m v) ω₀ ℏ = Real.sqrt 2 * m * ω₀ / (ℏ * v) := by
  unfold yukawaDecoherenceWidth yukawaCoupling
  ring

/-- **[The entropy-production rate is determined by the mass]** `Ṡ_I = √2 m_f ω₀ / (2 ℏ v)` — likewise a
prediction once `y_f` is recovered from the mass, via the hub `Γ = 2 Ṡ_I`. -/
theorem yukawaEntropyRate_yukawaCoupling (m v ω₀ ℏ : ℝ) :
    yukawaEntropyRate (yukawaCoupling m v) ω₀ ℏ = Real.sqrt 2 * m * ω₀ / (2 * ℏ * v) := by
  unfold yukawaEntropyRate yukawaDecoherenceWidth yukawaCoupling
  ring

end Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality

end
