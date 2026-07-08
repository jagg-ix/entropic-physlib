/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
public import Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

/-!
# Isolating the Yukawa couplings — `y = √2 ħω/(c² v)` from the two mass expressions

Exactly as the fine-structure constant was isolated by equating the *two* expressions for the muon anomaly
(`MuonAnomaly.SchwingerMagicRapidityEquation`: Schwinger `α/2π` `=` kinematic `1/sinh²η` ⟹ `α = 2π(K²−1)`), the Yukawa
coupling is isolated by equating the two expressions for the *same observable*, the fermion rest mass:

* **Higgs mechanism** — `m = yukawaMass y v = y·v/√2` (mass from the Yukawa coupling × VEV);
* **internal clock** — `m = comptonMass ω c ħ = ħω/c²` (mass from the de Broglie clock frequency,
 `Winding.NumberMass`).

Setting them equal and solving for `y` (`yukawa_isolated`, `yukawa_isolated_explicit`):

 `y = √2 ħω/(c² v)`,

i.e. **the Yukawa coupling is the internal-clock frequency measured in units of the Higgs VEV** (the existing
`yukawaCoupling m v = √2 m/v` applied to the clock mass). The notable *isolated value*: when a fermion's mass
equals `v/√2` its coupling is exactly `1` (`yukawaCoupling_natural_mass`) — the top quark sits there,
`y_top ≈ √2·173/246 ≈ 0.99` (`topYukawa_near_one`), the one near-unity Yukawa.

* **§A — the isolation.** `yukawa_isolated` (`y = yukawaCoupling (comptonMass ω c ħ) v`),
 `yukawaCoupling_comptonMass` (`= √2 ħω/(c² v)`), `yukawa_isolated_explicit`.
* **§B — the natural value.** `yukawaCoupling_natural_mass` (`m = v/√2 ⟹ y = 1`), `topYukawa_near_one`
 (`0.99 < y_top < 1`), `naturalMass_246_near_174` (`v/√2 ≈ 174 GeV`), `top_at_natural_mass`
 (`|v/√2 − m_top| < 1` GeV — why `y_top ≈ 1`).
* **§C — repo link.** `clockFrequency_sets_entropyRate` — composing the clock-mass isolation with the existing
 `yukawaEntropyRate_eq_const_mul_mass` gives `Ṡ_I ∝ ħω/c²`: the internal clock frequency sets the entropic
 decoherence rate, bridging the winding/Compton-clock layer to the `Ṡ_I` entropic-time core.

Proven: equating the Higgs mass with the Compton-clock mass gives `y = √2 ħω/(c² v)`, and
`m = v/√2` is the unit-coupling point (the top, numerically). This *isolates* the coupling in terms of the
clock frequency — it does **not** predict the frequency/mass values (those are empirical input, as for `α`);
the rigorous Yukawa-sector content is in `Physlib.Particles.StandardModel`.

## References

* `m_f = y_f v/√2`; top Yukawa `≈ 1`. `Physlib`
 (`Yukawa.MassDecoherenceProportionality.yukawaCoupling`/`yukawaMass`, `Winding.NumberMass.comptonMass`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation

/-! ## §A — isolate `y` by equating the Higgs mass with the Compton-clock mass -/

/-- **[The isolated Yukawa coupling]** equating the Higgs mass `yukawaMass y v` with the Compton-clock mass
`comptonMass ω c ħ` recovers the coupling `y = yukawaCoupling (comptonMass ω c ħ) v` — the coupling read off
the internal-clock frequency. -/
theorem yukawa_isolated (y v ω c ħ : ℝ) (hv : v ≠ 0) (h : yukawaMass y v = comptonMass ω c ħ) :
    y = yukawaCoupling (comptonMass ω c ħ) v := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [← h]
  unfold yukawaCoupling yukawaMass
  field_simp

/-- **[The coupling from the clock frequency]** `yukawaCoupling (ħω/c²) v = √2 ħω/(c² v)` — the Yukawa coupling
is the internal-clock frequency in units of the Higgs VEV. -/
theorem yukawaCoupling_comptonMass (v ω c ħ : ℝ) :
    yukawaCoupling (comptonMass ω c ħ) v = Real.sqrt 2 * ħ * ω / (c ^ 2 * v) := by
  unfold yukawaCoupling comptonMass; ring

/-- **[`y = √2 ħω/(c² v)`, explicit]** the isolated Yukawa coupling in closed form. -/
theorem yukawa_isolated_explicit (y v ω c ħ : ℝ) (hv : v ≠ 0)
    (h : yukawaMass y v = comptonMass ω c ħ) :
    y = Real.sqrt 2 * ħ * ω / (c ^ 2 * v) := by
  rw [yukawa_isolated y v ω c ħ hv h, yukawaCoupling_comptonMass]

/-! ## §B — the natural unit-coupling point and the top quark -/

/-- **[The unit-coupling mass]** `m = v/√2 ⟹ y = 1` — the special point where a fermion's mass equals
`v/√2` and its Yukawa coupling is exactly one. -/
theorem yukawaCoupling_natural_mass (v : ℝ) (hv : v ≠ 0) :
    yukawaCoupling (v / Real.sqrt 2) v = 1 := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold yukawaCoupling
  field_simp

/-- Numeric bounds on `√2` used for the top-quark estimates. -/
private theorem sqrt_two_bounds : (1.414 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.415 := by
  refine ⟨?_, ?_⟩
  · rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_lt_sqrt (by positivity); norm_num
  · rw [show (1.415 : ℝ) = Real.sqrt (1.415 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_lt_sqrt (by positivity); norm_num

/-- **[The top Yukawa is `≈ 1`]** `0.99 < y_top < 1` for `m_top ≈ 173 GeV`, `v ≈ 246 GeV`:
`y_top = √2·173/246 ≈ 0.99` — the one fermion with an `O(1)` Yukawa, sitting near the `m = v/√2` point. -/
theorem topYukawa_near_one :
    0.99 < yukawaCoupling 173 246 ∧ yukawaCoupling 173 246 < 1 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  unfold yukawaCoupling
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [hlo]
  · rw [div_lt_one (by norm_num)]; nlinarith [hhi]

/-- **[The unit-coupling mass is `≈ 174 GeV`]** `173 < v/√2 < 174` for `v ≈ 246 GeV` — the mass at which a
fermion's Yukawa coupling is exactly `1` (`yukawaCoupling_natural_mass`) is `246/√2 ≈ 173.95 GeV`. -/
theorem naturalMass_246_near_174 :
    (173 : ℝ) < 246 / Real.sqrt 2 ∧ 246 / Real.sqrt 2 < 174 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; nlinarith [hhi]
  · rw [div_lt_iff₀ hpos]; nlinarith [hlo]

/-- **[The top quark sits at the unit-coupling point]** `|v/√2 − m_top| < 1` GeV (`v ≈ 246`, `m_top ≈ 173`):
the top mass coincides with the natural mass `v/√2 ≈ 174 GeV` to within a GeV — this is *why* `y_top ≈ 1`.
The proof linking `topYukawa_near_one` to `yukawaCoupling_natural_mass`. -/
theorem top_at_natural_mass : |246 / Real.sqrt 2 - 173| < 1 := by
  obtain ⟨h1, h2⟩ := naturalMass_246_near_174
  rw [abs_lt]; constructor <;> linarith

/-! ## §C — link: the internal clock frequency sets the entropic decoherence rate -/

/-- **[The Compton clock drives the entropic decoherence rate]** for a fermion whose mass is its internal-clock
mass (`yukawaMass y v = comptonMass ω c ħ`), the entropy-production / decoherence rate is
`Ṡ_I = (√2 ω₀/(2ℏv))·(ħω/c²)` — *proportional to the internal clock frequency `ω`*. This links the
winding/Compton-clock mass (`Winding.NumberMass`) to the entropic decoherence rate
(`Yukawa.MassDecoherenceProportionality.yukawaEntropyRate`, the repo's `Ṡ_I` / Bender-width entropic-time core)
through the single Yukawa coupling: composing the clock-mass isolation with the existing
`yukawaEntropyRate_eq_const_mul_mass` (entropy rate ∝ mass). -/
theorem clockFrequency_sets_entropyRate (y v ω c ħ ω₀ ℏ : ℝ) (hv : v ≠ 0) (hℏ : ℏ ≠ 0)
    (h : yukawaMass y v = comptonMass ω c ħ) :
    yukawaEntropyRate y ω₀ ℏ = (Real.sqrt 2 * ω₀ / (2 * ℏ * v)) * comptonMass ω c ħ := by
  rw [yukawaEntropyRate_eq_const_mul_mass y v ω₀ ℏ hv hℏ, h]

end Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation

end

end
