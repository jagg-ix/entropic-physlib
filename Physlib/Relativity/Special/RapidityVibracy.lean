/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.HyperbolicBoost

/-!
# Rapidity as vibracy — the logarithmic frequency of the Quantum Inertial Frame

Wilkins–Williams (2001) observe that **rapidity** (the additive parameter of a Lorentz boost) and
Misner/Lévy-Leblond **linear time** (the additive cosmic time `H₀⁻¹ ln[R/R₀]`) are the *same* quantity:
a logarithmic measure of frequency shift, which they call **vibracy** `δ = ln(ν/ν₀)`. Any additive
parameter of a one-parameter transformation group is the logarithm of a multiplicative frequency
ratio.

This supplies the missing **log-frequency bridge** of the Quantum Inertial Frame cluster
(`Relativity.Special.QIF*`): the QIF's boost parameter (`QIFLorentzFrameChange`) and its entropic
`S_I/ℏ`-time (which is `log K`, `EntanglementEntropy.renyi2Entropy`) are two faces of vibracy —
kinetic log-frequency and cosmological/information log-frequency.

* **§A — vibracy and the log-Doppler rapidity.** `vibracy ν ν₀ = ln(ν/ν₀)`; the boost's Doppler ratio
 is `cosh α + sinh α = eᵅ` (`dopplerRatio_eq_exp`), so rapidity is the log-Doppler shift
 (`rapidity_eq_log_dopplerRatio`).
* **§B — additivity (composition).** The Doppler ratios of composed boosts multiply
 (`dopplerRatio_add`) — the additivity of rapidity `α₃ = α₁ + α₂`; vibracy of a frequency chain adds
 (`vibracy_chain`), the conservation law of total vibracy.
* **§C — Misner/Lévy-Leblond linear time.** `linearTime H₀ R R₀ = H₀⁻¹ · vibracy R R₀` — the additive
 cosmic time (`linearTime_additive`), the same log-frequency structure as the entropic time.
* **§D — the QIF/quantum-information bridge.** The velocity of a rapidity is `tanh α` (subluminal,
 reusing `abs_tanh_lt_one`); and vibracy of the Schmidt number `K` against the reference `1` is
 `log K` (`vibracy_one_eq_log`) — the Rényi-2 entanglement entropy / entropic time. Kinetic rapidity
 and information entropic time are the same vibracy.

Proven: the log-Doppler identity, the multiplicative→additive composition, the
linear-time additivity, and the `vibracy K 1 = log K` bridge. Interpretive: the unification of
rapidity, linear time, and entanglement entropy *as* one quantity ("vibracy") is Wilkins–Williams'
reading, supported by these shared logarithmic identities.

## References

* D. Wilkins, D. Williams, "From rapidity to vibracy (logarithmic frequency)", Am. J. Phys. **69**,
 158 (2001) [`Wilkins:2001vibracy`]; C. W. Misner, J.-M. Lévy-Leblond (linear time). Reuses
 `Relativity.Special.HyperbolicBoost` (`abs_tanh_lt_one`); connects `Relativity.Special.QIF*` and
 `MuonAnomaly.EntanglementEntropy` (`renyi2Entropy = log K`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Relativity.Special.RapidityVibracy

/-! ## §A — vibracy and the log-Doppler rapidity -/

/-- **Vibracy** `δ = ln(ν/ν₀)` — the logarithmic frequency shift (Wilkins–Williams Eq. 9). -/
noncomputable def vibracy (ν ν₀ : ℝ) : ℝ := Real.log (ν / ν₀)

/-- **The boost Doppler ratio is `eᵅ`**: `cosh α + sinh α = exp α` (Wilkins–Williams Eq. 7). -/
theorem dopplerRatio_eq_exp (α : ℝ) : Real.cosh α + Real.sinh α = Real.exp α := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- **Rapidity is the log-Doppler shift**: `α = ln(cosh α + sinh α) = ln(ν₀/ν)` — the boost parameter
is the vibracy of the relativistic Doppler shift. -/
theorem rapidity_eq_log_dopplerRatio (α : ℝ) : α = Real.log (Real.cosh α + Real.sinh α) := by
  rw [dopplerRatio_eq_exp, Real.log_exp]

/-! ## §B — additivity: the composition of boosts is the addition of rapidities -/

/-- **The Doppler ratios of composed boosts multiply**: `D(α + β) = D(α) · D(β)` — the multiplicative
frequency shift whose logarithm is the additivity of rapidity `α₃ = α₁ + α₂`. -/
theorem dopplerRatio_add (α β : ℝ) :
    Real.cosh (α + β) + Real.sinh (α + β)
      = (Real.cosh α + Real.sinh α) * (Real.cosh β + Real.sinh β) := by
  rw [dopplerRatio_eq_exp, dopplerRatio_eq_exp, dopplerRatio_eq_exp, Real.exp_add]

/-- **Vibracy is additive along a frequency chain** (conservation of total vibracy): a shift `ν₀ → ν₂`
factoring through `ν₁` has vibracy the sum of the parts (Wilkins–Williams Eq. 5/13). -/
theorem vibracy_chain (ν₀ ν₁ ν₂ : ℝ) (h0 : ν₀ ≠ 0) (h1 : ν₁ ≠ 0) (h2 : ν₂ ≠ 0) :
    vibracy ν₂ ν₀ = vibracy ν₂ ν₁ + vibracy ν₁ ν₀ := by
  unfold vibracy
  rw [Real.log_div h2 h0, Real.log_div h2 h1, Real.log_div h1 h0]; ring

/-! ## §C — Misner/Lévy-Leblond linear time -/

/-- **Linear (Misner/Lévy-Leblond) time** `θ = H₀⁻¹ ln[R/R₀]` — the additive cosmic time, the vibracy
of the scale factor (Wilkins–Williams Eqs. 6, 8). -/
noncomputable def linearTime (H₀ R R₀ : ℝ) : ℝ := vibracy R R₀ / H₀

/-- **Linear time is additive** over a chain of scale factors (Wilkins–Williams Eq. 5): the same
additivity as rapidity — both are vibracy. -/
theorem linearTime_additive (H₀ R₀ R₁ R₂ : ℝ) (h0 : R₀ ≠ 0) (h1 : R₁ ≠ 0) (h2 : R₂ ≠ 0) :
    linearTime H₀ R₂ R₀ = linearTime H₀ R₂ R₁ + linearTime H₀ R₁ R₀ := by
  unfold linearTime
  rw [vibracy_chain R₀ R₁ R₂ h0 h1 h2, add_div]

/-! ## §D — the QIF / quantum-information bridge -/

/-- **The velocity of a rapidity is subluminal**: `β = tanh α`, `|β| < 1` (reusing
`abs_tanh_lt_one`) — the QIF boost parameter maps to a sub-light velocity. -/
theorem rapidity_velocity_subluminal (α : ℝ) : |Real.tanh α| < 1 :=
  Physlib.Relativity.Special.abs_tanh_lt_one α

/-- **Vibracy is the entanglement/entropic log-frequency**: the vibracy of the Schmidt number `K`
against the reference `1` is `log K` — the Rényi-2 entanglement entropy `S₂ = log K`
(`MuonAnomaly.EntanglementEntropy.renyi2Entropy`) and the entropic time. So the QIF's kinetic rapidity
and its information-theoretic entropic time are the same vibracy. -/
theorem vibracy_one_eq_log (K : ℝ) : vibracy K 1 = Real.log K := by
  unfold vibracy; rw [div_one]

/-- **The rapidity–entanglement unification (Wilkins–Williams vibracy, one theorem).** When a Lorentz
boost's **Doppler frequency ratio** `cosh α + sinh α` coincides with a bipartite state's **Schmidt
number** `K`, the boost **rapidity equals the Rényi-2 entanglement entropy** `α = log K = S₂` — the
QIF entropic time. Kinematic rapidity and information entropy are one and the same vibracy, read off
the same frequency ratio: `α = vibracy K 1`. -/
theorem rapidity_eq_entanglementEntropy_of_doppler_eq_schmidt (α K : ℝ)
    (hDoppler : Real.cosh α + Real.sinh α = K) : α = Real.log K := by
  rw [← hDoppler, dopplerRatio_eq_exp, Real.log_exp]

end Physlib.Relativity.Special.RapidityVibracy
