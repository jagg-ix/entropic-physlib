/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZitterbewegungOperatorConsistency
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-!
# The quantum-walk coin angle is the mass

Kurzyński, *Relativistic effects in quantum walks: Klein's paradox and zitterbewegung*,
Phys. Lett. A **372** (2008) 6125–6129, studies the discrete-time quantum walk (DTQW) whose
continuum limit is the one-dimensional Dirac equation, and sets out "to show the relation between
the coin operator and the mass of the free relativistic particle by studying the zitterbewegung
frequency".

For a coin axis in the `X–Y` plane the step operator has eigenvalues

  `λ±(k) = cos(θ/2) cos k ± i √(1 − (cos(θ/2) cos k)²)`

and the trembling appears as `B(t) ≈ B cos[(E₊(k₀) − E₋(k₀)) t]` — an oscillation at the **energy
gap**, exactly as in the Dirac case.  At zero momentum the paper records
`λ±(0) = cos(θ/2) ± i sin(θ/2) = e^{±iθ/2}`, so the two branches sit at phases `±θ/2` and the gap
is `θ`.

That is the coin–mass relation.  `ElectronZitterbewegung` has `ω_Z = 2 ω_C` and, in natural units,
`ω_C = m`; matching the rest-frame gaps gives

  `θ = ω_Z = 2m`,  i.e. the coin angle is **twice the mass**.

So the walk's single tunable parameter is the mass, and the trembling frequency reads it off.  This
is the discrete counterpart of `ZitterbewegungOperatorConsistency`: there the factor of two comes
from the velocity anticommuting with `H`, here it comes from the two coin branches sitting at `±θ/2`
on the unit circle.  Both land on the same `ω_Z = 2m`.

What is formalized: the unit-circle (unitarity) property of the band, its rest value, and the gap
that fixes the coin–mass identification.  The Klein-paradox half of the paper — barrier transmission
in the walk — is not formalized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ### §A — The walk band lies on the unit circle -/

/-- The real part of the DTQW step-operator eigenvalue, `cos(θ/2) cos k`. -/
def coinBandValue (θ k : ℝ) : ℝ := Real.cos (θ / 2) * Real.cos k

/-- **The band value never leaves `[−1, 1]`**, so the square root below is real: a product of two
cosines is bounded by one. -/
theorem coinBandValue_abs_le_one (θ k : ℝ) : |coinBandValue θ k| ≤ 1 := by
  unfold coinBandValue
  rw [abs_mul]
  calc |Real.cos (θ / 2)| * |Real.cos k| ≤ 1 * 1 := by
        exact mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _)
          zero_le_one
    _ = 1 := by ring

/-- The upper DTQW band `λ₊ = c + i√(1 − c²)` written from its real part `c`. -/
def dtqwBand (c : ℝ) : ℂ := (c : ℂ) + Complex.I * ((Real.sqrt (1 - c ^ 2) : ℝ) : ℂ)

/-- **The walk is unitary: the band has modulus one.**  `|λ|² = c² + (1 − c²) = 1`, so the DTQW
eigenvalues sit on the unit circle and the walk conserves probability — the discrete counterpart of
the Dirac evolution being unitary. -/
theorem dtqwBand_normSq {c : ℝ} (hc : |c| ≤ 1) : Complex.normSq (dtqwBand c) = 1 := by
  have hnn : 0 ≤ 1 - c ^ 2 := by nlinarith [abs_le.mp hc]
  unfold dtqwBand
  simp [Complex.normSq_apply, Real.sq_sqrt hnn]
  nlinarith [Real.sq_sqrt hnn]

/-! ### §B — At rest the branches sit at `e^{±iθ/2}` -/

/-- **The rest-frame band value is `cos(θ/2)`.**  At zero momentum the walk's band reduces to the
coin's own cosine — the momentum dependence drops out. -/
theorem coinBandValue_at_zero (θ : ℝ) : coinBandValue θ 0 = Real.cos (θ / 2) := by
  unfold coinBandValue
  rw [Real.cos_zero, mul_one]

/-- **The rest branches are `cos(θ/2) ± i sin(θ/2)`.**  With `sin(θ/2) ≥ 0` the square root is
`sin(θ/2)` by the Pythagorean identity, so the upper branch is `e^{iθ/2}` and the lower its
conjugate — the paper's `λ±(0) = e^{±iθ/2}`. -/
theorem dtqwBand_at_rest {θ : ℝ} (hs : 0 ≤ Real.sin (θ / 2)) :
    dtqwBand (coinBandValue θ 0)
      = (Real.cos (θ / 2) : ℂ) + Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) := by
  rw [coinBandValue_at_zero]
  unfold dtqwBand
  congr 2
  have hpy : 1 - Real.cos (θ / 2) ^ 2 = Real.sin (θ / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  rw [hpy, Real.sqrt_sq hs]

/-! ### §C — The gap is the coin angle, hence twice the mass -/

/-- The rest-frame zitterbewegung frequency of the walk: the gap between the two branch phases
`+θ/2` and `−θ/2`. -/
def walkZitterFrequency (θ : ℝ) : ℝ := θ / 2 - (-(θ / 2))

/-- **The walk's trembling frequency is the coin angle.**  The two branches sit at `±θ/2`, so their
gap — the frequency of `B(t) ≈ B cos[(E₊ − E₋)t]` — is exactly `θ`. -/
theorem walkZitterFrequency_eq_coin_angle (θ : ℝ) : walkZitterFrequency θ = θ := by
  unfold walkZitterFrequency
  ring

/-- **The coin angle is twice the mass.**  Matching the walk's rest-frame gap to the Dirac
zitterbewegung frequency `ω_Z = 2 ω_C` with `ω_C = m c²/ħ` identifies `θ = 2 ω_C`: the single
tunable parameter of the coin *is* the mass, read off by the trembling.  This is the discrete
counterpart of the anticommutation factor of two in `ZitterbewegungOperatorConsistency`. -/
theorem coin_angle_eq_two_compton {θ m c ħ : ℝ}
    (hmatch : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    θ = 2 * comptonFrequency m c ħ := by
  rw [← walkZitterFrequency_eq_coin_angle θ]
  exact hmatch

/-- **The mass read off the trembling.**  Inverting the identification in natural units
(`c = ħ = 1`), the mass is half the coin angle. -/
theorem mass_eq_half_coin_angle {θ m : ℝ} (hm : 0 ≤ m)
    (hmatch : walkZitterFrequency θ = 2 * comptonFrequency m 1 1) :
    m = θ / 2 := by
  rw [walkZitterFrequency_eq_coin_angle] at hmatch
  unfold comptonFrequency at hmatch
  rw [hmatch]
  ring

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung

end
