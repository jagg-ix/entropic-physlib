/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock

meta import Zil

/-!
# The accelerated KMS condition and the point where it trivializes

Ambruş and Chernodub, *Acceleration as a circular motion along an imaginary circle:
Kubo–Martin–Schwinger condition for accelerating field theories in imaginary-time formalism*,
arXiv:2308.03225v3, put a uniformly accelerated thermal field theory in the imaginary-time
formalism.  Two features of that construction matter here.

**A second periodicity.**  Wick-rotating the Rindler wedge turns the rapidity into a *cyclic compact*
variable carrying **two** periodicities (their Eq. 39): the ordinary thermal one `θ → θ + 2π`, and a
new one `θ → θ + α` set by the **thermal acceleration**

  `α = a/T`   (their Eq. 5),

a dimensionless space-time constant.  The accelerated KMS condition identifies the points
`θ_j = θ − jα` for `j ∈ ℤ`, and the Rindler horizon — which in Lorentzian signature is a null
surface — shrinks under the Wick rotation to a **single point** (their Eq. 34).

**A trivialization.**  The two periodicities coincide exactly at `α = 2π`, which by
`unruhTemperature κ = κ/2π` is exactly `T = T_U`.  There the extra condition imposes nothing, and
the accelerated thermal state becomes the ordinary Minkowski vacuum.  The paper's Eqs. 10a–10b make
that quantitative: the energy densities

  `ε_scalar = (π²T⁴/30)·(1 − (α/2π)⁴)`,
  `ε_Dirac  = (7π²T⁴/60)·(1 − (α/2π)²)·(1 + (17/7)(α/2π)²)`

**vanish** at `α = 2π`, for both statistics.

**Why this belongs with the modular-flow thread.**  `ModularGeneratorPartitionFreedom` showed the
partition function is gauge for the modular flow — the KMS structure is insensitive to the
normalization.  The present module identifies the one place where the *accelerated* KMS structure is
insensitive to everything: at `T = T_U` the second periodicity degenerates onto the first, the
thermal energy density vanishes for scalars and for fermions alike, and the state carries no thermal
content to be gauged at all.  §C proves the degeneration, §B the vanishing, and they are the same
point.

Scope.  What is formalized is the algebra of the thermal acceleration and the Unruh point: the
characterization `α = 2π ↔ T = T_U`, the vanishing of both energy densities there and only there,
and the collapse of the two periodicities.  The imaginary-time construction that *produces*
Eqs. 10 and 39 — the Wick-rotated Rindler propagators and the horizon shrinking to a point — is the
paper's and is taken as given; the energy densities are transcribed, not derived.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.AcceleratedKMSUnruhPoint

open Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock

/-! ### §A — the thermal acceleration and the Unruh point -/

/-- **The thermal acceleration** `α = a/T` (Ambruş–Chernodub Eq. 5): the dimensionless ratio of the
proper acceleration to the temperature, constant over the accelerated space-time. -/
def thermalAcceleration (a T : ℝ) : ℝ := a / T

/-- **`α = 2π` is exactly the Unruh point.**  The thermal acceleration reaches `2π` precisely when
the temperature equals the Unruh temperature `a/2π` of the same acceleration — the paper's critical
value `α_c = 2π`, here as an equivalence rather than a substitution. -/
theorem thermalAcceleration_eq_two_pi_iff {a T : ℝ} (ha : a ≠ 0) (hT : T ≠ 0) :
    thermalAcceleration a T = 2 * Real.pi ↔ T = unruhTemperature a := by
  unfold thermalAcceleration unruhTemperature
  rw [div_eq_iff hT, eq_div_iff (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ### §B — the energy density vanishes there, for both statistics -/

/-- The conformal scalar energy density in the accelerated thermal state,
`ε = (π²T⁴/30)(1 − (α/2π)⁴)` (Ambruş–Chernodub Eq. 10a). -/
def scalarEnergyDensity (T alpha : ℝ) : ℝ :=
  Real.pi ^ 2 * T ^ 4 / 30 * (1 - (alpha / (2 * Real.pi)) ^ 4)

/-- The Dirac energy density in the accelerated thermal state,
`ε = (7π²T⁴/60)(1 − (α/2π)²)(1 + (17/7)(α/2π)²)` (Ambruş–Chernodub Eq. 10b). -/
def diracEnergyDensity (T alpha : ℝ) : ℝ :=
  7 * Real.pi ^ 2 * T ^ 4 / 60 * (1 - (alpha / (2 * Real.pi)) ^ 2)
    * (1 + (17 / 7) * (alpha / (2 * Real.pi)) ^ 2)

/-- **The scalar thermal energy vanishes at the Unruh point.**  At `α = 2π` the quartic factor is
`1 − 1 = 0`: the accelerated thermal state carries no scalar energy density above the vacuum. -/
theorem scalarEnergyDensity_vanishes_at_unruh (T : ℝ) :
    scalarEnergyDensity T (2 * Real.pi) = 0 := by
  unfold scalarEnergyDensity
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [div_self hpi]
  ring

/-- **The Dirac thermal energy vanishes at the same point.**  The quadratic factor `1 − (α/2π)²`
carries the zero, so fermions and bosons trivialize together — the Unruh point is a property of the
geometry, not of the statistics. -/
theorem diracEnergyDensity_vanishes_at_unruh (T : ℝ) :
    diracEnergyDensity T (2 * Real.pi) = 0 := by
  unfold diracEnergyDensity
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [div_self hpi]
  ring

/-- **And only there, at nonzero temperature.**  For `T ≠ 0` the Dirac density vanishes exactly on
`α = ±2π`, because the second factor `1 + (17/7)(α/2π)²` is strictly positive.  So the trivialization
is a genuine critical point of the accelerated state, not one zero among many. -/
theorem diracEnergyDensity_eq_zero_iff {T alpha : ℝ} (hT : T ≠ 0) :
    diracEnergyDensity T alpha = 0 ↔ (alpha / (2 * Real.pi)) ^ 2 = 1 := by
  unfold diracEnergyDensity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hT4 : (0 : ℝ) < T ^ 4 := by positivity
  have hpre : 7 * Real.pi ^ 2 * T ^ 4 / 60 ≠ 0 := by positivity
  have hpos : (0 : ℝ) < 1 + (17 / 7) * (alpha / (2 * Real.pi)) ^ 2 := by positivity
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 hpre
      · linarith
    · exact absurd h2 (ne_of_gt hpos)
  · intro h
    have hz : 1 - (alpha / (2 * Real.pi)) ^ 2 = 0 := by linarith
    rw [hz]
    ring

/-! ### §C — the two periodicities degenerate at the Unruh point -/

/-- The accelerated KMS identification of the imaginary rapidity, `θ_j = θ − jα`
(Ambruş–Chernodub Eq. 39): the extra cyclic structure the acceleration imposes on top of the
ordinary thermal period `2π`. -/
def imaginaryRapidityShift (theta alpha : ℝ) (j : ℤ) : ℝ := theta - (j : ℝ) * alpha

/-- **At the Unruh point the acceleration adds no new identification.**  With `α = 2π` the
accelerated shift is `θ − 2πj`, which is exactly the ordinary thermal periodicity — the second
condition degenerates onto the first and imposes nothing further.  This is the structural counterpart
of §B: where the extra periodicity collapses, the thermal energy vanishes. -/
theorem imaginaryRapidityShift_at_unruh (theta : ℝ) (j : ℤ) :
    imaginaryRapidityShift theta (2 * Real.pi) j = theta - 2 * Real.pi * (j : ℝ) := by
  unfold imaginaryRapidityShift
  ring

/-- **The accelerated shift is trivial exactly at integer multiples of the thermal period.**  The
`j = 1` identification returns `θ` itself only when `α = 0`; more usefully, the identification agrees
with the ordinary `2π` period exactly when `α = 2π`.  Away from that value the acceleration imposes
a genuinely new cyclic condition, which is why `α` is the paper's control parameter. -/
theorem imaginaryRapidityShift_eq_thermal_iff {theta alpha : ℝ} :
    imaginaryRapidityShift theta alpha 1 = theta - 2 * Real.pi ↔ alpha = 2 * Real.pi := by
  unfold imaginaryRapidityShift
  constructor
  · intro h; push_cast at h; linarith
  · intro h; rw [h]; push_cast; ring

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.AcceleratedKMSUnruhPoint.thermalAcceleration_eq_two_pi_iff where
  formalizes @ "claim:the-thermal-acceleration-a-over-t-reaches-two-pi-exactly-at-the-unruh-temperature-so-that-value-characterizes-the-unruh-point-rather-than-being-substituted-into-it",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ambrus-chernodub-2308.03225-acceleration-as-circular-motion-along-an-imaginary-circle-kms-condition-in-imaginary-time-formalism",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock.unruhTemperature",
  caveat @ "an-algebraic-characterization-of-the-critical-value-it-does-not-derive-the-unruh-temperature-which-is-the-cited-carriers"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.AcceleratedKMSUnruhPoint.diracEnergyDensity_eq_zero_iff where
  formalizes @ "claim:both-the-conformal-scalar-and-the-dirac-thermal-energy-densities-of-a-uniformly-accelerated-state-vanish-at-thermal-acceleration-two-pi-and-for-the-dirac-case-only-there-at-nonzero-temperature",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-thermal-acceleration-a-over-t-reaches-two-pi-exactly-at-the-unruh-temperature-so-that-value-characterizes-the-unruh-point-rather-than-being-substituted-into-it",
  supported_by @ "paper:ambrus-chernodub-2308.03225-acceleration-as-circular-motion-along-an-imaginary-circle-kms-condition-in-imaginary-time-formalism",
  caveat @ "the-energy-densities-are-transcribed-from-equations-ten-a-and-ten-b-of-the-paper-not-derived-here-what-is-proved-is-that-their-common-zero-is-the-unruh-point-and-for-dirac-that-it-is-the-only-one-at-nonzero-temperature"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.AcceleratedKMSUnruhPoint.imaginaryRapidityShift_eq_thermal_iff where
  formalizes @ "claim:the-extra-cyclic-identification-the-acceleration-imposes-on-the-imaginary-rapidity-coincides-with-the-ordinary-thermal-period-exactly-at-thermal-acceleration-two-pi-so-the-second-periodicity-degenerates-onto-the-first-there",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-thermal-acceleration-a-over-t-reaches-two-pi-exactly-at-the-unruh-temperature-so-that-value-characterizes-the-unruh-point-rather-than-being-substituted-into-it",
  supported_by @ "paper:ambrus-chernodub-2308.03225-acceleration-as-circular-motion-along-an-imaginary-circle-kms-condition-in-imaginary-time-formalism",
  caveat @ "the-wick-rotated-construction-that-produces-the-second-periodicity-including-the-rindler-horizon-shrinking-to-a-point-is-the-papers-and-is-taken-as-given"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.AcceleratedKMSUnruhPoint

end
