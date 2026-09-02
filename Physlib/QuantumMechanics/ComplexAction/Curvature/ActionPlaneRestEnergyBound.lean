/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed

meta import Zil

/-!
# What the inertial rest energy allows the action plane to be

`ActionPlaneMetricRigidity` shows the Nagao–Nielsen action-plane metric is forced once boost
invariance and unit normalization are imposed: three coefficients, none of them free.  That is a
rigidity, so the natural question is where CAT/EPT could deviate at all, and whether measurement
permits it.

**Where the freedom actually sits.**  `LorentzViolationVariableLightSpeed` carries the one-parameter
family the rigidity rules out — an invariant speed `k` in place of `c`, with

  `E² = p²k² + E₀²`,  `E₀ = m₀k²`   (`modified_mass_shell`),

reducing to special relativity exactly at `k = c` (`lorentz_recovered`).  So the deviation is not
hidden in the geometry: it is a single dimensionless number, and it appears **in the inertial rest
energy**, which is measured directly.

**The bound.**  `E₀ = m₀k²` against `E₀ = m₀c²` gives a fractional deviation `k²/c² − 1`.  Rainville
*et al.*, *A direct test of E = mc²*, Nature **438**, 1096 (2005), compares nuclear binding-energy
mass deficits against γ-ray energies and confirms `E₀ = m₀c²` to `4 × 10⁻⁷`.  So

  `|k²/c² − 1| < 4 × 10⁻⁷`.

**The verdict, and it cuts both ways.**  CAT/EPT survives this test — but the rigidity explains why
in a way that is not flattering: **the survival margin is zero because the structure has no room to
differ.** Demanding invariance under the standard boost group forces `k = c` as a theorem
(§A below and `ActionPlaneMetricRigidity`), and the experiment then confirms what the geometry
already required. A theory that cannot deviate cannot be discriminated by the observable it cannot
deviate in.

This is §9's conclusion reached from the geometry side rather than the calibration side, and now
quantified: the action-plane route gives CAT/EPT a **rigid** foundation rather than a calibrated
one — a genuine improvement in kind — while leaving it observationally identical to special
relativity in this sector.

Scope.  The `k`-family and its mass shell are `LorentzViolationVariableLightSpeed`'s, transcribed.
What is added is the rest-energy reading of the deviation parameter and its confrontation with the
measured bound.  Nothing here shows CAT/EPT *requires* `k = c` on independent grounds; the rigidity
does that only for those who accept the standard boost group as the invariance.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ActionPlaneRestEnergyBound

open Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed

/-! ### §A — the deviation is a single number, and it lives in the rest energy -/

/-- The fractional deviation of the inertial rest energy from `m₀c²`, when the action plane is built
on an invariant speed `k` rather than `c`: `E₀ = m₀k²` gives `E₀/(m₀c²) − 1 = k²/c² − 1`. -/
def restEnergyDeviation (k c : ℝ) : ℝ := k ^ 2 / c ^ 2 - 1

/-- **The deviation vanishes exactly on the special-relativistic point.**  For nonzero `c`, the
inertial rest energy agrees with `m₀c²` if and only if `k² = c²` — so a single dimensionless number
carries the whole difference between the `k`-family and special relativity. -/
theorem restEnergyDeviation_eq_zero_iff {k c : ℝ} (hc : c ≠ 0) :
    restEnergyDeviation k c = 0 ↔ k ^ 2 = c ^ 2 := by
  unfold restEnergyDeviation
  rw [sub_eq_zero, div_eq_one_iff_eq (pow_ne_zero 2 hc)]

/-- **The rest energy carries the deviation linearly.**  `E₀ = m₀k² = m₀c²(1 + δ)` with
`δ = restEnergyDeviation k c`: the measured quantity in a direct `E = mc²` test is exactly
`1 + δ`, so an experimental bound on the rest energy is immediately a bound on `δ`. -/
theorem restEnergy_eq_mul_one_add_deviation {m₀ k c : ℝ} (hc : c ≠ 0) :
    m₀ * k ^ 2 = m₀ * c ^ 2 * (1 + restEnergyDeviation k c) := by
  unfold restEnergyDeviation
  field_simp
  ring

/-! ### §B — the special-relativistic point -/

/-- **The special-relativistic point has zero deviation.**  `k = c` gives `δ = 0`, so by §A the
`k`-family collapses to special relativity exactly there — and `lorentz_recovered` already supplies
the mass shell at that point, which is why no separate mass-shell corollary is stated here. -/
theorem restEnergyDeviation_self {c : ℝ} (hc : c ≠ 0) :
    restEnergyDeviation c c = 0 := by
  unfold restEnergyDeviation
  rw [div_self (pow_ne_zero 2 hc), sub_self]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.ActionPlaneRestEnergyBound.restEnergy_eq_mul_one_add_deviation where
  formalizes @ "claim:the-whole-difference-between-the-variable-invariant-speed-action-plane-and-special-relativity-is-one-dimensionless-number-appearing-directly-in-the-inertial-rest-energy",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed.modified_mass_shell",
  experimental_bound @ "value:rainville-et-al-nature-438-1096-2005-a-direct-test-of-e-equals-m-c-squared-confirms-the-rest-energy-to-four-parts-in-ten-million;test:the-action-plane-invariant-speed-must-satisfy-the-fractional-rest-energy-deviation-k-squared-over-c-squared-minus-one-below-four-times-ten-to-the-minus-seven-so-cat-ept-survives-with-zero-margin-because-the-rigidity-already-forces-k-equals-c",
  caveat @ "survival-here-is-not-discrimination-the-rigidity-leaves-no-room-to-deviate-so-the-observable-cannot-distinguish-cat-ept-from-special-relativity-in-this-sector"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Curvature.ActionPlaneRestEnergyBound

end
