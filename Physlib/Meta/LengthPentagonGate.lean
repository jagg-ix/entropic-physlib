/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
public import Physlib.Meta.ZilAssert
public import Physlib.Meta.ZilGroupoidReport

/-!
# Gate: the five-carrier length pentagon is closed, with its half-nat ladder

Five length scales from four sectors — `schwarzschildRadius` (gravity's horizon scale),
`gravitationalLength` (its unit-mass half), `comptonWavelength` (the quantum scale),
`planckLength` (their geometric mean), `hubbleRadius` (the cosmological scale) — form a
pentagon in the bridge groupoid. This gate asserts, fail-closed on every build, that the
pentagon is categorically closed: all ten edges of the complete graph carry a dimensionally
homogeneous bridge constraint AND a connecting theorem.

**The discovery record.** `#zil_groupoid_report` on these five carriers found all ten edges
homogeneous but only six proven, and surfaced exactly four underived composites —
Schwarzschild ⟷ gravitational, Schwarzschild ⟷ Planck, gravitational ⟷ Hubble,
Planck ⟷ Hubble — every one reachable through proven flanks (the `λ_c·λ_g = ℓ_P²` /
geometric-mean welds of `ZeroPointLength` and the Hubble welds of
`HorizonEntropyExpansion`). The four closing welds now live in
`Cosmology.FLRW.HorizonEntropyExpansion` §F: `schwarzschildRadius_eq_two_gravitationalLength`,
`schwarzschildCompton_eq_two_planckLength_sq`, `gravitationalLength_eq_hubbleRadius_iff`
(`GmH = c³`, the Hoyle–Carvalho mass), `planckLength_eq_hubbleRadius_iff` (`GħH² = c⁵`).

**The half-nat ladder.** Under the information-extended typing (`G : L³ T⁻² M⁻¹ I⁻¹` — the
Brillouin/Landauer bookkeeping) the five carriers sit on three information rungs:

* `I⁰` — `comptonWavelength`, `hubbleRadius` (no `G`);
* `I^{-1/2}` — `planckLength` (`√G`: half of `G`'s information charge, the ℝ-level fact
  behind `ZeroPointLength.planckLengthSq_mul_planckMassSq`);
* `I⁻¹` — `schwarzschildRadius`, `gravitationalLength` (one full `G`).

Every edge's signed defect is the rung difference, and the assertions below enforce the whole
ladder: `[I]` across two rungs, `[I^1/2]` across one, `[1]` within the gravitational rung —
the geometric mean of gravity's length and quantum mechanics' length carries exactly **half a
nat**, build-checked. The pentagon itself is asserted under the information-free SI typing,
the same double-typing discipline as `Physlib.Meta.TemperaturePentagonGate`.
-/

-- The full pentagon under SI typing: ten edges, each homogeneous and proven.
#zil_assert_diagram Physlib.Relativity.SemiClassical.schwarzschildRadius,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLength,
  Cosmology.FLRW.Distances.hubbleRadius
  with "M : M, m : M, G : L^3 T^-2 M^-1, H : T^-1, ħ : L^2 T^-1 M"

-- The ladder, rung by rung, under the information-extended typing of G.
-- Two rungs apart (kinematic ⟶ gravitational): one full nat.
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
  Physlib.Relativity.SemiClassical.schwarzschildRadius "I"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, ħ : L^2 T^-1 M"
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength "I"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, ħ : L^2 T^-1 M"
#zil_assert_edge_defect Cosmology.FLRW.Distances.hubbleRadius
  Physlib.Relativity.SemiClassical.schwarzschildRadius "I"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, H : T^-1, ħ : L^2 T^-1 M"
#zil_assert_edge_defect Cosmology.FLRW.Distances.hubbleRadius
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength "I"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, H : T^-1, ħ : L^2 T^-1 M"
-- One rung apart (any carrier ⟶ the Planck length, or back): half a nat.
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLength "I^1/2"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, ħ : L^2 T^-1 M"
#zil_assert_edge_defect Cosmology.FLRW.Distances.hubbleRadius
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLength "I^1/2"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, H : T^-1, ħ : L^2 T^-1 M"
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLength
  Physlib.Relativity.SemiClassical.schwarzschildRadius "I^1/2"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, ħ : L^2 T^-1 M"
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.planckLength
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength "I^1/2"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, ħ : L^2 T^-1 M"
-- Within the gravitational rung: the information charge cancels edge-internally.
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.gravitationalLength
  Physlib.Relativity.SemiClassical.schwarzschildRadius "1"
  with "M : M, m : M, G : L^3 T^-2 M^-1 I^-1, ħ : L^2 T^-1 M"
