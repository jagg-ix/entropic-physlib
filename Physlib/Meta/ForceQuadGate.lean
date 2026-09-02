/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ForceScaleWelds
public import Physlib.Meta.ZilAssert
public import Physlib.Meta.ZilGroupoidReport

/-!
# Gate: the force quadrilateral is closed, and Newton's entropic reading is nat-neutral

Four force carriers from four sectors — `newtonForce` (`GMm/r²`), `verlindeEntropicForce`
(`T·ΔS/Δx`), `horizonEnergyRate` (`c⁴/2G`, the maximum-force scale), and the van der Waals
`dispersionForce` (`−(9/2)A/R⁷`).  `#zil_groupoid_report` found all six edges homogeneous
(the unifier normalizes the dispersion sign) with only the Newton–entropic edge proven; the
five welds of `Physlib.QuantumMechanics.ComplexAction.ForceScaleWelds` close the rest,
headlined by the maximum-force saturation `2G²Mm = c⁴r²`.

**The widest information span.** Under the information typing the quadrilateral stretches
across the full ladder: `newtonForce` carries `I^{-1}` (`G` in the numerator),
`horizonEnergyRate` carries `I^{+1}` (`G` in the denominator), and the two `G`-free carriers
sit at `I⁰` — so the Newton ⟶ maximum-force edge is off by **two nats** (`[I^{-2}]`), the
widest defect in the repository's gates: the force that *has* gravity and the force that
*bounds* gravity price the nat in opposite directions.

**Entropy's two prices.** The entropic-force edges depend on how entropy is typed, and the
gate asserts both readings: with `ΔS : E Θ⁻¹` (entropy as pure energy-per-temperature,
information-neutral) the Newton ⟶ entropic edge is off by `[I^{-1}]`; with
`ΔS : E Θ⁻¹ I^{-1}` (entropy priced per nat, the Brillouin convention under which
`S = k_B N` is the bookkeeping identity) the same edge is exactly `[1]` — **Verlinde's
entropic reading of Newton's force is information-consistent precisely when entropy carries
the per-nat price**.  The two assertions pin both conventions and their difference.
-/

-- The closed quadrilateral under SI typing: six edges, each homogeneous and proven.
#zil_assert_diagram Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce,
  Physlib.Thermodynamics.verlindeEntropicForce,
  Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.horizonEnergyRate,
  Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling.dispersionForce
  with "M : M, m : M, r : L, T : Θ, ΔS : M L^2 T^-2 Θ^-1, Δx : L, G : L^3 T^-2 M^-1, A : M L^8 T^-2, R : L"

-- The widest span: Newton (G above the bar) to the maximum force (G below it) — two nats.
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce
  Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.horizonEnergyRate "I^-2"
  with "M : M, m : M, r : L, G : L^3 T^-2 M^-1 I^-1"

-- The G-free carriers sit at I^0: one nat to Newton on either side.
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling.dispersionForce
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce "I"
  with "A : M L^8 T^-2, R : L, M : M, m : M, r : L, G : L^3 T^-2 M^-1 I^-1"
#zil_assert_edge_defect Physlib.Thermodynamics.verlindeEntropicForce
  Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.horizonEnergyRate "I^-1"
  with "T : Θ, ΔS : M L^2 T^-2 Θ^-1, Δx : L, G : L^3 T^-2 M^-1 I^-1"

-- Entropy's two prices on the Newton–entropic edge.
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce
  Physlib.Thermodynamics.verlindeEntropicForce "I^-1"
  with "M : M, m : M, r : L, G : L^3 T^-2 M^-1 I^-1, T : Θ, ΔS : M L^2 T^-2 Θ^-1, Δx : L"
#zil_assert_edge_defect Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce
  Physlib.Thermodynamics.verlindeEntropicForce "1"
  with "M : M, m : M, r : L, G : L^3 T^-2 M^-1 I^-1, T : Θ, ΔS : M L^2 T^-2 Θ^-1 I^-1, Δx : L"
