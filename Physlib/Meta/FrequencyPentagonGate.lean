/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FrequencyPentagonWelds
public import Physlib.Meta.ZilAssert
public import Physlib.Meta.ZilGroupoidReport

/-!
# Gate: the five-carrier frequency pentagon is closed

Five frequency carriers from five sectors — `comptonFrequency` (the quantum clock),
`deBroglieFrequency` (its general-`E` form), `cyclotronRate` (magnetic precession),
`collisionRate` (kinetic theory), `regionFrequency` (cavity modes) — form a pentagon in the
bridge groupoid. This gate asserts, fail-closed on every build, that the pentagon is
categorically closed: all ten edges homogeneous AND proven.

**The discovery record.** `#zil_groupoid_report` found all ten edges dimensionally
homogeneous but the proven part *sparse*: two proven edges (Compton–de Broglie,
Compton–collision), one underived composite through them (de Broglie ⟷ collision), and two
carriers — cyclotron, region — sitting as isolated vertices, connected to nothing. This is
the third shape the sweep has met: the temperature hexagon was one closure step from
complete, the length pentagon had a proven spine with four predicted composites, and this
family was mostly *unexplored* — the groupoid's composite prediction covered one edge and
the remaining seven needed direct welds. All eight now live in
`Physlib.QuantumMechanics.ComplexAction.FrequencyPentagonWelds`, headlined by the Schwinger
critical field (`comptonFrequency_eq_cyclotronRate_iff`: `ω_c = ω_C` at `qBħ = γm²c²`).

Every carrier here is `G`-free, so there is no information-defect ladder: the pentagon is
asserted under one typing and the closure is typing-invariant. This gate imports only the
carriers' own modules rather than the `Physlib` root, so its environment pass sees exactly
the welds and the two historical flanks.
-/

#zil_assert_diagram Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
  Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation.cyclotronRate,
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.QuantumGravitySpatialOperators.collisionRate,
  Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation.regionFrequency
  with "m : M, E : L^2 T^-2 M, q : C, γ : 1, B : M T^-1 C^-1, vbar : L T^-1, ℓ : L, κ : L T^-1, L : L, ħ : L^2 T^-1 M"
