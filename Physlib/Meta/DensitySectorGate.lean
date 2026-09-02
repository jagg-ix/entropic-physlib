/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.DensitySectorWelds
public import Physlib.Meta.ZilAssert
public import Physlib.Meta.ZilGroupoidReport

/-!
# Gate: the density quadrilateral is closed, with its Θ- and I-defect ladders

Five density-sector carriers: `criticalDensity` (`3H²/8πG`), `vacuumEnergyDensity`
(`Λc²/8πG`), black-body `energyDensity` (`bT⁴`), `radiationPressure` (`ρ/3`), and
`entropyDensity` (`(4/3)bT³`).  `#zil_groupoid_report` found the first four mutually
homogeneous but almost disconnected — only the radiation trio's internal relations proven,
the two `G`-carrying cosmological densities isolated vertices.  The five welds of
`Cosmology.FLRW.DensitySectorWelds` (exact de Sitter, the radiation-dominated Friedmann
relation, the radiation–vacuum equality temperature, and the two pressure forms) close the
quadrilateral, asserted fail-closed below.

**Two defect ladders.** `entropyDensity` is *deliberately not* in the closed diagram: it is
exactly one temperature unit off every density edge (`s = (4/3)bT³` vs `ρ = bT⁴`), and the
`[Θ]` assertions pin that offset as structure rather than hiding it.  Under the
information-extended typing of `G` the density sector's information ladder **inverts**
relative to the temperature/length gates: `G` sits in the *denominator* of the holographic
densities, so `criticalDensity` and `vacuumEnergyDensity` carry `I^{+1}` — a density is
bits-per-volume-priced — while the radiation carriers stay at `I⁰`.  The `[I]` assertions
enforce the inverted rung, `[1]` the within-rung cancellation, and the final `[Θ I]`
assertion is a genuinely two-axis defect: the holographic-to-entropy edge is off by one
temperature unit AND one nat at once. -/

-- The closed quadrilateral under SI typing: six edges, each homogeneous and proven.
#zil_assert_diagram Cosmology.FLRW.DensityParameters.criticalDensity,
  Cosmology.FLRW.MatterContent.vacuumEnergyDensity,
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.energyDensity,
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.radiationPressure
  with "H : T^-1, G : L^3 T^-2 M^-1, Λ : L^-2, b : M L^-3 Θ^-4, T : Θ, ρ : M L^-3"

-- The Θ ladder: the entropy density is one temperature unit off every density carrier.
#zil_assert_edge_defect Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.energyDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.entropyDensity "Θ"
  with "b : M L^-3 Θ^-4, T : Θ"
#zil_assert_edge_defect Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.radiationPressure
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.entropyDensity "Θ"
  with "ρ : M L^-3, b : M L^-3 Θ^-4, T : Θ"
#zil_assert_edge_defect Cosmology.FLRW.DensityParameters.criticalDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.entropyDensity "Θ"
  with "H : T^-1, G : L^3 T^-2 M^-1, b : M L^-3 Θ^-4, T : Θ"
#zil_assert_edge_defect Cosmology.FLRW.MatterContent.vacuumEnergyDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.entropyDensity "Θ"
  with "Λ : L^-2, G : L^3 T^-2 M^-1, b : M L^-3 Θ^-4, T : Θ"

-- The inverted information ladder: holographic densities carry I^{+1} (G in the
-- denominator), radiation carriers I^0.
#zil_assert_edge_defect Cosmology.FLRW.DensityParameters.criticalDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.energyDensity "I"
  with "H : T^-1, G : L^3 T^-2 M^-1 I^-1, b : M L^-3 Θ^-4, T : Θ"
#zil_assert_edge_defect Cosmology.FLRW.DensityParameters.criticalDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.radiationPressure "I"
  with "H : T^-1, G : L^3 T^-2 M^-1 I^-1, ρ : M L^-3"
#zil_assert_edge_defect Cosmology.FLRW.MatterContent.vacuumEnergyDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.energyDensity "I"
  with "Λ : L^-2, G : L^3 T^-2 M^-1 I^-1, b : M L^-3 Θ^-4, T : Θ"
#zil_assert_edge_defect Cosmology.FLRW.MatterContent.vacuumEnergyDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.radiationPressure "I"
  with "Λ : L^-2, G : L^3 T^-2 M^-1 I^-1, ρ : M L^-3"
#zil_assert_edge_defect Cosmology.FLRW.DensityParameters.criticalDensity
  Cosmology.FLRW.MatterContent.vacuumEnergyDensity "1"
  with "H : T^-1, G : L^3 T^-2 M^-1 I^-1, Λ : L^-2"

-- The two-axis defect: holographic ⟶ entropy is one temperature unit and one nat at once.
#zil_assert_edge_defect Cosmology.FLRW.DensityParameters.criticalDensity
  Physlib.Relativity.SemiClassical.SelfGravitatingRadiation.entropyDensity "Θ I"
  with "H : T^-1, G : L^3 T^-2 M^-1 I^-1, b : M L^-3 Θ^-4, T : Θ"
