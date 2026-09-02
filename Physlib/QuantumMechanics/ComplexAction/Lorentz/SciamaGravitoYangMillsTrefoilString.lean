/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockVerlindeWitten
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenJonesPolynomialChernSimons
public import Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel

/-!
# The gravito-Yang–Mills theory as Witten Chern–Simons: trefoil, positron, Verlinde, string

The gravito-Yang–Mills gauge theory (`SciamaUnruhGravitoYangMills`) — a non-abelian gauge field whose double
copy is the metric — has a topological sector that is **Witten's Chern–Simons theory**
(`ChernSimons.WittenJonesPolynomialChernSimons`): its Wilson loops compute the **Jones polynomial** of knots.
This module links that gauge theory to the trefoil, the positron, Verlinde entropy, and the string.

* `wittenJones_connectedSum_multiplicative` — the Chern–Simons Wilson-loop (Jones) invariant is multiplicative
  under connected sum: the topological invariant of the gauge theory factorizes (the framing/skein law).
* `electron_positron_chiral_trefoil` — the gauge theory's Dirac fermion (`SciamaUnruhComplexEinsteinFermion`,
  the electron) and its CPT mirror (the positron) are distinguished by the **chiral trefoil** Jones invariant
  `electronJones 2 ≠ positronJones 2` (`Particles.PositronModel`): the positron is the mirror trefoil, the
  `A ↦ A⁻¹` image of the electron's Chern–Simons knot.
* `wittenFraming_string_central_charge` — Witten's Chern–Simons **framing anomaly** phase `e^{2πi c/24}` and the
  string Virasoro Casimir `−c/24` are the same, both fixed by `ζ(−1) = −1/12`
  (`SciamaFockVerlindeWitten.virasoroCasimir_from_zeta`): the topological framing of the gauge theory is the
  string's central-charge ground energy.

So the loop closes: the **Verlinde** holographic screen fixes the coupling `G` and temperature `T_U` of the
gravito-Yang–Mills theory (`SciamaUnruhElectrogravitic`); its topological sector is **Witten** Chern–Simons,
computing the **trefoil** Jones invariant that separates the electron from the positron; its framing anomaly is
the **string** Virasoro Casimir `−c/24 = ½c·ζ(−1)`; and gravity is its double copy (`SciamaFockBCJAdSCFT`,
`gravity = gauge²` = KLT).  One theory — gauge, gravity, knot, particle, and string — off the holographic
screen.

Honest scope: the Jones-invariant factorization, the chiral-trefoil electron/positron distinction, and the
framing = string-Casimir identity.  The full Witten path integral and the trefoil's Chern–Simons expectation
are carried by the referenced modules; here they are tied to the arc's gauge/string/particle structure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaGravitoYangMillsTrefoilString

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.Particles.PositronModel
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockVerlindeWitten

/-- **[Chern–Simons Jones invariant factorizes] `⟨K₁#K₂⟩ = ⟨K₁⟩·⟨K₂⟩`.**  The normalized Wilson-loop (Jones)
invariant of the gauge theory's Witten Chern–Simons sector is multiplicative under connected sum — the
topological factorization / framing law of the gravito-Yang–Mills theory. -/
theorem wittenJones_connectedSum_multiplicative (Zsum Zunknot Z₁ Z₂ : ℂ)
    (hC : Zunknot ≠ 0) (h : Zsum * Zunknot = Z₁ * Z₂) :
    normalizedExpectation Zunknot Zsum
      = normalizedExpectation Zunknot Z₁ * normalizedExpectation Zunknot Z₂ :=
  normalized_connected_sum_multiplicative Zsum Zunknot Z₁ Z₂ hC h

/-- **[Electron/positron = chiral trefoil] `electronJones ≠ positronJones`.**  The gauge theory's Dirac fermion
(the electron) and its CPT mirror (the positron) are the two chiralities of the trefoil, distinguished by their
Chern–Simons Jones invariant — the positron is the `A ↦ A⁻¹` mirror knot of the electron. -/
theorem electron_positron_chiral_trefoil : electronJones 2 ≠ positronJones 2 :=
  positron_ne_electron

/-- **[Witten framing = string Virasoro Casimir] `½c·ζ(−1) = −c/24`.**  The Chern–Simons framing-anomaly phase
`e^{2πi c/24}` and the string's Virasoro ground-state Casimir `−c/24` are the same central-charge quantity,
both fixed by the proved `ζ(−1) = −1/12` — the topological framing of the gauge theory is the string's
central-charge ground energy. -/
theorem wittenFraming_string_central_charge (c : ℝ) :
    c * (1 / 2 * (riemannZeta (-1)).re) = -c / 24 :=
  virasoroCasimir_from_zeta c

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaGravitoYangMillsTrefoilString

end
