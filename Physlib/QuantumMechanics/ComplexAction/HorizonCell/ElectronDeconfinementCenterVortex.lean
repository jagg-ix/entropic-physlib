/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronChargeChiralitySU5
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
public import Physlib.QuantumMechanics.ComplexAction.Su5ElectroweakParticleLinks
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

/-!
# The electron's charge is a center-vortex N-ality: deconfinement from a trivial center element

Improves `ElectronChargeChiralitySU5` with the confinement-mechanism insight of Dehghan–Faber (*What do we know
about the confinement mechanism?*, arXiv:2412.10767): a Wilson loop picks up a **center element** of the gauge
group determined by the representation's **N-ality**, and confinement is the nontrivial-center (area-law) case.
This is exactly the repository's `colourCentre_triality` (`ωⁿ = 1 ⟺ 3∣n`, the `ℤ/3` center of `SU(3)`), and it
explains — in the *same* Wilson-loop/center framework the electron-cell arc built — why the electron is a **free
lepton** while quarks confine.

The electron sits in the `SU(5)` `5̄` with electric charge `Q(e⁻) = su5AntifundCharge 3 = windingCharge(−3) = −1`
(`ElectronChargeChiralitySU5`, `su5_electron_charge`). Its winding `−3` is divisible by `3`, so:

* its **`ℤ/3` color center element is trivial** `ω^{−3} = 1` (`electron_colour_singlet`) — a color singlet;
* being a color singlet is **equivalent to integer charge** (`electron_deconfined_iff_integer_charge`,
  `confinement_singlet_iff_integer_charge`): the center-vortex confinement criterion — a *trivial* center element
  gives no area law, so the electron is **deconfined / seen free**;
* a single quark (winding `2`, charge `2/3`) has a **nontrivial center** `ω² ≠ 1` (`quark_confined`,
  `quark_not_colour_singlet`) — it is confined, never free;
* the electron's **`ℤ/2` fermion-sign center element** is `ribbonTwist(1/2) = −1` (`electron_fermion_center`) —
  the sign a spin Wilson loop / center projection `Z_μ = signTr[U] = ±1` (Dehghan–Faber Eq. 2) picks up.

So the charge/chirality of `ElectronChargeChiralitySU5` is a **center Z(N) N-ality**: the electron's Wilson loop
picks up its center element, which is trivial for the color `ℤ/3` (a color singlet ⟹ deconfined, integer-charged)
and `−1` for the fermion `ℤ/2` (the spin sign). Charge conjugation `5̄ ↔ 5` is a center transformation; the
electron is free precisely because its color center element is trivial.

* **§A — the electron is a color singlet (trivial center)** (`electron_colour_singlet`).
* **§B — deconfinement ⟺ integer charge** (`electron_deconfined_iff_integer_charge`).
* **§C — the SU(5) `5̄` charge is the winding / N-ality** (`electron_su5_charge_is_winding`); the quark is
  confined (`quark_confined`); the fermion Z(2) center (`electron_fermion_center`).
* **§D — assembled** (`electron_center_vortex_deconfinement`).

**Honest layering.** Every statement is exact reuse: `colourCentre_triality`,
`confinement_singlet_iff_integer_charge`, `quark_not_colour_singlet`, `su5_electron_charge`,
`ribbonTwist_fermion`. The content is the *identification* — the arc's charge/chirality is the center-vortex
N-ality of Dehghan–Faber, and the electron's trivial color center is its deconfinement. No lattice/string-tension
dynamics is formalized. ## References

* Z. Dehghan, M. Faber, arXiv:2412.10767 (center-vortex confinement, N-ality, center projection `Z_μ=signTr[U]`).
  Repo carriers: `Particles.StrongInteractionColorOctet`, `Winding.QuarkChargeWinding`,
  `Su5ElectroweakParticleLinks`, `Hopf.ChargeConjugationRibbonTwist`,
  `HorizonCell.ElectronChargeChiralitySU5`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
open Physlib.QuantumMechanics.ComplexAction.Su5ElectroweakParticleLinks
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronDeconfinementCenterVortex


/-- **[The electron's color center element is trivial] `ω^{−3} = 1`.** The electron's winding `−3` (its `SU(5)`
`5̄` charge, `su5AntifundCharge 3 = windingCharge(−3)`) is divisible by `3`, so its `ℤ/3` color center element is
trivial — a color singlet. The Wilson loop of the electron picks up the identity center element: no confining
area law (Dehghan–Faber center-vortex criterion). -/
lemma electron_colour_singlet : cubeRoot ^ (-3 : ℤ) = 1 :=
  (colourCentre_triality (-3)).mpr (by decide)


/-- **[The electron is deconfined ⟺ integer charge].** The electron's `ℤ/3` color center is trivial (a color
singlet, `ω^{−3} = 1`) **iff** its charge `windingCharge(−3) = −1` is an integer — the center-vortex confinement
criterion: only color singlets carry a trivial center element, so only they escape the confining area law and
are seen free. The electron is the integer-charged, trivial-center, *deconfined* leptonic member of the `5̄`. -/
lemma electron_deconfined_iff_integer_charge :
    cubeRoot ^ (-3 : ℤ) = 1 ↔ ∃ k : ℤ, windingCharge (-3) = (k : ℚ) :=
  confinement_singlet_iff_integer_charge (-3)


/-- **[The electron's `SU(5)` `5̄` charge is its winding / N-ality] `su5AntifundCharge 3 = windingCharge(−3)`.**
The charge-chirality label of `ElectronChargeChiralitySU5` is the winding `−3` — the center `ℤ/3` N-ality that
the Wilson loop reads off. -/
lemma electron_su5_charge_is_winding : su5AntifundCharge 3 = windingCharge (-3) :=
  su5_electron_charge

/-- **[A single quark is confined] `ω² ≠ 1`.** An up-type quark (winding `2`, charge `2/3`) has a nontrivial
`ℤ/3` center element `ω² ≠ 1`: its Wilson loop carries a nontrivial center = a confining area law — never seen
free (unlike the color-singlet electron). -/
lemma quark_confined : cubeRoot ^ (2 : ℤ) ≠ 1 :=
  quark_not_colour_singlet

/-- **[The electron's `ℤ/2` fermion-sign center element] `ribbonTwist(1/2) = −1`.** The spin Wilson loop / center
projection `Z_μ = signTr[U] = ±1` (Dehghan–Faber Eq. 2) picks up the `ℤ/2` center element `−1` for the spin-½
electron — the fermion sign, the exclusion-statistics center of the arc's mutex cell. -/
lemma electron_fermion_center : ribbonTwist (1 / 2) = -1 :=
  ribbonTwist_fermion


/-- **[The electron's charge as a center-vortex N-ality, assembled].** The electron's `SU(5)` `5̄` charge is the
winding `−3` (its center `ℤ/3` N-ality); that N-ality is divisible by `3`, so:

* its color center element is trivial `ω^{−3} = 1` — a color singlet;
* trivial color center ⟺ integer charge — the center-vortex deconfinement criterion, so the electron is free;
* a quark's center is nontrivial `ω² ≠ 1` — confined;
* the electron's `ℤ/2` fermion center is `ribbonTwist(1/2) = −1`.

The charge/chirality of the arc is a center Z(N) N-ality; the electron is free precisely because its color center
element is trivial, while quarks confine. -/
lemma electron_center_vortex_deconfinement :
    cubeRoot ^ (-3 : ℤ) = 1
      ∧ (cubeRoot ^ (-3 : ℤ) = 1 ↔ ∃ k : ℤ, windingCharge (-3) = (k : ℚ))
      ∧ su5AntifundCharge 3 = windingCharge (-3)
      ∧ cubeRoot ^ (2 : ℤ) ≠ 1
      ∧ ribbonTwist (1 / 2) = -1 :=
  ⟨electron_colour_singlet, electron_deconfined_iff_integer_charge,
    electron_su5_charge_is_winding, quark_confined, electron_fermion_center⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronDeconfinementCenterVortex

end
