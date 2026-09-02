/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBranchConfigurationAnalogy

/-!
# The many-body band-structure mechanism: `s–d` scattering makes gold the worst conductor

`SciamaAdSCPTBranchConfigurationAnalogy` established the boundary of the single-parameter relativistic-Fermi
model: the bare fine-structure coupling `α²` predicts the single-atom contraction correctly
(`contraction_gold_most`) but gives the *wrong* transport ordering (`bare_relativistic_coupling_gold_first`
is gold-*first*, while the measured DC conductivity is `Ag > Cu > Au`, gold-*worst*).  The flip is a **collective
band-structure effect**, not a single-atom one.  This module supplies that mechanism and *derives* the real
ordering from it.

**The chain (Mott `s–d` scattering + Fermi golden rule + Drude/Sommerfeld).**

* **Drude/Sommerfeld** (Cazaux, *Understanding Solid State Physics*, Springer 2016): the DC conductivity of a
  metal is `σ = n e² τ / m*`, set by the carrier relaxation time `τ`.
* **Fermi golden rule** (Ringhofer–Nedjalkov–Kosina–Selberherr, *SIAM J. Appl. Math.* **64** (2004) 1933,
  Eq. 1.1: the collision kernel `S_FGR(p,p') = A^∓ δ(ε(p) − ε(p') ∓ ℏω)`): the scattering rate *out* of a
  carrier state is `1/τ = ∫ dp' S_FGR ∝ g(E_F)` — the energy `δ`-function, integrated over final states, yields
  the **density of final states at the Fermi level**.
* **Mott `s–d` scattering** (N. F. Mott, *Proc. R. Soc.* **A153** (1936) 699): in a noble/transition metal the
  light `s` carriers scatter dominantly into the heavy `d`-band, so `1/τ ≈ (2π/ℏ)|M_{sd}|² g_d(E_F)` and hence
  `σ ∝ 1 / g_d(E_F)` — the resistivity is governed by the `d`-band density of states at the Fermi level.

**The relativistic input.**  The *same* relativity that contracts gold's `6s` (`contractionRatioSq`,
`contraction_gold_most`) *raises* (destabilizes) its `5d` band — the contracted `6s`/`6p` screen the nucleus, so
the `d` electrons see less charge, expand, and rise toward `E_F`.  Gold's relativistically-raised `5d` therefore
has the **largest** `g_d(E_F)`; silver's deep `4d` the smallest (`dBandDOS`, ordered `Au > Cu > Ag`, from
photoemission `d`-band positions).  Through the chain above this makes gold the worst conductor.

* `dBandDOS_gold_most` — `g_d(E_F)`: `Au > Cu > Ag` (the band-structure input, gold's raised `5d` largest).
* `bandConductivity_antitone` — `σ ∝ 1/g_d(E_F)` is antitone in the `d`-band DOS.
* `bandConductivity_reference_order` — hence `σ`: **`Ag > Cu > Au`**, the measured DC ordering, **derived** from
  the band structure (not the fitted `κ` of the relativistic-Fermi model).
* `bandStructure_resolves_transport` — bundles it: the raised-`5d` DOS ordering gives the real `Ag > Cu > Au`,
  whereas the same bare `α²` gives gold-first — the collective mechanism that resolves the single-atom shortfall.

Honest scope: the `g_d(E_F)` ordering `Au > Cu > Ag` is the band-structure *input* (from the relativistic `5d`
raising / photoemission `d`-band positions); the DOS values are illustrative, chosen only to carry that
ordering.  The golden-rule rate `∝ g_d(E_F)` and the Drude `σ ∝ 1/g_d` are the derived links.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNobleMetalBandStructure

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermiOrderingBranches
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBranchConfigurationAnalogy

/-- The `d`-band density of states at the Fermi level `g_d(E_F)` — the band-structure input.  Ordered
`Au > Cu > Ag`: gold's relativistically-raised `5d` sits closest to `E_F` (largest `d`-DOS), silver's deep `4d`
furthest (smallest).  Illustrative values carrying that ordering. -/
def dBandDOS : NobleMetal → ℝ
  | .gold => 5
  | .copper => 3
  | .silver => 1

/-- **[The `d`-band DOS is positive]** for every noble metal. -/
theorem dBandDOS_pos (X : NobleMetal) : 0 < dBandDOS X := by
  cases X <;> norm_num [dBandDOS]

/-- **[Gold has the largest `d`-band DOS at `E_F`] `g_d`: `Au > Cu > Ag`.**  Gold's relativistically-raised `5d`
band lies closest to `E_F` — the same relativity (`contraction_gold_most`) that contracts the `6s` raises the
`5d`. -/
theorem dBandDOS_gold_most : dBandDOS .gold > dBandDOS .copper ∧ dBandDOS .copper > dBandDOS .silver := by
  refine ⟨?_, ?_⟩ <;> norm_num [dBandDOS]

/-- The Fermi-golden-rule `s–d` scattering rate `1/τ_{sd} = (2π/ℏ)|M|² g_d(E_F) ∝ g_d(E_F)` (Ringhofer et al.,
Eq. 1.1; Mott `s–d` model).  `prefactor` is the golden-rule matrix-element factor `(2π/ℏ)|M|²`. -/
def sdScatteringRate (prefactor : ℝ) (X : NobleMetal) : ℝ := prefactor * dBandDOS X

/-- The Drude/Sommerfeld conductivity with `s–d` scattering dominant: `σ = n e² τ / m* ∝ 1/(1/τ_{sd}) ∝
1/g_d(E_F)` (Cazaux; `carrier = n e² / m*`). -/
def bandConductivity (carrier prefactor : ℝ) (X : NobleMetal) : ℝ := carrier / sdScatteringRate prefactor X

/-- **[Conductivity is antitone in the `d`-band DOS] `σ ∝ 1/g_d(E_F)`.**  More `d`-states at `E_F` ⟹ more `s–d`
scattering ⟹ shorter `τ` ⟹ lower `σ`. -/
theorem bandConductivity_antitone {carrier prefactor : ℝ} (hc : 0 < carrier) (hp : 0 < prefactor)
    {X Y : NobleMetal} (h : dBandDOS X < dBandDOS Y) :
    bandConductivity carrier prefactor Y < bandConductivity carrier prefactor X := by
  unfold bandConductivity sdScatteringRate
  rw [div_eq_mul_one_div carrier (prefactor * dBandDOS Y),
      div_eq_mul_one_div carrier (prefactor * dBandDOS X)]
  exact mul_lt_mul_of_pos_left
    (one_div_lt_one_div_of_lt (mul_pos hp (dBandDOS_pos X)) (mul_lt_mul_of_pos_left h hp)) hc

/-- **[The real DC ordering, derived from the band structure] `σ`: `Ag > Cu > Au`.**  Gold's largest `g_d(E_F)`
gives the most `s–d` scattering, the shortest relaxation time, and the lowest conductivity — the measured
`Ag > Cu > Au`, obtained from the band structure rather than the fitted `κ` of the relativistic-Fermi model. -/
theorem bandConductivity_reference_order {carrier prefactor : ℝ} (hc : 0 < carrier) (hp : 0 < prefactor) :
    ReferenceOrder (bandConductivity carrier prefactor) :=
  ⟨bandConductivity_antitone hc hp (show dBandDOS .silver < dBandDOS .copper by norm_num [dBandDOS]),
   bandConductivity_antitone hc hp (show dBandDOS .copper < dBandDOS .gold by norm_num [dBandDOS])⟩

/-- **[The collective mechanism resolves the single-atom shortfall].**  From the relativistically-raised `5d`
DOS (`g_d`: `Au > Cu > Ag`), the `s–d`/golden-rule/Drude chain gives the real `Ag > Cu > Au`; yet the *same* bare
`α²` gives gold-*first* (`bare_relativistic_coupling_gold_first`).  The flip is the collective band-structure
effect — `s–d` scattering into gold's raised `5d` — that the single-parameter relativistic-Fermi model could
only absorb into a fitted coupling. -/
theorem bandStructure_resolves_transport {carrier prefactor : ℝ} (hc : 0 < carrier) (hp : 0 < prefactor) :
    (dBandDOS .gold > dBandDOS .copper ∧ dBandDOS .copper > dBandDOS .silver)
      ∧ ReferenceOrder (bandConductivity carrier prefactor)
      ∧ GoldFirstOrder (relConductivity (fineStructure ^ 2)) :=
  ⟨dBandDOS_gold_most, bandConductivity_reference_order hc hp, bare_relativistic_coupling_gold_first⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTNobleMetalBandStructure

end
