/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
public import Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration
public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
public import Physlib.QuantumMechanics.ComplexAction.Fermion.AnnihilationTwoPhotons
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

/-!
# The electron hub: Zitterbewegung ⟷ Compton clock ⟷ spin-½ double cover

A single link surface tying together the electron formalizations into one object, so downstream files
import *this* to reach every facet of the electron at once:

* **Dirac electron — Zitterbewegung (operator).** `Dirac.FourSpinorDiracHamiltonian` §F: the velocity operator
  `α₁` is luminal (`α₁²=1`), not conserved (`[H,α₁]=2η₁`), and the trembling operator `η₁=Hα₁−p₁`
  oscillates `[H,η₁]=2Hη₁` at the rest gap `2H = 2mβ`, `H(0)²=m²·1`.
* **Compton clock (scalar).** `ComptonClock.FrequencyTrinity`: `ω_C = mc²/ħ`, `ω_Z = 2√(p²c²+m²c⁴)/ħ`, with
  `ω_Z = 2ω_C` at rest.
* **Spin-½ / double cover.** `Hopf.ChargeConjugationRibbonTwist.ribbonTwist ½ = −1` (the fermion exchange
  sign) and `Hopf.QuaternionIsoclinicHopfFibration.hopf_neg` (`hopf(−q)=hopf q`, the `SU(2)→SO(3)` `4π`-return).

The genuine link they share is the **factor of two**: the electron's Zitterbewegung trembles at *twice*
its Compton clock (`restFrame_zitter_operator_frequency`: the rest oscillation operator `2H` squares to
`(2ω_C)²·1`), and that doubling is the `E₊−E₋` interference of the two energy sheets — the same two sheets
of the spinor double cover that make the electron spin-½ (`ribbonTwist ½=−1`) and need a `4π` turn to
return (`hopf(−q)=hopf q`). The hub theorem `electron_zitterbewegung_spin_half` states all three together.

The electron's *other* facets are imported directly here and re-exported, so the whole electron is one
import: its **charge** as a winding (`Winding.QuarkChargeWinding.electron_charge`, `Q=−1` at `n=−3`), its
**topology** as the trefoil knot with a Chern-Simons-Witten Jones invariant
(`ChernSimons.TrefoilFermionChernSimonsInvariant`, chiral so `electron ≠ positron`), its **annihilation** as an
unknotting (`Fermion.AnnihilationTwoPhotons`, knot · anti-knot `= 1`), and its **magnetic moment** as a
rapidity/entanglement defect (`MuonAnomaly.RapidityFromSchmidt.anomaly_rapidity`, `a = K²−1`). The
main result `electron_complete` gathers all seven facets in one theorem. The Zitterbewegung is the dynamical
face of the same spin-½ object.

* **§C — charge & topology** (`electron_charge_neg_one`, `electron_trefoil_chiral`,
  `electron_positron_unknots`).
* **§D — magnetic moment / g−2** (`electron_anomaly_eq_schmidt_defect`).
* **§E — CPT & charge conjugation** (`electron_dirac_cpt_invariant` the Greaves-Thomas dynamical CPT
  theorem `A·D(−p)·A⁻¹=D(p)`, `electron_charge_conjugation` `Q(−n)=−Q(n)`, `electron_antiparticle_annihilates`
  `e⁻+e⁺=0`).
* **§F — the whole electron** (`electron_complete`, now including the three CPT facets).

**Honest layering.** Each conjunct of the hub theorem is a theorem proved in its own file; the hub *links*
them (the bundling is the content — that the Zitterbewegung doubling, the spin-½ exchange sign, and the
double cover are facets of one electron). The `E₊−E₋ = 2ω_C ⟺ spin-½` reading is the standard physical
interpretation; the algebra (`2H` squares to `(2ω_C)²`, `ribbonTwist ½=−1`, `hopf(−q)=hopf q`) is exact.

## References

* Schrödinger's Zitterbewegung; the Compton/Zitterbewegung/de Broglie trinity; the spinor double cover.
  `Physlib` (`Dirac.FourSpinorDiracHamiltonian`, `ComptonClock.FrequencyTrinity`, `Hopf.ChargeConjugationRibbonTwist`,
  `Hopf.QuaternionIsoclinicHopfFibration`).


-/

set_option autoImplicit false

open Quaternion
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.Fermion.AnnihilationTwoPhotons
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.RapidityFromSchmidt
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ElectronZitterbewegung


/-- **[The Zitterbewegung operator trembles at twice the Compton clock]** the rest-frame oscillation
operator `2H = 2mβ` of `Dirac.FourSpinorDiracHamiltonian` squares to `(2 ω_C)²·1`, where `ω_C = mc²/ħ` is the
`ComptonClock.FrequencyTrinity` Compton frequency (natural units `c=ħ=1`): the operator dynamics realize the
scalar Zitterbewegung frequency `ω_Z = 2ω_C`. -/
lemma restFrame_zitter_operator_frequency (m : ℝ) :
    ((2 : ℂ) • diracHamiltonian4 0 0 0 m) * ((2 : ℂ) • diracHamiltonian4 0 0 0 m)
      = (((2 * comptonFrequency m 1 1) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [smul_mul_smul_comm, restFrame_zitter_gap, smul_smul]
  congr 1
  unfold comptonFrequency
  push_cast
  ring

/-- **[The scalar Zitterbewegung frequency is twice Compton]** `ω_Z = 2 ω_C` at rest (re-exposing
`ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton` through the hub). -/
lemma zitterbewegung_scalar_eq_two_compton (m : ℝ) (hm : 0 ≤ m) :
    zitterbewegungFrequency 0 m 1 1 = 2 * comptonFrequency m 1 1 :=
  zitterbewegung_rest_eq_two_compton m 1 1 hm


/-- **[The electron, assembled]** the Zitterbewegung trembles at twice the Compton clock
(`2H` squares to `(2ω_C)²·1`), the electron is spin-½ (`ribbonTwist ½ = −1`), and it carries the spinor
double cover (`hopf(−q) = hopf q`, the `4π` return). The factor of two in the Zitterbewegung *is* the
`E₊−E₋` two-sheet structure that makes the electron a spin-½ fermion — one object, three facets. -/
lemma electron_zitterbewegung_spin_half (m : ℝ) :
    ((2 : ℂ) • diracHamiltonian4 0 0 0 m) * ((2 : ℂ) • diracHamiltonian4 0 0 0 m)
        = (((2 * comptonFrequency m 1 1) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
      ∧ ribbonTwist (1 / 2) = -1
      ∧ ∀ q : ℍ[ℝ], hopf (-q) = hopf q :=
  ⟨restFrame_zitter_operator_frequency m, ribbonTwist_fermion, hopf_neg⟩


/-- **[Electron charge `−1`]** the electron is the integer-winding `n = −3` state, `Q = −1`
(`Winding.QuarkChargeWinding`). -/
lemma electron_charge_neg_one : windingCharge (-3) = -1 := Winding.QuarkChargeWinding.electron_charge

/-- **[Electron trefoil is chiral]** the Chern-Simons-Witten Jones invariant of the electron trefoil differs
from the positron mirror (`electronJones 2 ≠ positronJones 2`) — the topological particle/antiparticle
distinction (`ChernSimons.TrefoilFermionChernSimonsInvariant`). -/
lemma electron_trefoil_chiral : electronJones 2 ≠ positronJones 2 := trefoil_chiral_distinguishes

/-- **[Electron–positron annihilation unknots]** the electron knot composed with the positron anti-knot
collapses to the vacuum, `chargeState q · chargeState (−q) = 1` (`Fermion.AnnihilationTwoPhotons`). -/
lemma electron_positron_unknots (q : ℤ) : chargeState q * chargeState (-q) = 1 :=
  fermion_antifermion_unknots q


/-- **[Anomaly is the Schmidt defect `a = K²−1`]** at the operating-point rapidity the magnetic anomaly equals the
Schmidt-number defect `K²−1` — g−2 as a rapidity/entanglement defect (`MuonAnomaly.RapidityFromSchmidt`). -/
lemma electron_anomaly_eq_schmidt_defect (K : ℝ) (hK : 1 < K) :
    anomaly (rapidity K) = K ^ 2 - 1 := anomaly_rapidity K hK


/-- **[The Dirac dynamics is `CPT`-invariant]** `A·D(−p)·A⁻¹ = D(p)` with `A = (−i)γ⁵` — the Greaves-Thomas
dynamical `CPT` theorem: the electron's covariant Dirac operator is invariant under the combined
`CPT` inversion (`PTSymmetricQFT.CPTDiracDynamics`). -/
lemma electron_dirac_cpt_invariant (p : Fin 4 → ℝ) (m : ℝ) :
    ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  cpt_diracOp_invariant p m

/-- **[Charge conjugation `C` reverses charge]** `Q(−n) = −Q(n)` — the electron's charge conjugate (the
positron) carries the opposite charge (`Winding.QuarkChargeWinding.windingCharge_neg`). -/
lemma electron_charge_conjugation (n : ℤ) : windingCharge (-n) = - windingCharge n :=
  windingCharge_neg n

/-- **[The electron and its antiparticle annihilate]** `e⁻ + e⁺ = vacuum`: the electron and its `C`-conjugate
positron sum to zero additive quantum numbers (`AntiparticleConjugation`). -/
lemma electron_antiparticle_annihilates :
    Particles.BaryonLeptonNumberConservation.electron + positron = ⟨0, 0, 0⟩ :=
  electron_positron_annihilate


/-- **[The electron in one theorem]** every facet of the same spin-½ object: (i) the Zitterbewegung trembles
at twice the Compton clock; (ii) spin-½ exchange sign `ribbonTwist ½ = −1`; (iii) the `SU(2)→SO(3)` double
cover `hopf(−q)=hopf q` (`4π` return); (iv) charge `Q=−1` as winding `n=−3`; (v) the trefoil is chiral
(electron ≠ positron); (vi) annihilation unknots to the vacuum; (vii) the g−2 anomaly is the Schmidt defect
`K²−1`; (viii) **CPT** — charge conjugation reverses charge `Q(−n)=−Q(n)`; (ix) the electron and its
antiparticle positron annihilate `e⁻+e⁺=0`; (x) the **dynamical CPT theorem** `A·D(−p)·A⁻¹=D(p)`. Each
conjunct is proved in its own file; the hub links them into one electron. -/
lemma electron_complete (m : ℝ) (p : Fin 4 → ℝ) (q n : ℤ) (K : ℝ) (hK : 1 < K) :
    ((2 : ℂ) • diracHamiltonian4 0 0 0 m) * ((2 : ℂ) • diracHamiltonian4 0 0 0 m)
        = (((2 * comptonFrequency m 1 1) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
      ∧ ribbonTwist (1 / 2) = -1
      ∧ (∀ qq : ℍ[ℝ], hopf (-qq) = hopf qq)
      ∧ windingCharge (-3) = -1
      ∧ electronJones 2 ≠ positronJones 2
      ∧ chargeState q * chargeState (-q) = 1
      ∧ anomaly (rapidity K) = K ^ 2 - 1
      ∧ windingCharge (-n) = - windingCharge n
      ∧ Particles.BaryonLeptonNumberConservation.electron + positron = ⟨0, 0, 0⟩
      ∧ ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  ⟨restFrame_zitter_operator_frequency m, ribbonTwist_fermion, hopf_neg,
    Winding.QuarkChargeWinding.electron_charge, trefoil_chiral_distinguishes,
    fermion_antifermion_unknots q, anomaly_rapidity K hK,
    windingCharge_neg n, electron_positron_annihilate, cpt_diracOp_invariant p m⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ElectronZitterbewegung

end
