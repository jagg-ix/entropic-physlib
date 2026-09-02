/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsZoo
public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
public import Physlib.Particles.StandardModel.HiggsBoson.Potential
public import Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification
public import Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
public import Mathlib.Tactic
meta import Zil

/-!
# The Higgs boson: the neutral self-conjugate massive scalar

The Higgs is the Standard Model's lone fundamental **scalar** (spin `0`). This file assembles its
classification: a spin-`0` boson (exchange phase `θ(0)=+1`, distinct from the spin-½ fermions), electrically
and otherwise **neutral** (`(Q,B,L)=(0,0,0)`), and therefore its **own antiparticle** (`C(H)=H`); it is
massive (unlike the massless `γ`, gluon).

* **§A — spin-0 scalar boson.** `higgs_scalar_spinZero` (`θ(0)=+1`, from `Fermion.SpinStatisticsZoo`),
  `higgs_not_fermion` (`θ(0) ≠ θ(½)`).
* **§B — neutral and self-conjugate.** `higgs` `(Q,B,L)=(0,0,0)`; `higgs_selfConjugate` (`C(H)=H`, the Higgs
  is its own antiparticle — a self-conjugate neutral, like the photon/`Z`).
* **§C — Higgs potential and mass.** The canonical Standard Model potential is exposed through
  `standardModelPotential_complete_square`; the radial stationarity equation gives
  `higgsMassSq = 2 * lambda * v^2`.
* **§D — couplings.** The W/Z couplings are the derivatives of the existing VEV mass carriers with respect
  to the VEV, while the fermion coupling is the existing Yukawa identity `m_f/v = y_f/sqrt 2`.
* **§E — widths and branching ratios.** Partial widths are kept symbolic, but Lean checks the normalization
  law `sum BR_i = 1` whenever the total width is nonzero.
* **§F — the main result** `higgs_boson`.
* **§G — Deser/DJT separation.** The Higgs VEV and the Chern-Simons topological mass are checked as
  distinct mechanisms: the VEV is fixed by Higgs-potential stationarity assumptions, while the DJT mass is
  fixed by gauge coupling/level data and can be positive even when Higgs-VEV gauge masses vanish.

**Honest layering.** Proven: spin-0 gives the bosonic exchange phase (`≠` the fermionic one), and a particle
with all additive quantum numbers zero is self-conjugate (`AntiparticleConjugation.selfConjugate_iff_neutral`).
The dynamical layer proves the tree-level algebraic consequences of the Standard Model potential and existing
electroweak/Yukawa definitions. It does not import experimental constants such as `125 GeV`, `246 GeV`, or
measured branching fractions.

## References

* The Higgs scalar (spin 0, neutral, self-conjugate, massive). `Physlib` (`Fermion.SpinStatisticsZoo`,
  `AntiparticleConjugation`).


-/

set_option autoImplicit false

open scoped BigOperators

open Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsZoo
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification
open Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TopologicalMassDJT
open Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson


/-- **[The Higgs is a scalar boson]** `θ(0) = +1` — spin `0`, the symmetric exchange phase
(`Fermion.SpinStatisticsZoo.higgs_scalar_boson`). -/
lemma higgs_scalar_spinZero : ribbonTwist ((0 : ℤ) : ℝ) = 1 := higgs_scalar_boson

/-- **[The Higgs is not a fermion]** `θ(0) = +1 ≠ −1 = θ(½)` — the scalar boson and the spin-½ matter fields
have opposite exchange phases. -/
lemma higgs_not_fermion : ribbonTwist ((0 : ℤ) : ℝ) ≠ ribbonTwist (1 / 2) := by
  rw [higgs_scalar_spinZero, ribbonTwist_fermion]; norm_num


/-- **The Higgs** at the additive-quantum-number level: `(Q,B,L) = (0,0,0)` — electrically neutral, no
baryon or lepton number. -/
def higgs : Particles.BaryonLeptonNumberConservation.QuantumNumbers := ⟨0, 0, 0⟩

/-- **[The Higgs is its own antiparticle]** `C(H) = H` — being neutral in every additive quantum number, the
Higgs is self-conjugate (`selfConjugate_iff_neutral`), like the photon and `Z⁰`. -/
lemma higgs_selfConjugate : conjugate higgs = higgs :=
  (selfConjugate_iff_neutral higgs).mpr ⟨rfl, rfl, rfl⟩


/-- The Standard Model Higgs potential carrier already present in the repo:
`V = -mu^2 |phi|^2 + lambda |phi|^4`. -/
def standardModelPotential (mu2 lambda : ℝ) : StandardModel.HiggsField.Potential where
  μ2 := mu2
  𝓵 := lambda

/-- The Standard Model potential completes the square around
`|phi|^2 = mu^2/(2 lambda)`, reusing the canonical `StandardModel.HiggsField.Potential` theorem. -/
lemma standardModelPotential_complete_square
    (mu2 lambda : ℝ) (hlambda : lambda ≠ 0)
    (phi : StandardModel.HiggsField) (x : SpaceTime) :
    (standardModelPotential mu2 lambda).toFun phi x =
      lambda * (StandardModel.HiggsField.normSq phi x - mu2 / (2 * lambda)) ^ 2
        - mu2 ^ 2 / (4 * lambda) := by
  simpa [standardModelPotential] using
    (StandardModel.HiggsField.Potential.complete_square
      (P := standardModelPotential mu2 lambda) hlambda phi x)

/-- Radial Higgs potential as a function of `r = |Phi|^2`:
`V(r) = -mu^2 r + lambda r^2`. -/
def higgsRadialPotential (mu2 lambda r : ℝ) : ℝ :=
  -mu2 * r + lambda * r ^ 2

/-- The radial minimum location in the completed-square coordinate:
`r_min = mu^2/(2 lambda)`, for `lambda ≠ 0`.  For the usual convention
`Phi = (0,(v+h)/sqrt 2)`, this corresponds to `v^2 = mu^2/lambda`. -/
def higgsRadialNormSqAtMinimum (mu2 lambda : ℝ) : ℝ :=
  mu2 / (2 * lambda)

/-- The radial Higgs potential completes the square around
`r = mu^2/(2 lambda)`. -/
lemma higgsRadialPotential_complete_square
    (mu2 lambda r : ℝ) (hlambda : lambda ≠ 0) :
    higgsRadialPotential mu2 lambda r =
      lambda * (r - higgsRadialNormSqAtMinimum mu2 lambda) ^ 2
        - mu2 ^ 2 / (4 * lambda) := by
  unfold higgsRadialPotential higgsRadialNormSqAtMinimum
  field_simp [hlambda]
  ring

/-- At the completed-square radial minimum, the potential value is
`-mu^4/(4 lambda)`. -/
lemma higgsRadialPotential_at_normSqMinimum
    (mu2 lambda : ℝ) (hlambda : lambda ≠ 0) :
    higgsRadialPotential mu2 lambda (higgsRadialNormSqAtMinimum mu2 lambda) =
      -mu2 ^ 2 / (4 * lambda) := by
  unfold higgsRadialPotential higgsRadialNormSqAtMinimum
  field_simp [hlambda]
  ring

/-- The conventional VEV-square derived from the potential parameters:
`v^2 = mu^2/lambda`, using `|Phi|^2 = v^2/2`. -/
def higgsVEVSqFromPotential (mu2 lambda : ℝ) : ℝ :=
  mu2 / lambda

/-- The conventional VEV-square is twice the radial `|Phi|^2` minimum. -/
lemma higgsVEVSqFromPotential_eq_two_normSqMinimum
    (mu2 lambda : ℝ) (hlambda : lambda ≠ 0) :
    higgsVEVSqFromPotential mu2 lambda =
      2 * higgsRadialNormSqAtMinimum mu2 lambda := by
  unfold higgsVEVSqFromPotential higgsRadialNormSqAtMinimum
  field_simp [hlambda]

/-- The radial Higgs stationarity equation at the VEV: `lambda v^2 = mu^2`. -/
def HiggsVEVStationary (mu2 lambda v : ℝ) : Prop :=
  lambda * v ^ 2 = mu2

/-- If `v^2` is the potential-derived VEV-square, then the VEV stationarity
equation holds. -/
lemma higgsVEVStationary_of_sq_eq_higgsVEVSqFromPotential
    (mu2 lambda v : ℝ) (hlambda : lambda ≠ 0)
    (hv2 : v ^ 2 = higgsVEVSqFromPotential mu2 lambda) :
    HiggsVEVStationary mu2 lambda v := by
  unfold HiggsVEVStationary higgsVEVSqFromPotential at *
  rw [hv2]
  field_simp [hlambda]

/-- The stationarity equation identifies the completed-square norm minimum
with `v^2/2`, matching the Standard Model convention
`Phi = (0,(v+h)/sqrt 2)`. -/
lemma higgsRadialNormSqAtMinimum_eq_vevSq_div_two_of_stationary
    (mu2 lambda v : ℝ) (hlambda : lambda ≠ 0)
    (hstat : HiggsVEVStationary mu2 lambda v) :
    higgsRadialNormSqAtMinimum mu2 lambda = v ^ 2 / 2 := by
  unfold higgsRadialNormSqAtMinimum HiggsVEVStationary at *
  rw [← hstat]
  field_simp [hlambda]

/-- The tree-level Higgs mass-square from the potential parameter:
`m_h^2 = 2 mu^2`. -/
def higgsMassSqFromPotential (mu2 : ℝ) : ℝ :=
  2 * mu2

/-- The same tree-level Higgs mass-square written at the VEV:
`m_h^2 = 2 lambda v^2`. -/
def higgsMassSqFromVEV (lambda v : ℝ) : ℝ :=
  2 * lambda * v ^ 2

/-- The stationarity equation identifies the two Higgs mass-square forms:
`mu^2 = lambda v^2`, hence `m_h^2 = 2 lambda v^2`. -/
lemma higgsMassSqFromPotential_eq_higgsMassSqFromVEV
    (mu2 lambda v : ℝ) (hstat : HiggsVEVStationary mu2 lambda v) :
    higgsMassSqFromPotential mu2 = higgsMassSqFromVEV lambda v := by
  unfold HiggsVEVStationary higgsMassSqFromPotential higgsMassSqFromVEV at *
  rw [← hstat]
  ring

/-- Solving the tree-level mass equation for the quartic coupling:
`lambda = m_h^2/(2 v^2)` when `v != 0`. -/
lemma higgsQuartic_eq_massSq_div_two_vevSq
    (mh2 lambda v : ℝ) (hv : v ≠ 0)
    (hmass : mh2 = higgsMassSqFromVEV lambda v) :
    lambda = mh2 / (2 * v ^ 2) := by
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  unfold higgsMassSqFromVEV at hmass
  rw [hmass]
  field_simp [hv2]


/-- The tree-level `hWW` coupling written as `2 m_W^2 / v`. -/
noncomputable def higgsWWCouplingFromMass (mW v : ℝ) : ℝ :=
  2 * mW ^ 2 / v

/-- The tree-level `hZZ` coupling written as `2 m_Z^2 / v`. -/
noncomputable def higgsZZCouplingFromMass (mZ v : ℝ) : ℝ :=
  2 * mZ ^ 2 / v

/-- The `hWW` coupling induced by the VEV mass formula:
`2 (g v/2)^2 / v = g^2 v / 2`. -/
lemma higgsWWCouplingFromMass_wMassFromVEV
    (g v : ℝ) (hv : v ≠ 0) :
    higgsWWCouplingFromMass (wMassFromVEV g v) v = g ^ 2 * v / 2 := by
  unfold higgsWWCouplingFromMass wMassFromVEV
  field_simp [hv]

/-- The `hZZ` coupling induced by the VEV mass formula:
`2 (sqrt(g^2+g'^2) v/2)^2 / v = (g^2+g'^2) v/2`. -/
lemma higgsZZCouplingFromMass_zMassFromVEV
    (g g' v : ℝ) (hv : v ≠ 0) :
    higgsZZCouplingFromMass (zMassFromVEV g g' v) v =
      (g ^ 2 + g' ^ 2) * v / 2 := by
  have hnonneg : 0 ≤ g ^ 2 + g' ^ 2 := by
    nlinarith [sq_nonneg g, sq_nonneg g']
  unfold higgsZZCouplingFromMass zMassFromVEV
  have hs :
      (Real.sqrt (g ^ 2 + g' ^ 2) * v / 2) ^ 2 =
        (g ^ 2 + g' ^ 2) * v ^ 2 / 4 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hnonneg]
    ring
  rw [hs]
  field_simp [hv]
  ring

/-- The Higgs-fermion coupling is the existing Standard Model Yukawa identity:
`g_hff = m_f/v = y_f/sqrt 2`. -/
lemma higgsFermionCoupling_from_yukawaMass
    (y v : ℝ) (hv : v ≠ 0) :
    higgsFermionCouplingFromMass
        (Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass y v) v =
      higgsFermionCouplingFromYukawa y :=
  higgsFermionCouplingFromMass_yukawaMass_eq y v hv


/-- Symbolic Higgs partial-width assignment over a finite mode type. -/
abbrev HiggsPartialWidths (Mode : Type*) := Mode → ℝ

/-- Total Higgs width as the finite sum of partial widths. -/
def higgsTotalWidth {Mode : Type*} [Fintype Mode] (Gamma : HiggsPartialWidths Mode) : ℝ :=
  ∑ mode : Mode, Gamma mode

/-- Branching ratio `BR_i = Gamma_i / Gamma_total`. -/
def higgsBranchingRatio {Mode : Type*} [Fintype Mode]
    (Gamma : HiggsPartialWidths Mode) (mode : Mode) : ℝ :=
  Gamma mode / higgsTotalWidth Gamma

/-- If every partial width is nonnegative, the total Higgs width is nonnegative. -/
lemma higgsTotalWidth_nonneg {Mode : Type*} [Fintype Mode]
    (Gamma : HiggsPartialWidths Mode) (hGamma : ∀ mode, 0 ≤ Gamma mode) :
    0 ≤ higgsTotalWidth Gamma := by
  unfold higgsTotalWidth
  exact Finset.sum_nonneg (fun mode _ => hGamma mode)

/-- Higgs branching ratios normalize to one when the total width is nonzero. -/
lemma higgsBranchingRatio_sum_eq_one {Mode : Type*} [Fintype Mode]
    (Gamma : HiggsPartialWidths Mode) (hTot : higgsTotalWidth Gamma ≠ 0) :
    ∑ mode : Mode, higgsBranchingRatio Gamma mode = 1 := by
  unfold higgsBranchingRatio higgsTotalWidth
  rw [← Finset.sum_div]
  exact div_self hTot

/-- A partial width is zero at zero coupling for any decay channel whose width is a quadratic coupling
factor times a kinematic factor. -/
def quadraticCouplingPartialWidth (coupling kinematic : ℝ) : ℝ :=
  coupling ^ 2 * kinematic

lemma quadraticCouplingPartialWidth_nonneg
    (coupling kinematic : ℝ) (hkin : 0 ≤ kinematic) :
    0 ≤ quadraticCouplingPartialWidth coupling kinematic := by
  unfold quadraticCouplingPartialWidth
  positivity

@[simp] lemma quadraticCouplingPartialWidth_zero_coupling (kinematic : ℝ) :
    quadraticCouplingPartialWidth 0 kinematic = 0 := by
  simp [quadraticCouplingPartialWidth]


/-- **[The Higgs boson]** the neutral self-conjugate scalar: spin-`0` bosonic exchange phase `θ(0)=+1`,
distinct from the fermions (`θ(0) ≠ θ(½)`), and its own antiparticle (`C(H)=H`). -/
lemma higgs_boson :
    ribbonTwist ((0 : ℤ) : ℝ) = 1
      ∧ ribbonTwist ((0 : ℤ) : ℝ) ≠ ribbonTwist (1 / 2)
      ∧ conjugate higgs = higgs :=
  ⟨higgs_scalar_spinZero, higgs_not_fermion, higgs_selfConjugate⟩

/-- Checked Higgs dynamical layer: the Standard Model potential supplies the VEV/mass-square relation,
the W/Z mass carriers supply the Higgs-gauge couplings, the Yukawa bridge supplies `g_hff`, and finite
partial widths give normalized branching ratios. -/
lemma higgsBoson_dynamicalLayer_checked
    (mu2 lambda v g g' y : ℝ) (hv : v ≠ 0)
    (hstat : HiggsVEVStationary mu2 lambda v) :
    higgsMassSqFromPotential mu2 = higgsMassSqFromVEV lambda v
      ∧ higgsWWCouplingFromMass (wMassFromVEV g v) v = g ^ 2 * v / 2
      ∧ higgsZZCouplingFromMass (zMassFromVEV g g' v) v =
          (g ^ 2 + g' ^ 2) * v / 2
      ∧ higgsFermionCouplingFromMass
          (Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass y v) v =
          higgsFermionCouplingFromYukawa y
      ∧ (∀ {Mode : Type*} [Fintype Mode] (Gamma : HiggsPartialWidths Mode),
          higgsTotalWidth Gamma ≠ 0 →
          ∑ mode : Mode, higgsBranchingRatio Gamma mode = 1) := by
  exact ⟨higgsMassSqFromPotential_eq_higgsMassSqFromVEV mu2 lambda v hstat,
    higgsWWCouplingFromMass_wMassFromVEV g v hv,
    higgsZZCouplingFromMass_zMassFromVEV g g' v hv,
    higgsFermionCoupling_from_yukawaMass y v hv,
    fun Gamma hTot => higgsBranchingRatio_sum_eq_one Gamma hTot⟩


/-- A DJT topological mass may be displayed with an unused Higgs-VEV parameter.
The definition deliberately ignores `v`: Deser--Jackiw--Templeton mass is fixed
by Chern--Simons gauge data, not by the Standard Model Higgs vacuum. -/
noncomputable def djtTopologicalMassWithUnusedHiggsVEV (dj : DJTData) (_v : ℝ) : ℝ :=
  topologicalMass dj

/-- The DJT topological mass is independent of the Higgs VEV parameter. -/
lemma djtTopologicalMass_independent_of_higgsVEV
    (dj : DJTData) (v₁ v₂ : ℝ) :
    djtTopologicalMassWithUnusedHiggsVEV dj v₁ =
      djtTopologicalMassWithUnusedHiggsVEV dj v₂ := rfl

/-- The DJT topological mass formula depends only on gauge coupling and
Chern--Simons level: `m_CS = e^2 |k|/(2π)`. -/
lemma djtTopologicalMass_eq_gaugeLevelData (e : ℝ) (k : ℤ) :
    topologicalMass ({ e := e, level := k } : DJTData) =
      e ^ 2 * |(k : ℝ)| / (2 * Real.pi) := rfl

/-- Unit coupling and unit Chern--Simons level give a strictly positive DJT
topological mass. -/
lemma djtTopologicalMass_unitLevel_pos :
    0 < topologicalMass ({ e := 1, level := 1 } : DJTData) := by
  unfold topologicalMass
  positivity

/-- At zero Higgs VEV, the tree-level electroweak W/Z masses vanish. -/
lemma higgsGaugeMasses_vanish_at_zero_vev (g g' : ℝ) :
    wMassFromVEV g 0 = 0 ∧ zMassFromVEV g g' 0 = 0 := by
  simp [wMassFromVEV, zMassFromVEV]

/-- Deser/DJT supplies a non-Higgs mass mechanism: with zero Higgs VEV the
electroweak VEV masses vanish, but the unit-level Chern--Simons topological
mass is still positive. -/
lemma deserTopologicalMass_positive_with_zero_higgsVEV_gaugeMasses :
    ∃ dj : DJTData,
      0 < topologicalMass dj
        ∧ wMassFromVEV 1 0 = 0
        ∧ zMassFromVEV 1 0 0 = 0 := by
  refine ⟨{ e := 1, level := 1 }, djtTopologicalMass_unitLevel_pos, ?_, ?_⟩
  · exact (higgsGaugeMasses_vanish_at_zero_vev 1 0).1
  · exact (higgsGaugeMasses_vanish_at_zero_vev 1 0).2

/-- The same DJT topological mass is compatible with distinct Higgs-VEV W
masses. Hence DJT data do not determine the Higgs VEV or the electroweak
VEV masses. -/
lemma same_djtTopologicalMass_allows_distinct_higgsVEVMasses :
    ∃ dj : DJTData,
      djtTopologicalMassWithUnusedHiggsVEV dj 0 =
        djtTopologicalMassWithUnusedHiggsVEV dj 2
        ∧ wMassFromVEV 1 0 ≠ wMassFromVEV 1 2 := by
  refine ⟨{ e := 1, level := 1 }, rfl, ?_⟩
  norm_num [wMassFromVEV]

/-- Checked separation of mechanisms.  From the Higgs potential assumptions,
Lean derives the VEV stationarity/mass identities and the W/Z/Yukawa coupling
relations; from Deser--Jackiw--Templeton data, Lean derives a separate
Chern--Simons topological mass independent of the VEV. -/
lemma higgsBoson_deserMechanismSeparation_checked
    (mu2 lambda v g g' y : ℝ) (dj : DJTData)
    (hlambda : lambda ≠ 0) (hv : v ≠ 0)
    (hstat : HiggsVEVStationary mu2 lambda v) :
    higgsRadialNormSqAtMinimum mu2 lambda = v ^ 2 / 2
      ∧ higgsMassSqFromPotential mu2 = higgsMassSqFromVEV lambda v
      ∧ higgsWWCouplingFromMass (wMassFromVEV g v) v = g ^ 2 * v / 2
      ∧ higgsZZCouplingFromMass (zMassFromVEV g g' v) v =
          (g ^ 2 + g' ^ 2) * v / 2
      ∧ higgsFermionCouplingFromMass
          (Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass y v) v =
          higgsFermionCouplingFromYukawa y
      ∧ (∀ v₁ v₂ : ℝ,
          djtTopologicalMassWithUnusedHiggsVEV dj v₁ =
            djtTopologicalMassWithUnusedHiggsVEV dj v₂) := by
  exact ⟨higgsRadialNormSqAtMinimum_eq_vevSq_div_two_of_stationary
      mu2 lambda v hlambda hstat,
    higgsMassSqFromPotential_eq_higgsMassSqFromVEV mu2 lambda v hstat,
    higgsWWCouplingFromMass_wMassFromVEV g v hv,
    higgsZZCouplingFromMass_zMassFromVEV g g' v hv,
    higgsFermionCoupling_from_yukawaMass y v hv,
    fun v₁ v₂ => djtTopologicalMass_independent_of_higgsVEV dj v₁ v₂⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsVEVSqFromPotential_eq_two_normSqMinimum where
  formalizes @ "claim:the-higgs-vacuum-expectation-value-squared-is-fixed-by-the-potential-minimum-v-squared-equals-mu-squared-over-lambda",
  supported_by @ "paper:pdg-2026-review-higgs-boson"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsMassSqFromPotential_eq_higgsMassSqFromVEV where
  formalizes @ "claim:the-higgs-mass-squared-from-the-potential-curvature-equals-two-lambda-v-squared-from-the-vacuum-expectation-value",
  requires @ "claim:the-higgs-vacuum-expectation-value-squared-is-fixed-by-the-potential-minimum-v-squared-equals-mu-squared-over-lambda",
  supported_by @ "paper:pdg-2026-review-higgs-boson"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsQuartic_eq_massSq_div_two_vevSq where
  formalizes @ "claim:the-higgs-quartic-coupling-equals-the-mass-squared-over-twice-the-vacuum-expectation-value-squared",
  requires @ "claim:the-higgs-mass-squared-from-the-potential-curvature-equals-two-lambda-v-squared-from-the-vacuum-expectation-value"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgs_selfConjugate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation.selfConjugate_iff_neutral",
  formalizes @ "claim:the-higgs-boson-is-its-own-antiparticle-a-neutral-self-conjugate-scalar"

zil_file_contract physlib.higgsBoson where
  promises "The Higgs sector of the Standard Model: the Mexican-hat potential completes the square about its minimum, fixing the vacuum expectation value squared to mu-squared over lambda; the Higgs mass squared from the potential curvature equals two lambda v squared, so the quartic coupling equals the mass squared over twice the VEV squared; the WW and ZZ and fermion couplings follow from the gauge and Yukawa masses; the Higgs is a neutral self-conjugate spin-zero boson; and partial widths are non-negative with branching ratios summing to one."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.standardModelPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsVEVSqFromPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsMassSqFromVEV"]
  forbids_substitutes ["a derivation of the numerical Higgs mass or VEV, which are experimental inputs",
    "a proof of vacuum stability or the hierarchy problem, only the tree-level potential relations are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsVEVSqFromPotential_eq_two_normSqMinimum,
    Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsMassSqFromPotential_eq_higgsMassSqFromVEV,
    Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsQuartic_eq_massSq_div_two_vevSq,
    Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgs_selfConjugate,
    Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsBranchingRatio_sum_eq_one]

/- ZIL-END -/

end
