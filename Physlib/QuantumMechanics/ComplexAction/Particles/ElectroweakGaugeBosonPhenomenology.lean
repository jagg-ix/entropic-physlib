/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ElectroweakYangMillsThermodynamics
public import Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo
public import Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
public import Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor
public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
public import Mathlib.Tactic
meta import Zil

/-!
# Electroweak gauge-boson masses, couplings, widths, and decay modes

This file links the already-formalized gauge-boson sector to the canonical
electroweak coupling API:

* `W/Z` masses are the existing Higgs-VEV formulas, with the W-mass file's
  local Weinberg angle identified with `WeinbergAngle.cosWeinberg` and
  `WeinbergAngle.sinWeinberg`;
* the photon mass is exactly zero, via the existing unbroken gauge-boson mass
  layer;
* `e = g sin theta_W = g' cos theta_W`, `alpha = e^2/(4 pi)`, and
  `sin^2 theta_W = g'^2/(g^2+g'^2)` reuse `WeinbergAngle` and
  `ElectroweakYangMillsThermodynamics`;
* gluon self-interaction is the concrete nonzero `su(3)` commutator
  `[lambda_1,lambda_2] = 2 i lambda_3`, plus the existing Lie/Jacobi
  structure;
* the cross-section and partial-width formulas are explicit tree-level
  carriers.  Lean proves their algebraic scaling, zero-coupling limits, and
  nonnegativity under the usual positive-energy/mass hypotheses;
* the listed weak decay modes conserve `(Q,B,L)` exactly using the repository's
  `QuantumNumbers` and charge-conjugation API.

No scattering amplitudes or radiative corrections are claimed here.  The
formulas are reusable tree-level interfaces whose algebraic consequences are
checked.
-/

set_option autoImplicit false

open scoped BigOperators
open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology

open Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
open Physlib.QuantumMechanics.ComplexAction.ElectroweakYangMillsThermodynamics
open Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification
open Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo
open Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
open Physlib.QuantumMechanics.ComplexAction.Particles.GluonLieAlgebra
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

/-! ## A. W/Z masses and the canonical Weinberg-angle API -/

/-- The W-mass file's cosine is the canonical `WeinbergAngle.cosWeinberg`. -/
lemma wMassFile_cosWeinberg_eq_canonical (g g' : ℝ) :
    Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.cosWeinberg g g'
      = cosWeinberg g g' :=
  rfl

/-- The W-mass file's sine is the canonical `WeinbergAngle.sinWeinberg`. -/
lemma wMassFile_sinWeinberg_eq_canonical (g g' : ℝ) :
    Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.sinWeinberg g g'
      = sinWeinberg g g' :=
  rfl

/-- The W-boson VEV mass carrier agrees with the gauge-boson-classification
carrier; both are `m_W = g v / 2`. -/
lemma wMass_eq_classification_wMassFromVEV (g v : ℝ) :
    Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass g v =
      wMassFromVEV g v :=
  rfl

/-- The Z-boson VEV mass carrier agrees with the gauge-boson-classification
carrier; both are `m_Z = sqrt(g^2+g'^2) v / 2`. -/
lemma zMass_eq_classification_zMassFromVEV (g g' v : ℝ) :
    Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass g g' v =
      zMassFromVEV g g' v :=
  rfl

/-- The canonical tree-level mass relation `m_W = m_Z cos theta_W`, using
the canonical `WeinbergAngle.cosWeinberg`. -/
lemma wMass_eq_zMass_mul_canonicalCosWeinberg
    (g g' v : ℝ) (hS : 0 < g ^ 2 + g' ^ 2) :
    Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass g v =
      Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass g g' v *
        cosWeinberg g g' := by
  simpa [Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.cosWeinberg,
    cosWeinberg]
    using
      Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass_eq_zMass_mul_cosWeinberg
        g g' v hS

/-- The photon mass in the W-mass layer is exactly zero. -/
lemma photonMass_eq_zero :
    Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.photonMass = 0 :=
  rfl

/-- The gauge-boson zoo exposes the existing mass layer: photon and gluon are
massless in the unbroken sectors, while W/Z masses are the VEV formulas. -/
lemma gaugeBosonZoo_massLayer_available (g g' v c ħ : ℝ) :
    HasGaugeBosonZooWithMassLayer g g' v c ħ :=
  gaugeBosonZooWithMassLayer_checked g g' v c ħ

/-! ## B. Electroweak couplings, `alpha`, and `sin^2 theta_W` -/

/-- The neutral weak coupling `g_Z = sqrt(g^2+g'^2)`. -/
noncomputable def zNeutralCoupling (g g' : ℝ) : ℝ :=
  Real.sqrt (g ^ 2 + g' ^ 2)

/-- `g_Z^2 = g^2+g'^2`. -/
lemma zNeutralCoupling_sq (g g' : ℝ) :
    zNeutralCoupling g g' ^ 2 = g ^ 2 + g' ^ 2 := by
  have hnonneg : 0 ≤ g ^ 2 + g' ^ 2 := by
    nlinarith [sq_nonneg g, sq_nonneg g']
  simpa [zNeutralCoupling] using Real.sq_sqrt hnonneg

/-- The charged-current vertex convention `g_W = g/sqrt(2)`. -/
noncomputable def chargedWeakVertexCoupling (g : ℝ) : ℝ :=
  g / Real.sqrt 2

/-- The square of the charged-current vertex coupling. -/
lemma chargedWeakVertexCoupling_sq (g : ℝ) :
    chargedWeakVertexCoupling g ^ 2 = g ^ 2 / 2 := by
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold chargedWeakVertexCoupling
  rw [div_pow, h2]

/-- The photon-fermion coupling `e Q`. -/
def photonFermionCoupling (e Q : ℝ) : ℝ :=
  e * Q

/-- The Z vector coupling in the convention `T3 - 2 Q sin^2(theta_W)`. -/
def zVectorCoupling (sinSqTheta T3 Q : ℝ) : ℝ :=
  T3 - 2 * Q * sinSqTheta

/-- The Z axial coupling in the convention `T3`. -/
def zAxialCoupling (T3 : ℝ) : ℝ :=
  T3

/-- Electron vector coupling: `g_V^e = -1/2 + 2 sin^2(theta_W)`. -/
lemma electron_zVectorCoupling (sinSqTheta : ℝ) :
    zVectorCoupling sinSqTheta (-(1 / 2)) (-1) = -1 / 2 + 2 * sinSqTheta := by
  unfold zVectorCoupling
  ring

/-- Electron axial coupling: `g_A^e = -1/2`. -/
lemma electron_zAxialCoupling :
    zAxialCoupling (-(1 / 2 : ℝ)) = -1 / 2 := by
  unfold zAxialCoupling
  norm_num

/-- The coupling definition gives `sin^2 theta_W = g'^2/(g^2+g'^2)`. -/
lemma sinSqWeinberg_eq_couplingRatio
    (g g' : ℝ) (hS : 0 < g ^ 2 + g' ^ 2) :
    sinWeinberg g g' ^ 2 = g' ^ 2 / (g ^ 2 + g' ^ 2) := by
  unfold sinWeinberg
  rw [div_pow, Real.sq_sqrt (le_of_lt hS)]

/-- The existing electric charge gives `alpha = e^2/(4 pi)` with
`e = g sin theta_W`. -/
lemma fineStructureConstant_from_electroweak
    (g g' : ℝ) :
    fineStructureConstant (electricCharge g g') =
      g ^ 2 * sinWeinberg g g' ^ 2 / (4 * Real.pi) := by
  unfold fineStructureConstant electricCharge
  ring

/-- The same `alpha` can be written using `e = g' cos theta_W`. -/
lemma fineStructureConstant_from_hypercharge_form
    (g g' : ℝ) :
    fineStructureConstant (electricCharge g g') =
      g' ^ 2 * cosWeinberg g g' ^ 2 / (4 * Real.pi) := by
  rw [electricCharge_symm]
  unfold fineStructureConstant
  ring

/-- The on-shell weak mixing relation, stated with the canonical Weinberg
sine and the existing W/Z mass carriers. -/
lemma sinSqWeinberg_eq_one_sub_massSq_ratio_canonical
    (g g' v : ℝ) (hg : 0 < g) (hg' : 0 < g') (hv : 0 < v) :
    sinWeinberg g g' ^ 2 =
      1 -
        Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass g v ^ 2 /
          Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass g g' v ^ 2 := by
  simpa [Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.sinWeinberg,
    sinWeinberg]
    using
      Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.sinSq_weinberg_eq_one_sub_massSq_ratio
        g g' v hg hg' hv

/-! ## C. Gluon self-interaction -/

/-- The concrete `su(3)` three-gluon vertex is nonzero:
`[lambda_1,lambda_2] = 2 i lambda_3 != 0`. -/
lemma lambda12_gluon_threeVertex_nonzero :
    lambda1 * lambda2 - lambda2 * lambda1 ≠ 0 := by
  intro h
  have hz :
      ((2 * Complex.I) • lambda3 : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
    rw [← comm_12, h]
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) hz
  simp [lambda3] at h00

/-- Concrete gluon self-interaction and the basis-free Lie/Jacobi structure
are available together. -/
lemma gluon_selfInteraction_checked
    (A B C : Matrix (Fin 3) (Fin 3) ℂ) :
    lambda1 * lambda2 - lambda2 * lambda1 ≠ 0
      ∧ lambda1 * lambda2 - lambda2 * lambda1 = (2 * Complex.I) • lambda3
      ∧ ⁅A, B⁆ = -⁅B, A⁆
      ∧ ⁅A, A⁆ = 0
      ∧ ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 :=
  ⟨lambda12_gluon_threeVertex_nonzero, comm_12,
    (gluon_lie_structure A B C).1,
    (gluon_lie_structure A B C).2.1,
    (gluon_lie_structure A B C).2.2⟩

/-! ## D. Tree-level cross-section and partial-width carriers -/

/-- Tree-level massless QED carrier:
`e+ e- -> mu+ mu-`, `sigma = 4 pi alpha^2/(3 s)`. -/
noncomputable def eeToMuonPairCrossSection (alpha s : ℝ) : ℝ :=
  4 * Real.pi * alpha ^ 2 / (3 * s)

/-- The `e+e- -> mu+mu-` carrier is nonnegative for positive `s`. -/
lemma eeToMuonPairCrossSection_nonneg
    (alpha s : ℝ) (hs : 0 < s) :
    0 ≤ eeToMuonPairCrossSection alpha s := by
  unfold eeToMuonPairCrossSection
  positivity

/-- At zero electromagnetic coupling the QED carrier vanishes. -/
lemma eeToMuonPairCrossSection_zero_coupling (s : ℝ) :
    eeToMuonPairCrossSection 0 s = 0 := by
  simp [eeToMuonPairCrossSection]

/-- The QED carrier scales quadratically in `alpha`. -/
lemma eeToMuonPairCrossSection_alpha_scaling (c alpha s : ℝ) :
    eeToMuonPairCrossSection (c * alpha) s =
      c ^ 2 * eeToMuonPairCrossSection alpha s := by
  unfold eeToMuonPairCrossSection
  ring

/-- Multiplying by `s` removes the propagator denominator. -/
lemma eeToMuonPairCrossSection_mul_s
    (alpha : ℝ) {s : ℝ} (hs : s ≠ 0) :
    eeToMuonPairCrossSection alpha s * s = 4 * Real.pi * alpha ^ 2 / 3 := by
  unfold eeToMuonPairCrossSection
  field_simp [hs]

/-- Low-energy four-Fermi neutrino carrier `sigma ~ G_F^2 E^2 / pi`. -/
noncomputable def fourFermiNeutrinoCrossSection (GF E : ℝ) : ℝ :=
  GF ^ 2 * E ^ 2 / Real.pi

/-- The four-Fermi carrier is nonnegative. -/
lemma fourFermiNeutrinoCrossSection_nonneg (GF E : ℝ) :
    0 ≤ fourFermiNeutrinoCrossSection GF E := by
  unfold fourFermiNeutrinoCrossSection
  positivity

/-- The four-Fermi carrier vanishes at zero weak coupling. -/
lemma fourFermiNeutrinoCrossSection_zero_coupling (E : ℝ) :
    fourFermiNeutrinoCrossSection 0 E = 0 := by
  simp [fourFermiNeutrinoCrossSection]

/-- Tree-level massless leptonic W partial width:
`Gamma(W -> l nu) = g^2 m_W/(48 pi)`. -/
noncomputable def wLeptonicPartialWidth (g mW : ℝ) : ℝ :=
  g ^ 2 * mW / (48 * Real.pi)

/-- The W leptonic width is nonnegative for nonnegative `m_W`. -/
lemma wLeptonicPartialWidth_nonneg
    (g mW : ℝ) (hmW : 0 ≤ mW) :
    0 ≤ wLeptonicPartialWidth g mW := by
  unfold wLeptonicPartialWidth
  positivity

/-- The W leptonic width vanishes at zero weak coupling. -/
lemma wLeptonicPartialWidth_zero_coupling (mW : ℝ) :
    wLeptonicPartialWidth 0 mW = 0 := by
  simp [wLeptonicPartialWidth]

/-- Tree-level Z partial width carrier:
`Gamma(Z -> f fbar) = N_c G_F m_Z^3 (g_V^2+g_A^2)/(6 pi sqrt 2)`. -/
noncomputable def zFermionPartialWidth
    (NC GF mZ gV gA : ℝ) : ℝ :=
  NC * GF * mZ ^ 3 * (gV ^ 2 + gA ^ 2) / (6 * Real.pi * Real.sqrt 2)

/-- The Z partial-width carrier is nonnegative under the standard
nonnegative input hypotheses. -/
lemma zFermionPartialWidth_nonneg
    (NC GF mZ gV gA : ℝ)
    (hNC : 0 ≤ NC) (hGF : 0 ≤ GF) (hmZ : 0 ≤ mZ) :
    0 ≤ zFermionPartialWidth NC GF mZ gV gA := by
  unfold zFermionPartialWidth
  positivity

/-- The Z partial-width carrier vanishes at zero Fermi coupling. -/
lemma zFermionPartialWidth_zero_GF (NC mZ gV gA : ℝ) :
    zFermionPartialWidth NC 0 mZ gV gA = 0 := by
  simp [zFermionPartialWidth]

/-! ## E. Specific weak decay modes and charge conservation -/

/-- The charged-lepton generation label used for W decay bookkeeping. -/
inductive LeptonGeneration where
  | electron | muon | tau
  deriving DecidableEq

/-- A charged lepton `l-` has `(Q,B,L)=(-1,0,1)`. -/
def chargedLeptonQN (_ : LeptonGeneration) : QuantumNumbers :=
  ⟨-1, 0, 1⟩

/-- A neutrino has `(Q,B,L)=(0,0,1)`. -/
def neutrinoQN (_ : LeptonGeneration) : QuantumNumbers :=
  ⟨0, 0, 1⟩

/-- A charged antilepton `l+` is the conjugate of `l-`. -/
def chargedAntiLeptonQN (l : LeptonGeneration) : QuantumNumbers :=
  conjugate (chargedLeptonQN l)

/-- An antineutrino is the conjugate of the neutrino. -/
def antiNeutrinoQN (l : LeptonGeneration) : QuantumNumbers :=
  conjugate (neutrinoQN l)

/-- The additive quantum numbers of `W+`. -/
def wPlusQN : QuantumNumbers :=
  ⟨gaugeBosonCharge GaugeBoson.wPlus, 0, 0⟩

/-- The additive quantum numbers of `W-`. -/
def wMinusQN : QuantumNumbers :=
  ⟨gaugeBosonCharge GaugeBoson.wMinus, 0, 0⟩

/-- The additive quantum numbers of `Z0`. -/
def zBosonQN : QuantumNumbers :=
  ⟨gaugeBosonCharge GaugeBoson.zZero, 0, 0⟩

/-- `W+ -> l+ + nu_l` conserves `(Q,B,L)`. -/
lemma wPlus_leptonicDecay_conserves (l : LeptonGeneration) :
    wPlusQN = chargedAntiLeptonQN l + neutrinoQN l := by
  cases l <;> ext <;>
    simp [wPlusQN, chargedAntiLeptonQN, chargedLeptonQN, neutrinoQN,
      conjugate, gaugeBosonCharge]

/-- `W- -> l- + anti-nu_l` conserves `(Q,B,L)`. -/
lemma wMinus_leptonicDecay_conserves (l : LeptonGeneration) :
    wMinusQN = chargedLeptonQN l + antiNeutrinoQN l := by
  cases l <;> ext <;>
    simp [wMinusQN, chargedLeptonQN, antiNeutrinoQN, neutrinoQN,
      conjugate, gaugeBosonCharge]

/-- `Z0 -> f + anti-f` conserves `(Q,B,L)` for every particle quantum-number
vector `f`. -/
lemma zToFermionAntifermion_conserves (q : QuantumNumbers) :
    zBosonQN = q + conjugate q := by
  rw [pair_annihilates q]
  ext <;> simp [zBosonQN, gaugeBosonCharge]

/-- The weak decay modes covered in this module. -/
inductive WeakDecayMode where
  | wPlusLeptonic (l : LeptonGeneration)
  | wMinusLeptonic (l : LeptonGeneration)
  | zFermionPair (q : QuantumNumbers)

/-- Initial quantum numbers for the listed weak decay modes. -/
def weakDecayInitial : WeakDecayMode → QuantumNumbers
  | .wPlusLeptonic _ => wPlusQN
  | .wMinusLeptonic _ => wMinusQN
  | .zFermionPair _ => zBosonQN

/-- Final quantum numbers for the listed weak decay modes. -/
def weakDecayFinal : WeakDecayMode → QuantumNumbers
  | .wPlusLeptonic l => chargedAntiLeptonQN l + neutrinoQN l
  | .wMinusLeptonic l => chargedLeptonQN l + antiNeutrinoQN l
  | .zFermionPair q => q + conjugate q

/-- Every listed weak decay mode conserves `(Q,B,L)`. -/
lemma weakDecayMode_conserves_QBL (mode : WeakDecayMode) :
    weakDecayInitial mode = weakDecayFinal mode := by
  cases mode with
  | wPlusLeptonic l =>
      exact wPlus_leptonicDecay_conserves l
  | wMinusLeptonic l =>
      exact wMinus_leptonicDecay_conserves l
  | zFermionPair q =>
      exact zToFermionAntifermion_conserves q

/-! ## F. Repo-facing synthesis theorem -/

/-- Main checked capability for electroweak gauge-boson phenomenology.

The theorem deliberately separates algebraic tree-level formulas from any
unformalized analytic scattering derivation or radiative correction. -/
lemma electroweakGaugeBosonPhenomenology_checked
    (g g' v c ħ alpha s GF E mW : ℝ)
    (hS : 0 < g ^ 2 + g' ^ 2) (hs : 0 < s) (hmW : 0 ≤ mW) :
    Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.wMass g v =
        Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.zMass g g' v *
          cosWeinberg g g'
      ∧ Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.photonMass = 0
      ∧ HasGaugeBosonZooWithMassLayer g g' v c ħ
      ∧ sinWeinberg g g' ^ 2 = g' ^ 2 / (g ^ 2 + g' ^ 2)
      ∧ fineStructureConstant (electricCharge g g') =
          g ^ 2 * sinWeinberg g g' ^ 2 / (4 * Real.pi)
      ∧ lambda1 * lambda2 - lambda2 * lambda1 ≠ 0
      ∧ eeToMuonPairCrossSection alpha s * s = 4 * Real.pi * alpha ^ 2 / 3
      ∧ 0 ≤ eeToMuonPairCrossSection alpha s
      ∧ 0 ≤ fourFermiNeutrinoCrossSection GF E
      ∧ 0 ≤ wLeptonicPartialWidth g mW
      ∧ ∀ mode : WeakDecayMode, weakDecayInitial mode = weakDecayFinal mode := by
  exact ⟨wMass_eq_zMass_mul_canonicalCosWeinberg g g' v hS,
    photonMass_eq_zero,
    gaugeBosonZoo_massLayer_available g g' v c ħ,
    sinSqWeinberg_eq_couplingRatio g g' hS,
    fineStructureConstant_from_electroweak g g',
    lambda12_gluon_threeVertex_nonzero,
    eeToMuonPairCrossSection_mul_s alpha (ne_of_gt hs),
    eeToMuonPairCrossSection_nonneg alpha s hs,
    fourFermiNeutrinoCrossSection_nonneg GF E,
    wLeptonicPartialWidth_nonneg g mW hmW,
    weakDecayMode_conserves_QBL⟩


/-! ## D. Higgs mechanism: the neutral gauge-boson mass matrix -/

/-- **The neutral gauge-boson mass-squared matrix** in the `(W³, B)` basis, generated by the Higgs
kinetic term `|D_μφ|²` evaluated at the VEV `v`: `M = (v²/4)·[[g², −gg'],[−gg', g'²]]`. Its eigenvalues
are the physical neutral masses. -/
noncomputable def neutralMassMatrix (g g' v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v ^ 2 / 4 * g ^ 2, -(v ^ 2 / 4 * (g * g'));
     -(v ^ 2 / 4 * (g * g')), v ^ 2 / 4 * g' ^ 2]

/-- **[The photon stays massless — `det M = 0`]** the mass matrix is singular, so one eigenvalue (the
photon mass-squared) vanishes: the Higgs mechanism leaves one neutral combination massless. -/
lemma neutralMassMatrix_det_zero (g g' v : ℝ) : (neutralMassMatrix g g' v).det = 0 := by
  simp only [neutralMassMatrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **[The trace is the `Z` mass-squared] `Tr M = (v²/4)(g² + g'²) = m_Z²`.** -/
lemma neutralMassMatrix_trace (g g' v : ℝ) :
    (neutralMassMatrix g g' v).trace = v ^ 2 / 4 * (g ^ 2 + g' ^ 2) := by
  simp only [neutralMassMatrix, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **[Higgs mechanism: the neutral masses are exactly `{0, m_Z²}`]** the characteristic polynomial
`λ² − (Tr M) λ + det M` of the neutral mass matrix factors as `λ · (λ − m_Z²)` with
`m_Z² = (v²/4)(g² + g'²)`. So the two neutral mass-squared eigenvalues are precisely `0` (the photon) and
`m_Z²` (the `Z`): the masses are *generated* — read off the mass matrix eigenvalues — not merely posited
as VEV relations. -/
lemma neutralMassMatrix_char_factors (g g' v lam : ℝ) :
    lam ^ 2 - (neutralMassMatrix g g' v).trace * lam + (neutralMassMatrix g g' v).det
      = lam * (lam - v ^ 2 / 4 * (g ^ 2 + g' ^ 2)) := by
  rw [neutralMassMatrix_det_zero, neutralMassMatrix_trace]; ring

end Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.wMass_eq_zMass_mul_canonicalCosWeinberg where
  formalizes @ "claim:the-w-mass-equals-the-z-mass-times-the-cosine-of-the-weinberg-angle-the-tree-level-custodial-rho-equals-one-relation",
  supported_by @ "paper:pdg-2026-review-electroweak-model"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.neutralMassMatrix_char_factors where
  formalizes @ "claim:the-electroweak-neutral-mass-matrix-characteristic-polynomial-factors-as-lambda-times-lambda-minus-m-z-squared-so-the-neutral-masses-zero-and-m-z-squared-are-eigenvalues",
  requires @ "claim:the-w-mass-equals-the-z-mass-times-the-cosine-of-the-weinberg-angle-the-tree-level-custodial-rho-equals-one-relation",
  supported_by @ "paper:pdg-2026-review-electroweak-model"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.photonMass_eq_zero where
  formalizes @ "claim:the-photon-is-massless-the-zero-eigenvalue-of-the-neutral-gauge-boson-mass-matrix"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.sinSqWeinberg_eq_one_sub_massSq_ratio_canonical where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak.sinSq_weinberg_eq_one_sub_massSq_ratio",
  formalizes @ "claim:the-weinberg-angle-obeys-sin-squared-equals-one-minus-the-w-to-z-mass-squared-ratio"

zil_file_contract physlib.electroweakGaugeBosonPhenomenology where
  promises "Electroweak gauge-boson phenomenology at tree level: the W mass equals the Z mass times the cosine of the Weinberg angle (the custodial rho-equals-one relation); the neutral gauge-boson mass matrix has characteristic polynomial factoring as lambda times lambda minus m-Z-squared, so the photon is massless (zero eigenvalue) and the Z has mass m-Z-squared; the Weinberg angle obeys sin-squared equals one minus the W-to-Z mass-squared ratio; and neutral- and charged-current couplings, cross sections and partial widths are non-negative and correctly scaled, with weak-decay quantum numbers conserved."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.neutralMassMatrix",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.zNeutralCoupling"]
  forbids_substitutes ["a derivation of the numerical gauge-boson masses or the Weinberg angle, which are PDG inputs",
    "a loop-level or radiative-correction treatment, only the tree-level relations are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.wMass_eq_zMass_mul_canonicalCosWeinberg,
    Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.photonMass_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.neutralMassMatrix_det_zero,
    Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.neutralMassMatrix_char_factors,
    Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.sinSqWeinberg_eq_one_sub_massSq_ratio_canonical,
    Physlib.QuantumMechanics.ComplexAction.Particles.ElectroweakGaugeBosonPhenomenology.electroweakGaugeBosonPhenomenology_checked]

/- ZIL-END -/
