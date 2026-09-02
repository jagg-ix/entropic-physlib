/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ComplexDAlembertSecondBianchi
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumGravityCausalDiamond
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeGravFluidNoether
public import Physlib.SpaceAndTime.ExponentialEntropicLapse
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
meta import Zil

/-!
# A. Complex-Action/Entropic-Time Gravity Synthesis Bridge

This file ports the usable part of the gravity inventory in `reference tree`
without importing its `Gravitas` shim layer.  The reference material there
has several connected lanes:

* contracted Bianchi + Einstein equation ⇒ stress-energy conservation;
* complex/entropic Einstein equations ⇒ real and entropic source
  conservation;
* ADM/Wheeler-DeWitt + modular/horizon/entropic-lapse bookkeeping.
* Schwinger-Keldysh/ADM entropy damping via exponential lapse factors
  and coercive complex-action weights;
* viscosity/Mpemba/Cameron damping as a scalar consequence of the
  gravitational-fluid complex Noether charge;
* Bekenstein-Jacobson horizon bits connected to Verch quasifree horizon
  cells and the real Noether sector.

Physlib already has stronger carriers for those lanes:
`ComplexEinstein.EinsteinFieldEquationsPhysLean`, `LeviCivita.GravitationalTensor`,
`Curvature.ComplexDAlembertSecondBianchi`, `ComplexEinstein.WheelerDeWittLusanna`,
`ComplexEinstein.WheelerDeWittComplexEinstein`, `CausalDiamond.QuantumGravityCausalDiamond`,
`ExponentialEntropicLapse`, `PathIntegral.ComplexActionDampingCoercivity`,
`GravitationalFieldEquations.GravitationalFluidComplexNoether`, `AlgebraicQFTQuasifree.QuasifreeGravFluidNoether`, and
`BekensteinJacobsonEntropicBits`.  The theorems below assemble those carriers
into reusable bridge statements.

The complex-action/entropic-time files that remain reference-only for now are the VML path-integral
rigidity theorem, `Gravitas` discrete geodesic/event carriers, smooth/FRW
certificate shells, and Lovelock/conditional-Einstein records.  Physlib does
not yet have native carriers for those layers, so copying them would only
package assumptions.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis

open Real
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.Curvature.ComplexDAlembertSecondBianchi
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumGravityCausalDiamond
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
open Physlib.QFT.Wick.Consistency
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether
open Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeGravFluidNoether
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.Thermodynamics

variable {ι : Type*}

/-! ## A.1. Bianchi/EFE Stress Conservation and Levi-Civita Balance -/

/-- **complex-action/entropic-time Bianchi lane, realised on Physlib carriers.**

The complex-action/entropic-time `RelativityGRBianchiBridge` route
`∇·G = 0 ∧ G = κT ∧ κ ≠ 0 ⇒ ∇·T = 0` is strengthened here with
the Levi-Civita gravitational tensor:

* matter stress is conserved;
* the gravitational/inertial tensor is divergence-free;
* the gravitational tensor is exactly `-T`;
* the d'Alembert balance `T + A = 0` holds.
-/
lemma bianchi_einstein_leviCivita_stress_gravity_balance
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (κ : ℝ)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ)
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0)
    (hκ : κ ≠ 0) :
    Div T = 0
      ∧ Div (gravitationalTensor Ric scalarR g κ) = 0
      ∧ gravitationalTensor Ric scalarR g κ = -T
      ∧ T + gravitationalTensor Ric scalarR g κ = 0 :=
  ⟨bianchi_implies_conservation Div Ric scalarR g T κ hEFE hBianchi hκ,
    gravitationalTensor_divergence_free Div Ric scalarR g κ hBianchi,
    gravitationalTensor_eq_neg_matter Ric scalarR g T κ hκ hEFE,
    dAlembert_balance Ric scalarR g T κ hκ hEFE⟩

/-! ## A.2. Complex Bianchi / Entropic-Source Conservation -/

/-- **Complex complex-action/entropic-time gravity lane, realised on Physlib carriers.**

The complex Einstein equation plus the complex Bianchi identity gives the
same conservation chain for both the ordinary stress tensor and the entropic
stress tensor.  The theorem also projects the real Bianchi component back
to the Levi-Civita gravitational tensor, so the complex source-conservation
result can feed the older real-gravity balance files.
-/
lemma complex_bianchi_leviCivita_source_conservation
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ) (κ : ℝ)
    (hκ : κ ≠ 0)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ)
    (hBianchi : complexDiv Div (complexEinsteinTensor (einsteinTensor Ric scalarR g) Λ) = 0) :
    complexDiv Div (complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ) = 0
      ∧ complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0
      ∧ Div T = 0
      ∧ Div S = 0
      ∧ Div (gravitationalTensor Ric scalarR g κ) = 0 := by
  obtain ⟨hA, hBal, hT, hS⟩ :=
    complex_dAlembert_bianchi Div Ric scalarR g Λ T S κ hκ hEFE hBianchi
  obtain ⟨hBG, _hBΛ⟩ :=
    (complexBianchi_iff Div (einsteinTensor Ric scalarR g) Λ).mp hBianchi
  exact ⟨hA, hBal, hT, hS,
    gravitationalTensor_divergence_free Div Ric scalarR g κ hBG⟩

/-! ## A.3. ADM/Wheeler-DeWitt Lane Plus Entropic Lapse -/

variable {d : ℕ}

/-- **ADM/Wheeler-DeWitt + entropic-lapse bridge.**

This is the Physlib-native counterpart of the complex-action/entropic-time ADM-WDW entropic
holography lane: the quantized ADM Hamiltonian constraint is kept as the
Wheeler-DeWitt theorem, while the communicating/entropic clock is kept in
`SpaceTime.EntropicLapseFactor`.
-/
lemma adm_wdw_entropic_lapse_contract
    (R3 KdotK HI : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0)
    (A : Physlib.SpaceTime.ADMData d) (lam : SpaceTime d → ℝ)
    (hLam : ∀ y, 0 ≤ lam y)
    (x : SpaceTime d) (dt O_inf : ℝ) :
    (WheelerDeWitt (hamiltonianConstraint R3 KdotK K) HI Ψ
        ↔ (R3 + yorkTime K ^ 2 = KdotK) ∧ HI = 0)
      ∧ A.admEntropicProperTime lam x dt
          = A.admStaticProperTime x dt + lam x * dt
      ∧ Physlib.SpaceTime.EntropicLapseFactor.entropicProperTimeOnADM
          (Physlib.SpaceTime.EntropicLapseFactor.ofEntropyProductionRate A lam hLam) A x dt
          = A.admEntropicProperTime lam x dt
      ∧ (O_inf / A.entropicEffectiveLapse lam x) * A.entropicEffectiveLapse lam x = O_inf :=
  ⟨wheelerDeWitt_lusanna R3 KdotK HI K Ψ hΨ,
    A.admEntropicProperTime_decomposes lam x dt,
    Physlib.SpaceTime.ofEntropyProductionRate_equiv_admEntropicProperTime A lam hLam x dt,
    A.entropicEffectiveLapse_tolman_invariant hLam O_inf x⟩

/-! ## A.4. ADM/Wheeler-DeWitt Lane Plus Causal-Diamond Horizon Mode -/

/-- **Gravity path-integral/horizon lane joined to ADM-WDW.**

complex-action/entropic-time's holographic lane packages ADM-WDW, modular time, and horizon
thermodynamics into one witness.  Physlib already has the concrete horizon
mode: the one-loop fermion determinant is the causal-diamond horizon energy,
and the reversible limit is the static-patch/luminal limit.  This theorem
bundles that horizon mode with the ADM-WDW constraint and entropic-lapse
identities above.
-/
lemma adm_wdw_horizon_entropic_synthesis
    (R3 KdotK HI : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0)
    (A : Physlib.SpaceTime.ADMData d) (lam : SpaceTime d → ℝ)
    (hLam : ∀ y, 0 ≤ lam y)
    (x : SpaceTime d) (dt O_inf η : ℝ) :
    (WheelerDeWitt (hamiltonianConstraint R3 KdotK K) HI Ψ
        ↔ (R3 + yorkTime K ^ 2 = KdotK) ∧ HI = 0)
      ∧ A.admEntropicProperTime lam x dt
          = A.admStaticProperTime x dt + lam x * dt
      ∧ berezin (fermionGaussian (bogoliubovEnergy (Real.sinh η) 1)) = Real.cosh η
      ∧ (bogoliubovEntropicTime (Real.sinh η) 1 = 0
          ↔ Real.tanh η = 1 ∨ Real.tanh η = -1)
      ∧ (O_inf / A.entropicEffectiveLapse lam x) * A.entropicEffectiveLapse lam x = O_inf := by
  obtain ⟨hWDW, hADM, _hMult, hTolman⟩ :=
    adm_wdw_entropic_lapse_contract R3 KdotK HI K Ψ hΨ A lam hLam x dt O_inf
  obtain ⟨hDet, hRev, _hDiag, _hJ⟩ := quantumGravity_horizon_synthesis η
  exact ⟨hWDW, hADM, hDet, hRev, hTolman⟩

/-! ## A.5. Schwinger-Keldysh / ADM Entropy Damping Lane -/

/-- **Schwinger-Keldysh ADM entropy insertion, realised on Physlib carriers.**

complex-action/entropic-time's `SchwingerKeldyshADMBridge` and `ADMEntropyPathIntegralBridge`
record `N sqrt(h) lambda` entropy insertions and their damping factors.
Physlib already has the pointwise ADM lapse, the exponential entropic
lapse, and the complex-action damping bound.  This theorem bundles those
facts in the common use case: non-negative accumulated entropy potential
`phi` shrinks the effective ADM lapse and a coercive imaginary action
controls the path-integral modulus.
-/
lemma adm_sk_entropy_damping_contract
    (A : Physlib.SpaceTime.ADMData d) (phi : SpaceTime d → ℝ)
    (hphi : ∀ x, 0 ≤ phi x)
    (S_R S_I C normPhiSq hbar : ℝ)
    (hcoer : IsCoercive S_I C normPhiSq) (hhbar : 0 < hbar)
    (x : SpaceTime d) :
    0 < Physlib.SpaceTime.exponentialEntropicLapse A.lapse.N phi x
      ∧ Physlib.SpaceTime.exponentialDampingFactor (phi x) ≤ 1
      ∧ (Physlib.SpaceTime.EntropicLapseFactor.ofExponentialDamping phi).Λ x
          = Physlib.SpaceTime.exponentialDampingFactor (phi x)
      ∧ ‖complexActionWeight S_R S_I hbar‖
          ≤ Real.exp (-(C * normPhiSq / hbar)) :=
  ⟨Physlib.SpaceTime.exponentialEntropicLapse_pos A.lapse.N_pos x,
    Physlib.SpaceTime.exponentialDampingFactor_le_one (hphi x),
    Physlib.SpaceTime.EntropicLapseFactor.ofExponentialDamping_Λ_eq phi x,
    damping_bound S_R S_I C normPhiSq hbar hcoer hhbar⟩

/-! ## A.6. Viscosity / Mpemba / Cameron Lane into Gravitational Noether -/

/-- Cameron suppression weight `exp(-tau)` used by the viscosity/Mpemba lane. -/
def cameronWeight (tau : ℝ) : ℝ := Real.exp (-tau)

lemma cameronWeight_pos (tau : ℝ) : 0 < cameronWeight tau :=
  Real.exp_pos _

lemma cameronWeight_le_one {tau : ℝ} (htau : 0 ≤ tau) :
    cameronWeight tau ≤ 1 := by
  unfold cameronWeight
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr htau)

/-- More accumulated entropic time gives stronger Cameron suppression. -/
lemma cameron_suppression_ordering {tauHot tauCold : ℝ}
    (h : tauCold ≤ tauHot) :
    cameronWeight tauHot ≤ cameronWeight tauCold := by
  unfold cameronWeight
  exact Real.exp_le_exp.mpr (neg_le_neg h)

/-- Damped enstrophy, the scalar imaginary-stress component in the complex-action/entropic-time
viscosity/Mpemba lane. -/
def dampedEnstrophy (Omega tau : ℝ) : ℝ := Omega * cameronWeight tau

lemma dampedEnstrophy_le (Omega : ℝ) {tau : ℝ}
    (hOmega : 0 ≤ Omega) (htau : 0 ≤ tau) :
    dampedEnstrophy Omega tau ≤ Omega := by
  unfold dampedEnstrophy
  calc
    Omega * cameronWeight tau ≤ Omega * 1 :=
      mul_le_mul_of_nonneg_left (cameronWeight_le_one htau) hOmega
    _ = Omega := mul_one _

/-- **Einstein-viscosity/Mpemba lane joined to the gravitational Noether sector.**

complex-action/entropic-time's viscosity/Mpemba files use the same entropic-time accumulator for
fluid damping and Einstein locality.  In Physlib, the connected gravity
hook is the gravitational-fluid complex Noether charge: its real part is
the causal-diamond Wald charge and its imaginary part is the enstrophy
rate.  This theorem adds the scalar Cameron ordering used by the Mpemba
lane to that existing Noether package.
-/
lemma viscosity_mpemba_gravFluid_noether_contract
    (kappa area k volume Lambda Vzeta dim G nu P VS Omega tauHot tauCold : ℝ)
    (hpi : (0 : ℝ) < Real.pi) (hG : G ≠ 0) (hdim : dim - 2 ≠ 0)
    (hStokes :
      noetherCharge kappa area G =
        noetherCurrentIntegral kappa k volume Lambda Vzeta dim G)
    (htauOrder : tauCold ≤ tauHot)
    (hOmega : 0 ≤ Omega) (htauHot : 0 ≤ tauHot) :
    (gravFluidNoetherCharge kappa area G nu P VS).re = noetherCharge kappa area G
      ∧ (dim - 2) * kappa * area = (dim - 1) * kappa * k * volume + 2 * Vzeta * Lambda
      ∧ ((gravFluidNoetherCharge kappa area G nu P VS).im ≤ 0 ↔ VS ≤ nu * P)
      ∧ cameronWeight tauHot ≤ cameronWeight tauCold
      ∧ dampedEnstrophy Omega tauHot ≤ Omega :=
  ⟨gravFluidNoetherCharge_re kappa area G nu P VS,
    smarr_from_noether kappa area k volume Lambda Vzeta dim G hpi hG hdim hStokes,
    gravFluidNoetherCharge_im_nonpos_iff kappa area G nu P VS,
    cameron_suppression_ordering htauOrder,
    dampedEnstrophy_le Omega hOmega htauHot⟩

/-! ## A.7. Horizon Bits / Clausius Lane into Verch-Noether Gravity -/

/-- **Bekenstein-Jacobson horizon bits joined to Verch/Noether gravity.**

This ports the useful part of the complex-action/entropic-time conditional-Einstein and
holographic lanes that is already represented in Physlib: horizon heat,
entropy, area bits, and the real Noether sector are all the same
geometric object.  The result deliberately stops at the algebraic
Clausius/Bekenstein identity; the full Lovelock/Einstein derivation
remains a future native carrier rather than a copied certificate.
-/
lemma horizon_bits_noether_verch_contract
    (kappa area G ellP nu P VS hbar eta deltaQ T dS : ℝ)
    (hellP : ellP ≠ 0) (hT : T ≠ 0)
    (hClausius : deltaQ = T * dS)
    (hBekenstein : dS = (Constants.kB * area) / (4 * ellP ^ 2))
    (hhbar : hbar ≠ 0) (heta : 0 < eta)
    (phi : Fin 2 → ℝ) (hcell : schmidtNumber eta = cellBondDimension) :
    (gravFluidNoetherCharge kappa area G nu P VS).re = noetherCharge kappa area G
      ∧ tauEntFromEntropy dS = clausiusTauEnt deltaQ T
      ∧ tauEntFromEntropy dS = bekensteinTauEnt area ellP
      ∧ bekensteinTauEnt area ellP = Real.log 2 * bekensteinBits area ellP
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle hbar eta) phi
          = Real.exp (-(1 / 4)) := by
  obtain ⟨hNoether, _hBH, hCell⟩ :=
    gravNoether_area_is_verchQuasifree_entropy
      kappa area G ellP nu P VS hbar eta hellP hhbar heta phi hcell
  obtain ⟨hCl, hBek, hBits⟩ :=
    entropicTime_four_way_identity
      (δQ := deltaQ) (T := T) (dS := dS) (dA := area) (ℓP := ellP)
      hT hellP hClausius hBekenstein
  exact ⟨hNoether, hCl, hBek, hBits, hCell⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.bianchi_einstein_leviCivita_stress_gravity_balance where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.dAlembert_balance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.gravitationalTensor_divergence_free",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.gravitationalTensor_eq_neg_matter",
  formalizes @ "claim:the-contracted-bianchi-identity-plus-the-einstein-field-equation-give-stress-energy-conservation-and-the-levi-civita-gravitational-tensor-is-divergence-free-equal-to-minus-the-matter-tensor-in-dalembert-balance"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.complex_bianchi_leviCivita_source_conservation where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.gravitationalTensor_divergence_free",
  formalizes @ "claim:the-complex-einstein-equation-plus-the-complex-bianchi-identity-conserve-both-the-ordinary-and-the-entropic-stress-tensors-and-project-the-real-bianchi-component-back-to-the-levi-civita-gravitational-tensor-divergence-freedom",
  requires @ "claim:the-contracted-bianchi-identity-plus-the-einstein-field-equation-give-stress-energy-conservation-and-the-levi-civita-gravitational-tensor-is-divergence-free-equal-to-minus-the-matter-tensor-in-dalembert-balance"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.adm_wdw_entropic_lapse_contract where
  supported_by @ "lean:Physlib.SpaceTime.EntropicLapseFactor",
  formalizes @ "claim:the-quantized-adm-hamiltonian-constraint-is-the-wheeler-dewitt-equation-the-adm-entropic-proper-time-decomposes-into-the-static-proper-time-plus-the-entropy-production-lapse-and-the-entropic-effective-lapse-is-tolman-invariant"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.adm_sk_entropy_damping_contract where
  supported_by @ "lean:Physlib.SpaceTime.EntropicLapseFactor",
  supported_by @ "lean:WignerSergiSystem.damping_bound",
  formalizes @ "claim:a-non-negative-accumulated-entropy-potential-keeps-the-exponential-entropic-adm-lapse-positive-and-below-one-and-a-coercive-imaginary-action-bounds-the-complex-action-path-integral-modulus-by-the-entropic-damping-factor"

zil_file_contract physlib.gravitySynthesis where
  promises "The gravity synthesis bridge: ports the usable gravity inventory onto Physlib carriers across several connected lanes. The contracted Bianchi identity plus the Einstein equation give stress-energy conservation with the Levi-Civita gravitational tensor divergence-free and in d'Alembert balance (bianchi_einstein_leviCivita_stress_gravity_balance); the complex Einstein equation plus the complex Bianchi identity conserve both the ordinary and the entropic stress tensors and project back to the real Levi-Civita tensor (complex_bianchi_leviCivita_source_conservation). The ADM/Wheeler-DeWitt lane keeps the quantized Hamiltonian constraint as Wheeler-DeWitt while the entropic clock decomposes the ADM proper time into a static part plus an entropy-production lapse, Tolman-invariant (adm_wdw_entropic_lapse_contract); and the Schwinger-Keldysh lane shows a non-negative entropy potential shrinks the effective ADM lapse while a coercive imaginary action bounds the path-integral modulus (adm_sk_entropy_damping_contract)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.gravitationalTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinTensor"]
  forbids_substitutes ["the ADM/Wheeler-DeWitt canonical-gravity infrastructure, the Bianchi identities, and the entropic-lapse and coercivity carriers, which are the cited inputs bundled by these contraction theorems",
    "any new gravitational dynamics, the file only assembles existing carriers into synthesis contracts"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.bianchi_einstein_leviCivita_stress_gravity_balance,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.complex_bianchi_leviCivita_source_conservation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.adm_wdw_entropic_lapse_contract,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.adm_sk_entropy_damping_contract]

/- ZIL-END -/
