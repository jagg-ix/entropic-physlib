/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.ProblemOfTimeInstance
public import Physlib.SpaceAndTime.ADMEntropicProperTime
public import Physlib.Gravity.Canonical.ProblemOfTime
public import Physlib.Thermodynamics.Landauer
public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.DiracConstraints
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ADMSectionII
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant

/-!
# Kuchař problem-of-time bridge

This ports the reusable Kuchař material from the reference tree into the
Physlib gravity/quantum-clock stack.  The file deliberately keeps only the
parts that connect to existing carriers:

* the Wheeler-DeWitt split constraint `H_clock + H_system = 0`;
* bridges from `Landauer.PageWoottersBipartite`, `ComplexEinstein.WheelerDeWittLusanna`,
  `ProblemOfTimeInstance`, `EntropicTime.GravitySynthesis`, and the ADM
  lapse-contour Hamiltonian-gauge layer.

The paper anchors, exact Kuchař A/B/C contract, six-problem status ledger, and
constructive progress model live in `Physlib.Gravity.Canonical.ProblemOfTime`.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.KucharProblemOfTime

open QuantumInfo.Finite
open Physlib.Gravity.Canonical
open Physlib.SpaceAndTime
open Physlib.Thermodynamics.Landauer
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.DiracConstraints
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition


/-- A Page-Wootters bipartite carrier is a Kuchař WDW split witness. -/
def pageWoottersBipartite_to_kucharWDWSplit
    {d_sys d_clock : Type} [Fintype d_sys] [DecidableEq d_sys]
    [Fintype d_clock] [DecidableEq d_clock]
    (M : PageWoottersBipartite d_sys d_clock) : KucharWDWSplit :=
  { H_clock := M.E_clock
    H_system := M.E_sys
    constraint := by
      have h := M.WDW_constraint
      linarith }

/-- Page-Wootters Eq. 14 gives the Kuchař timeless anti-balance. -/
lemma pageWoottersBipartite_realizes_kuchar_timeless_form
    {d_sys d_clock : Type} [Fintype d_sys] [DecidableEq d_sys]
    [Fintype d_clock] [DecidableEq d_clock]
    (M : PageWoottersBipartite d_sys d_clock) :
    (pageWoottersBipartite_to_kucharWDWSplit M).H_clock =
      -(pageWoottersBipartite_to_kucharWDWSplit M).H_system :=
  PageWoottersBipartite.E_clock_eq_neg_E_sys M


/-- The operator Wheeler-DeWitt equation induces a split Kuchař witness. -/
def wheelerDeWitt_to_kucharWDWSplit
    (HR HI : ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0)
    (hWDW : WheelerDeWitt HR HI Ψ) : KucharWDWSplit :=
  { H_clock := HR
    H_system := HI
    constraint := by
      obtain ⟨hR, hI⟩ := wheelerDeWitt_constraints_of_nontrivial_state HR HI Ψ hΨ hWDW
      rw [hR, hI]
      ring }

/-- The induced split witness is automatically timeless. -/
lemma wheelerDeWitt_induces_kuchar_timeless_form
    (HR HI : ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0)
    (hWDW : WheelerDeWitt HR HI Ψ) :
    (wheelerDeWitt_to_kucharWDWSplit HR HI Ψ hΨ hWDW).H_clock =
      -(wheelerDeWitt_to_kucharWDWSplit HR HI Ψ hΨ hWDW).H_system :=
  KucharWDWSplit.clock_eq_neg_system
    (wheelerDeWitt_to_kucharWDWSplit HR HI Ψ hΨ hWDW)

/-- Lusanna ADM WDW is the vacuum ADM scalar constraint plus the imaginary constraint. -/
lemma lusanna_wdw_realizes_kuchar_frozen_formalism
    {d : ℕ} (R3 KdotK HI : ℝ) (K : Matrix (Fin d) (Fin d) ℝ)
    (Ψ : ℂ) (hΨ : Ψ ≠ 0)
    (hWDW : WheelerDeWitt (hamiltonianConstraint R3 KdotK K) HI Ψ) :
    R3 + yorkTime K ^ 2 = KdotK ∧ HI = 0 :=
  (wheelerDeWitt_lusanna R3 KdotK HI K Ψ hΨ).mp hWDW


/--
Concrete evidence that the expanded Kuchař contract is connected to existing
Physlib theorem families, rather than being an isolated accounting layer.
-/
structure PhyslibKucharBridgeLinks : Prop where
  pageWoottersKernel :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H]
      (C : Physlib.QuantumMechanics.RelationalTime.HamiltonianConstraint H),
      C.IsPhysical 0
        ∧ (∀ {Ψ : H}, C.IsPhysical Ψ → ∀ c : ℂ, C.IsPhysical (c • Ψ))
        ∧ (∀ {Ψ Φ : H}, C.IsPhysical Ψ → C.IsPhysical Φ → C.IsPhysical (Ψ + Φ))
        ∧ (∀ Ψ Φ : H, C.IsPhysical Ψ → C.IsPhysical Φ →
            Physlib.QuantumMechanics.RelationalTime.physicalKernelInnerProduct C Ψ Φ =
              inner ℂ Ψ Φ)
  finiteTrace :
    ∀ {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n],
      normTrace (1 : Matrix n n ℂ) = 1
        ∧ (∀ a b : Matrix n n ℂ, normTrace (a * b) = normTrace (b * a))
  pageWoottersBipartite :
    ∀ {d_sys d_clock : Type} [Fintype d_sys] [DecidableEq d_sys]
      [Fintype d_clock] [DecidableEq d_clock]
      (M : PageWoottersBipartite d_sys d_clock),
      M.tauPW = M.t
        ∧ M.E_clock = -M.E_sys
        ∧ Sᵥₙ M.clockMarginal = Sᵥₙ M.sysMarginal
        ∧ 0 ≤ Sᵥₙ M.sysMarginal
        ∧ 0 ≤ Sᵥₙ M.clockMarginal
  diracFirstClass :
    ∀ {n : ℕ} {C₁ C₂ : Matrix (Fin n) (Fin n) ℂ} {a b : ℂ}
      (_h : IsFirstClass C₁ C₂ a b) (O : Matrix (Fin n) (Fin n) ℂ),
      collisionStar C₁ (collisionStar C₂ O) - collisionStar C₂ (collisionStar C₁ O)
        = collisionStar (a • C₁ + b • C₂) O
  diracObservableCommutant :
    ∀ {A : Type*} [Ring A] (𝒞 : Set A),
      {O | DiracObservable 𝒞 O} = commutant 𝒞
  complexConstraintObservable :
    ∀ {n : ℕ} {C_R C_I O : Matrix (Fin n) (Fin n) ℂ},
      collisionStar C_R O = 0 → collisionStar C_I O = 0 →
      collisionStar (complexConstraint C_R C_I) O = 0
  tetradSeparationInvariant :
    ∀ {d : ℕ}
      (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (_hΛ : Λ ∈ LorentzGroup d)
      (x : (Fin 1 ⊕ Fin d) → ℝ),
      properSeparationSq (Λ * E) x = properSeparationSq E x
  reconstructedMetricUnique :
    ∀ {d : ℕ} (E E' : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
      (x : (Fin 1 ⊕ Fin d) → ℝ),
      coordCongruence E minkowskiMatrix = coordCongruence E' minkowskiMatrix →
      properSeparationSq E x = properSeparationSq E' x
  entropicAdmTotalProperTime :
    ∀ {sd : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
      (A : Physlib.SpaceTime.ADMData sd) (lam : SpaceTime sd → ℝ)
      (U : EntropicTimeUnits) (q p : SpaceTime sd)
      (ρ σ : MState d) (x : SpaceTime sd) (dt : ℝ),
      A.admStaticProperTime x dt = geometricInterval q p →
      lam x * dt = entropicProperTimeMetric U ρ σ →
      A.admEntropicProperTime lam x dt = totalProperTimeMetric U q p ρ σ
  entropicGravitySynthesis :
    ∀ {d : ℕ}
      (R3 KdotK HI : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (_hΨ : Ψ ≠ 0)
      (A : Physlib.SpaceTime.ADMData d) (lam : SpaceTime d → ℝ)
      (hLam : ∀ y, 0 ≤ lam y)
      (x : SpaceTime d) (dt O_inf : ℝ),
      (WheelerDeWitt (hamiltonianConstraint R3 KdotK K) HI Ψ
          ↔ (R3 + yorkTime K ^ 2 = KdotK) ∧ HI = 0)
        ∧ A.admEntropicProperTime lam x dt
            = A.admStaticProperTime x dt + lam x * dt
        ∧ Physlib.SpaceTime.EntropicLapseFactor.entropicProperTimeOnADM
            (Physlib.SpaceTime.EntropicLapseFactor.ofEntropyProductionRate A lam hLam) A x dt
            = A.admEntropicProperTime lam x dt
        ∧ (O_inf / A.entropicEffectiveLapse lam x) * A.entropicEffectiveLapse lam x = O_inf
  admMaximalSlicing :
    ∀ (tfSq : ℝ), 0 ≤ tfSq →
      0 ≤ Physlib.QuantumMechanics.ComplexAction.GravLapse.ADMSectionII.momentumQuadratic tfSq 0
  pageWoottersTimeless :
    ∀ {d_sys d_clock : Type} [Fintype d_sys] [DecidableEq d_sys]
      [Fintype d_clock] [DecidableEq d_clock]
      (M : PageWoottersBipartite d_sys d_clock),
      (pageWoottersBipartite_to_kucharWDWSplit M).H_clock =
        -(pageWoottersBipartite_to_kucharWDWSplit M).H_system
  wheelerDeWittNontrivial :
    ∀ (HR HI : ℝ) (Ψ : ℂ), Ψ ≠ 0 → WheelerDeWitt HR HI Ψ → HR = 0 ∧ HI = 0
  entropicProblemOfTime :
    (∀ {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d),
        topologicalEntropicTime ρ ρ = 0)
      ∧ (∀ {d : Type*} [Fintype d] [DecidableEq d]
          (hbar kB T_inf : ℝ) (ρ : MState d),
          metricEntropicTime hbar kB T_inf ρ ρ = ⟨0⟩)
      ∧ (∀ {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : MState d),
          0 ≤ topologicalEntropicTime ρ σ)

/-- Existing Physlib bridge theorems provide concrete evidence for the expanded Kuchař contract. -/
lemma physlib_kuchar_bridge_links : PhyslibKucharBridgeLinks := by
  exact
    { pageWoottersKernel := fun C =>
        Physlib.QuantumMechanics.RelationalTime.hilbertSpace_innerProduct_obligation_discharged C
      finiteTrace := fun {_n} {_} {_} {_} => ⟨normTrace_one, normTrace_cyclic⟩
      pageWoottersBipartite := fun M =>
        ⟨PageWoottersBipartite.tauPW_eq_t M,
          PageWoottersBipartite.E_clock_eq_neg_E_sys M,
          PageWoottersBipartite.marginal_entropies_equal M,
          PageWoottersBipartite.sysMarginal_entropy_nonneg M,
          PageWoottersBipartite.clockMarginal_entropy_nonneg M⟩
      diracFirstClass := fun h O => firstClass_flow_closes h O
      diracObservableCommutant := fun 𝒞 => diracObservable_eq_commutant 𝒞
      complexConstraintObservable := fun hR hI => complexConstraint_dirac_of hR hI
      tetradSeparationInvariant := fun Λ E hΛ x =>
        properSeparationSq_lorentz_gauge hΛ x
      reconstructedMetricUnique := fun E E' x hmetric =>
        properSeparation_unique_of_reconstructed_metric E E' x hmetric
      entropicAdmTotalProperTime := fun A lam U q p ρ σ x dt h_geom h_ent =>
        Physlib.SpaceTime.admEntropicProperTime_eq_totalProperTimeMetric
          A lam U q p ρ σ x dt h_geom h_ent
      entropicGravitySynthesis := fun R3 KdotK HI K Ψ hΨ A lam hLam x dt O_inf =>
        Physlib.QuantumMechanics.ComplexAction.EntropicTime.GravitySynthesis.adm_wdw_entropic_lapse_contract
          R3 KdotK HI K Ψ hΨ A lam hLam x dt O_inf
      admMaximalSlicing := fun tfSq htf =>
        Physlib.QuantumMechanics.ComplexAction.GravLapse.ADMSectionII.momentumQuadratic_maximalSlice_nonneg
          tfSq htf
      pageWoottersTimeless := fun M => pageWoottersBipartite_realizes_kuchar_timeless_form M
      wheelerDeWittNontrivial := fun HR HI Ψ hΨ hWDW =>
        wheelerDeWitt_constraints_of_nontrivial_state HR HI Ψ hΨ hWDW
      entropicProblemOfTime := entropic_problem_of_time_instance }

/--
The expanded Kuchař contract is linked to Physlib bridge families and to the
canonical six-problem open-obligation ledger.
-/
@[zil_claim Kuchar.expandedContractLinkedToPhyslib] lemma kuchar_expanded_contract_linked_to_physlib :
    PhyslibKucharBridgeLinks
      ∧ (∀ p, canonicalKucharStatus p ≠ KucharStatus.solvedInPhyslib)
      ∧ (∀ p, 0 < (canonicalOpenObligations p).length)
      ∧ (∀ p, 0 < (KucharMajorProblem.paperAnchors p).length) :=
  ⟨physlib_kuchar_bridge_links,
    canonicalKucharStatus_none_solved,
    canonicalOpenObligations_nonempty,
    KucharMajorProblem.paperAnchors_nonempty⟩

/-- A compact capability statement for the Kuchař bridge now available in Physlib. -/
@[zil_claim Kuchar.problemOfTimePhyslibCapabilities] lemma kuchar_problem_of_time_physlib_capabilities :
    PhyslibKucharBridgeLinks
    ∧ (∀ p, canonicalKucharStatus p ≠ KucharStatus.solvedInPhyslib)
    ∧ (∀ p, 0 < (canonicalOpenObligations p).length)
    ∧ (∀ p, 0 < (KucharMajorProblem.paperAnchors p).length)
    ∧ (∀ {d_sys d_clock : Type} [Fintype d_sys] [DecidableEq d_sys]
        [Fintype d_clock] [DecidableEq d_clock]
        (M : PageWoottersBipartite d_sys d_clock),
        (pageWoottersBipartite_to_kucharWDWSplit M).H_clock =
          -(pageWoottersBipartite_to_kucharWDWSplit M).H_system)
    ∧ (∀ (HR HI : ℝ) (Ψ : ℂ), Ψ ≠ 0 →
        WheelerDeWitt HR HI Ψ → HR = 0 ∧ HI = 0)
    ∧ (∀ {d : Type*} [Fintype d] [DecidableEq d]
        (hbar kB T_inf : ℝ) (ρ : MState d),
        metricEntropicTime hbar kB T_inf ρ ρ = ⟨0⟩) := by
  exact ⟨physlib_kuchar_bridge_links,
    canonicalKucharStatus_none_solved,
    canonicalOpenObligations_nonempty,
    KucharMajorProblem.paperAnchors_nonempty,
    fun {_ _ _ _ _ _} M => pageWoottersBipartite_realizes_kuchar_timeless_form M,
    fun HR HI Ψ hΨ hWDW => wheelerDeWitt_constraints_of_nontrivial_state HR HI Ψ hΨ hWDW,
    fun {_ _ _} hbar kB T_inf ρ =>
      frozen_LRF_problem_of_time hbar kB T_inf ρ⟩

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.KucharProblemOfTime

end
