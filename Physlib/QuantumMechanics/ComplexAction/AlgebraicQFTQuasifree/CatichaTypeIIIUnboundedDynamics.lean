/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
meta import Zil

/-!
# Caticha continuum generators on type-III local nets

This module joins the two continuum upgrades without duplicating either one.  A measurable real
mode-diagonal Ipek--Caticha generator supplies the self-adjoint unbounded operator; a concrete
type-III local net supplies the observable algebras.  The remaining localization datum is precisely
operator affiliation, stated explicitly for each region.

The second half adds the missing information-dynamics interface without pretending that the finite
diagonal entropy is Araki entropy.  A `TypeIIIArakiPositiveTimeDynamics` carries a regionwise
extended-real relative entropy, a positive-time state semigroup, and the operator-algebraic
data-processing theorem as explicit analytic data.  From those fields the module proves:

* relative entropy to a stationary reference is antitone;
* finite interval entropy production is nonnegative and obeys an exact cocycle;
* the associated complex-action damping amplitude is a Lyapunov monotone whenever the initial
  Araki relative entropy is finite.

The final theorem packages those information laws with the already constructed standard Hadamard
vacuum and self-adjoint affiliated Caticha generator.  It is a genuine type-III carrier theorem, but
construction of Araki relative entropy and proof of its data-processing property for a concrete
model remain the supplied microlocal/operator-algebraic obligations.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics

open MeasureTheory
open ComplexConjugate
open LinearPMap
open QuantumMechanics.SpaceDHilbertSpace
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

variable {ι : Type*} [Preorder ι]

/-- **Unbounded continuum/type-III Caticha dynamics.**  Regional real measurable symbols determine
maximal self-adjoint continuum multiplication generators.  Given their affiliation with the supplied
local type-III algebras, they assemble into the common type-III unbounded-dynamics carrier. -/
noncomputable def catichaTypeIIIUnboundedDynamics {d : ℕ}
    (N : ConcreteTypeIIINet (QuantumMechanics.SpaceDHilbertSpace d) ι)
    (lapse shift : ι → ℝ) (hperp hi : ι → Space d → ℂ)
    (hperpMeas : ∀ O, AEStronglyMeasurable (hperp O))
    (hiMeas : ∀ O, AEStronglyMeasurable (hi O))
    (hperpReal : ∀ O, conj ∘ hperp O = hperp O)
    (hiReal : ∀ O, conj ∘ hi O = hi O)
    (haffiliated : ∀ O,
      IsAffiliated
        (continuumMultiplicationGenerator (lapse O) (shift O) (hperp O) (hi O))
        (N.alg O)) :
    TypeIIIUnboundedDynamics N where
  generator O :=
    continuumMultiplicationGenerator (lapse O) (shift O) (hperp O) (hi O)
  isUnbounded O :=
    continuumMultiplicationGenerator_isUnbounded (lapse O) (shift O) (hperp O) (hi O)
      (hperpMeas O) (hiMeas O)
  isSelfAdjoint O :=
    continuumMultiplicationGenerator_isSelfAdjoint (lapse O) (shift O) (hperp O) (hi O)
      (hperpMeas O) (hiMeas O) (hperpReal O) (hiReal O)
  affiliated := haffiliated

/-- Every regional generator constructed by `catichaTypeIIIUnboundedDynamics` has real spectrum. -/
theorem catichaTypeIIIUnboundedDynamics_spectrum_real {d : ℕ}
    (N : ConcreteTypeIIINet (QuantumMechanics.SpaceDHilbertSpace d) ι)
    (lapse shift : ι → ℝ) (hperp hi : ι → Space d → ℂ)
    (hperpMeas : ∀ O, AEStronglyMeasurable (hperp O))
    (hiMeas : ∀ O, AEStronglyMeasurable (hi O))
    (hperpReal : ∀ O, conj ∘ hperp O = hperp O)
    (hiReal : ∀ O, conj ∘ hi O = hi O)
    (haffiliated : ∀ O,
      IsAffiliated
        (continuumMultiplicationGenerator (lapse O) (shift O) (hperp O) (hi O))
        (N.alg O)) (O : ι) :
    σ ((catichaTypeIIIUnboundedDynamics N lapse shift hperp hi hperpMeas hiMeas
      hperpReal hiReal haffiliated).generator O) ⊆ Set.range Complex.ofReal :=
  TypeIIIUnboundedDynamics.spectrum_real
    (catichaTypeIIIUnboundedDynamics N lapse shift hperp hi hperpMeas hiMeas
      hperpReal hiReal haffiliated) O

/-! ## B. Regionwise Araki information dynamics -/

variable {H region : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Preorder region]

/-- Positive-time information dynamics on the normal-state carrier of a concrete type-III local
net.  `relativeEntropy` is extended-real, as genuine Araki relative entropy may be infinite.
`dataProcessing` is deliberately a field: the structure does not manufacture operator relative
entropy from the finite diagonal formula. -/
structure TypeIIIArakiPositiveTimeDynamics
    (N : ConcreteTypeIIINet H region) (State : region → Type*) where
  /-- Regionwise Araki relative entropy of local states. -/
  relativeEntropy : ∀ O, State O → State O → ENNReal
  /-- Positive-time evolution of local states. -/
  evolve : ∀ O, NNReal → State O → State O
  /-- Zero elapsed time acts identically. -/
  evolve_zero : ∀ (O : region) (rho : State O), evolve O 0 rho = rho
  /-- Positive-time evolution composes additively. -/
  evolve_add : ∀ (O : region) (s t : NNReal) (rho : State O),
    evolve O (s + t) rho = evolve O s (evolve O t rho)
  /-- Operator-algebraic data processing for every local positive-time channel. -/
  dataProcessing : ∀ (O : region) (t : NNReal) (rho omega : State O),
    relativeEntropy O (evolve O t rho) (evolve O t omega) ≤ relativeEntropy O rho omega
  /-- Araki relative entropy vanishes when both local states agree. -/
  relativeEntropy_self : ∀ (O : region) (omega : State O),
    relativeEntropy O omega omega = 0

namespace TypeIIIArakiPositiveTimeDynamics

variable {N : ConcreteTypeIIINet H region} {State : region → Type*}
variable (S : TypeIIIArakiPositiveTimeDynamics N State)

/-- The local state reached after nonnegative time `t`. -/
def stateAt (O : region) (rho : State O) (t : NNReal) : State O :=
  S.evolve O t rho

/-- A local reference state is stationary when the regional semigroup fixes it. -/
def IsFixedReferenceAt (O : region) (omega : State O) : Prop :=
  ∀ t, S.stateAt O omega t = omega

/-- The type-III state evolution starts at the supplied state. -/
@[simp] lemma stateAt_zero (O : region) (rho : State O) :
    S.stateAt O rho 0 = rho :=
  S.evolve_zero O rho

/-- The semigroup law transported to regional state orbits. -/
lemma stateAt_add (O : region) (rho : State O) (s t : NNReal) :
    S.stateAt O rho (s + t) = S.stateAt O (S.stateAt O rho t) s :=
  S.evolve_add O s t rho

/-- Applying the same positive-time channel to a state and a stationary reference cannot increase
their local Araki relative entropy. -/
lemma relativeEntropy_add_right_le (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega) (s t : NNReal) :
    S.relativeEntropy O (S.stateAt O rho (s + t)) omega ≤
      S.relativeEntropy O (S.stateAt O rho s) omega := by
  rw [add_comm, S.stateAt_add]
  have h := S.dataProcessing O t (S.stateAt O rho s) omega
  have ht := hfix t
  change S.evolve O t omega = omega at ht
  simpa [stateAt, ht] using h

/-- **Type-III Araki H-theorem interface.** Relative entropy to a stationary local reference is
antitone along positive-time evolution.  The conclusion is derived from the semigroup law and the
supplied operator data-processing theorem, not from a finite trace formula. -/
theorem relativeEntropy_antitone (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega) :
    Antitone (fun t => S.relativeEntropy O (S.stateAt O rho t) omega) := by
  intro s t hst
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  exact S.relativeEntropy_add_right_le O rho omega hfix s u

/-- The real entropic clock remaining at local time `t`, obtained from finite Araki relative
entropy by an explicit `ENNReal.toReal` conversion. -/
noncomputable def remainingArakiClockAt
    (γ : ℝ) (O : region) (rho omega : State O) (t : NNReal) : ℝ :=
  γ * (S.relativeEntropy O (S.stateAt O rho t) omega).toReal

/-- Finite initial Araki relative entropy remains finite along the positive-time orbit. -/
lemma relativeEntropy_stateAt_ne_top (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤) (t : NNReal) :
    S.relativeEntropy O (S.stateAt O rho t) omega ≠ ⊤ := by
  apply ne_top_of_le_ne_top hfin
  have hzero : (0 : NNReal) ≤ t := bot_le
  simpa using S.relativeEntropy_antitone O rho omega hfix hzero

/-- The finite real Araki clock is antitone for nonnegative calibration. -/
theorem remainingArakiClockAt_antitone
    (γ : ℝ) (hγ : 0 ≤ γ) (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤) :
    Antitone (S.remainingArakiClockAt γ O rho omega) := by
  intro s t hst
  unfold remainingArakiClockAt
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono
      (S.relativeEntropy_stateAt_ne_top O rho omega hfix hfin s)
      (S.relativeEntropy_antitone O rho omega hfix hst)) hγ

/-- Real entropy produced on an ordered local time interval. -/
noncomputable def intervalArakiProduction
    (γ : ℝ) (O : region) (rho omega : State O) (s t : NNReal) : ℝ :=
  S.remainingArakiClockAt γ O rho omega s - S.remainingArakiClockAt γ O rho omega t

/-- Forward local intervals have nonnegative Araki entropy production. -/
theorem intervalArakiProduction_nonneg
    (γ : ℝ) (hγ : 0 ≤ γ) (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤)
    {s t : NNReal} (hst : s ≤ t) :
    0 ≤ S.intervalArakiProduction γ O rho omega s t :=
  sub_nonneg.mpr (S.remainingArakiClockAt_antitone γ hγ O rho omega hfix hfin hst)

/-- Interval production plus final distinguishability equals initial distinguishability. -/
lemma intervalArakiProduction_add_residual_eq
    (γ : ℝ) (O : region) (rho omega : State O) (s t : NNReal) :
    S.intervalArakiProduction γ O rho omega s t +
        S.remainingArakiClockAt γ O rho omega t =
      S.remainingArakiClockAt γ O rho omega s := by
  unfold intervalArakiProduction
  ring

/-- **Local Araki production cocycle.** Production is additive over adjacent intervals. -/
theorem intervalArakiProduction_cocycle
    (γ : ℝ) (O : region) (rho omega : State O) (s t u : NNReal) :
    S.intervalArakiProduction γ O rho omega s t +
        S.intervalArakiProduction γ O rho omega t u =
      S.intervalArakiProduction γ O rho omega s u := by
  unfold intervalArakiProduction
  ring

/-! ## C. Type-III entropic clock as complex-action damping -/

/-- The master complex-action weight whose imaginary action is the finite local Araki clock. -/
noncomputable def remainingArakiWeightAt
    (S_R ħ γ : ℝ) (O : region) (rho omega : State O) (t : NNReal) : ℂ :=
  complexActionPathIntegralWeight S_R
    (ħ * S.remainingArakiClockAt γ O rho omega t) ħ

/-- The local type-III information clock controls the master-weight modulus exactly. -/
lemma remainingArakiWeightAt_norm
    (S_R ħ γ : ℝ) (hħ : ħ ≠ 0)
    (O : region) (rho omega : State O) (t : NNReal) :
    ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖ =
      Real.exp (-S.remainingArakiClockAt γ O rho omega t) := by
  rw [remainingArakiWeightAt, master_modulus_is_kuiken, kuikenWeight,
    mul_div_cancel_left₀ _ hħ]

/-- **Type-III complex-action Lyapunov law.** As Araki distinguishability is lost, the modulus of
the associated remaining-clock amplitude can only recover. -/
theorem remainingArakiWeightAt_norm_monotone
    (S_R ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤) :
    Monotone (fun t => ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖) := by
  intro s t hst
  change ‖S.remainingArakiWeightAt S_R ħ γ O rho omega s‖ ≤
    ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖
  rw [S.remainingArakiWeightAt_norm S_R ħ γ hħ O rho omega s,
    S.remainingArakiWeightAt_norm S_R ħ γ hħ O rho omega t,
    Real.exp_le_exp]
  exact neg_le_neg (S.remainingArakiClockAt_antitone γ hγ O rho omega hfix hfin hst)

end TypeIIIArakiPositiveTimeDynamics

/-! ## D. Local covariance under region restriction -/

/-- Region-restriction data for a type-III Araki positive-time dynamics.  Restriction follows the
isotony order of the concrete local net, composes on nested regions, commutes with positive-time
evolution, and satisfies Araki data processing. -/
structure TypeIIIArakiRestrictionData
    {N : ConcreteTypeIIINet H region} {State : region → Type*}
    (S : TypeIIIArakiPositiveTimeDynamics N State) where
  /-- Restriction of a state on a larger region to a nested smaller region. -/
  restrictState : ∀ {O₁ O₂ : region}, O₁ ≤ O₂ → State O₂ → State O₁
  /-- Restriction along the reflexive inclusion is the identity. -/
  restrict_refl : ∀ (O : region) (rho : State O),
    restrictState (le_refl O) rho = rho
  /-- Restrictions compose on chains of nested regions. -/
  restrict_trans : ∀ {O₁ O₂ O₃ : region}
    (h₁₂ : O₁ ≤ O₂) (h₂₃ : O₂ ≤ O₃) (rho : State O₃),
    restrictState h₁₂ (restrictState h₂₃ rho) =
      restrictState (h₁₂.trans h₂₃) rho
  /-- Region restriction intertwines the local positive-time evolutions. -/
  evolve_restrict : ∀ {O₁ O₂ : region} (h : O₁ ≤ O₂)
    (t : NNReal) (rho : State O₂),
    S.evolve O₁ t (restrictState h rho) = restrictState h (S.evolve O₂ t rho)
  /-- Araki relative entropy cannot increase under restriction to a smaller region. -/
  relativeEntropy_restrict_le : ∀ {O₁ O₂ : region} (h : O₁ ≤ O₂)
    (rho omega : State O₂),
    S.relativeEntropy O₁ (restrictState h rho) (restrictState h omega) ≤
      S.relativeEntropy O₂ rho omega

namespace TypeIIIArakiRestrictionData

variable {N : ConcreteTypeIIINet H region} {State : region → Type*}
variable {S : TypeIIIArakiPositiveTimeDynamics N State}
variable (R : TypeIIIArakiRestrictionData S)

/-- A stationary state on a larger region restricts to a stationary state on every nested
subregion. -/
lemma restrict_fixedReferenceAt {O₁ O₂ : region} (h : O₁ ≤ O₂)
    (omega : State O₂) (hfix : S.IsFixedReferenceAt O₂ omega) :
    S.IsFixedReferenceAt O₁ (R.restrictState h omega) := by
  intro t
  unfold TypeIIIArakiPositiveTimeDynamics.stateAt
  rw [R.evolve_restrict h t omega]
  have ht := hfix t
  change S.evolve O₂ t omega = omega at ht
  rw [ht]

/-- **Local-covariant Araki clock.** Restricting a finite-entropy state/reference pair to a nested
region cannot increase its remaining entropic clock at any positive time. -/
theorem remainingArakiClockAt_restrict_le
    {O₁ O₂ : region} (h : O₁ ≤ O₂)
    (γ : ℝ) (hγ : 0 ≤ γ) (rho omega : State O₂)
    (hfix : S.IsFixedReferenceAt O₂ omega)
    (hfin : S.relativeEntropy O₂ rho omega ≠ ⊤) (t : NNReal) :
    S.remainingArakiClockAt γ O₁
        (R.restrictState h rho) (R.restrictState h omega) t ≤
      S.remainingArakiClockAt γ O₂ rho omega t := by
  unfold TypeIIIArakiPositiveTimeDynamics.remainingArakiClockAt
  unfold TypeIIIArakiPositiveTimeDynamics.stateAt
  rw [R.evolve_restrict h t rho]
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono
      (S.relativeEntropy_stateAt_ne_top O₂ rho omega hfix hfin t)
      (R.relativeEntropy_restrict_le h (S.evolve O₂ t rho) omega)) hγ

/-- The complex-action modulus on a larger region is bounded above by the modulus obtained after
restriction, because restriction discards Araki distinguishability. -/
theorem remainingArakiWeightAt_norm_restrict_mono
    {O₁ O₂ : region} (h : O₁ ≤ O₂)
    (S_Rlarge S_Rsmall ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (rho omega : State O₂)
    (hfix : S.IsFixedReferenceAt O₂ omega)
    (hfin : S.relativeEntropy O₂ rho omega ≠ ⊤) (t : NNReal) :
    ‖S.remainingArakiWeightAt S_Rlarge ħ γ O₂ rho omega t‖ ≤
      ‖S.remainingArakiWeightAt S_Rsmall ħ γ O₁
        (R.restrictState h rho) (R.restrictState h omega) t‖ := by
  rw [S.remainingArakiWeightAt_norm S_Rlarge ħ γ hħ O₂ rho omega t,
    S.remainingArakiWeightAt_norm S_Rsmall ħ γ hħ O₁
      (R.restrictState h rho) (R.restrictState h omega) t,
    Real.exp_le_exp]
  exact neg_le_neg (R.remainingArakiClockAt_restrict_le h γ hγ rho omega hfix hfin t)

/-- The existing quasifree state-isotony identity and the new Araki restriction inequality hold on
one inclusion map.  This is the direct bridge from two-point covariance to the local information
clock. -/
theorem quasifree_araki_local_covariance_chain
    {O₁ O₂ : region} (hO : O₁ ≤ O₂)
    {T : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {s₁ s₂ : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ}
    (hT : IsTwoPointCovariant T s₁ s₂) (f : Fin 2 → ℝ)
    (rho omega : State O₂) :
    quasifreeWeight s₂ (T f) = quasifreeWeight s₁ f ∧
      S.relativeEntropy O₁ (R.restrictState hO rho) (R.restrictState hO omega) ≤
        S.relativeEntropy O₂ rho omega :=
  ⟨quasifree_state_covariant hT f, R.relativeEntropy_restrict_le hO rho omega⟩

end TypeIIIArakiRestrictionData

/-! ## E. Differential Spohn rate and quantitative relaxation -/

namespace TypeIIIArakiPositiveTimeDynamics

variable {N : ConcreteTypeIIINet H region} {State : region → Type*}
variable (S : TypeIIIArakiPositiveTimeDynamics N State)

/-- A right Araki/Spohn production rate is the positive-time limit of interval production per unit
time.  Existence is an explicit differentiability obligation. -/
def HasRightArakiProductionRate
    (γ : ℝ) (O : region) (rho omega : State O) (rate : ℝ) : Prop :=
  Filter.Tendsto
    (fun t : NNReal => (t : ℝ)⁻¹ *
      S.intervalArakiProduction γ O rho omega 0 t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds rate)

/-- A stationary reference used as both state and reference has a constructed zero right
Araki-production rate. -/
theorem fixedReference_hasRightArakiProductionRate_zero
    (γ : ℝ) (O : region) (omega : State O)
    (hfix : S.IsFixedReferenceAt O omega) :
    S.HasRightArakiProductionRate γ O omega omega 0 := by
  have heq :
      (fun t : NNReal => (t : ℝ)⁻¹ *
        S.intervalArakiProduction γ O omega omega 0 t) = fun _ => 0 := by
    funext t
    simp only [intervalArakiProduction, remainingArakiClockAt]
    rw [hfix 0, hfix t, S.relativeEntropy_self O omega]
    simp
  rw [HasRightArakiProductionRate, heq]
  exact tendsto_const_nhds

/-- **Differential type-III H-theorem.** Every existing right Araki production rate is
nonnegative, because it is the limit of nonnegative finite-interval productions. -/
theorem rightArakiProductionRate_nonneg
    (γ : ℝ) (hγ : 0 ≤ γ) (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤)
    (rate : ℝ) (hrate : S.HasRightArakiProductionRate γ O rho omega rate) :
    0 ≤ rate := by
  apply ge_of_tendsto hrate
  filter_upwards [] with t
  exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg t))
    (S.intervalArakiProduction_nonneg γ hγ O rho omega hfix hfin bot_le)

/-- Right Araki/Spohn production based at an arbitrary positive time `s`. -/
def HasRightArakiProductionRateAt
    (γ : ℝ) (O : region) (rho omega : State O) (s : NNReal) (rate : ℝ) : Prop :=
  Filter.Tendsto
    (fun t : NNReal => (t : ℝ)⁻¹ *
      S.intervalArakiProduction γ O rho omega
        s (s + t))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds rate)

/-- **Shifted differential type-III H-theorem.** Every existing right production rate based at an
arbitrary nonnegative time is nonnegative. -/
theorem rightArakiProductionRateAt_nonneg
    (γ : ℝ) (hγ : 0 ≤ γ) (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤)
    (s : NNReal) (rate : ℝ)
    (hrate : S.HasRightArakiProductionRateAt γ O rho omega s rate) :
    0 ≤ rate := by
  apply ge_of_tendsto hrate
  filter_upwards [] with t
  exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg t))
    (S.intervalArakiProduction_nonneg γ hγ O rho omega hfix hfin
      (le_add_right (le_refl s)))

/-- An explicit exponential Araki-clock contraction estimate.  This is where a concrete model
supplies detailed balance, a spectral gap, or a logarithmic-Sobolev inequality. -/
def HasExponentialArakiClockContraction
    (rateConst γ : ℝ) (O : region) (rho omega : State O) : Prop :=
  ∀ t : NNReal,
    S.remainingArakiClockAt γ O rho omega t ≤
      Real.exp (-rateConst * (t : ℝ)) * S.remainingArakiClockAt γ O rho omega 0

/-- The real remaining Araki clock is nonnegative for nonnegative calibration. -/
lemma remainingArakiClockAt_nonneg
    (γ : ℝ) (hγ : 0 ≤ γ) (O : region) (rho omega : State O) (t : NNReal) :
    0 ≤ S.remainingArakiClockAt γ O rho omega t :=
  mul_nonneg hγ ENNReal.toReal_nonneg

/-- **Quantitative type-III return-to-equilibrium bound.** An explicit exponential
relative-entropy contraction forces the complex-action modulus into a shrinking lower/upper
bracket whose upper endpoint is unit modulus. -/
theorem remainingArakiWeightAt_quantitative_recovery
    (rateConst S_R ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (O : region) (rho omega : State O)
    (hcontract : S.HasExponentialArakiClockContraction rateConst γ O rho omega)
    (t : NNReal) :
    Real.exp (-(Real.exp (-rateConst * (t : ℝ)) *
        S.remainingArakiClockAt γ O rho omega 0)) ≤
        ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖ ∧
      ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖ ≤ 1 := by
  rw [S.remainingArakiWeightAt_norm S_R ħ γ hħ O rho omega t]
  constructor
  · rw [Real.exp_le_exp]
    exact neg_le_neg (hcontract t)
  · rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (S.remainingArakiClockAt_nonneg γ hγ O rho omega t)

/-- A positive exponential contraction rate makes the scalar decay factor tend to zero along
nonnegative time. -/
lemma exponentialArakiFactor_tendsto_zero
    (rateConst : ℝ) (hrate : 0 < rateConst) :
    Filter.Tendsto (fun t : NNReal => Real.exp (-rateConst * (t : ℝ)))
      Filter.atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hpos : Filter.Tendsto (fun t : NNReal => rateConst * (t : ℝ))
      Filter.atTop Filter.atTop :=
    (NNReal.tendsto_coe_atTop.2 Filter.tendsto_id).const_mul_atTop hrate
  simpa only [Function.comp_def, neg_mul] using
    Filter.tendsto_neg_atTop_atBot.comp hpos

/-- **Actual Araki-clock relaxation.** A positive exponential entropy-contraction estimate forces
the remaining local Araki clock to converge to zero. -/
theorem remainingArakiClockAt_tendsto_zero
    (rateConst γ : ℝ) (hrate : 0 < rateConst) (hγ : 0 ≤ γ)
    (O : region) (rho omega : State O)
    (hcontract : S.HasExponentialArakiClockContraction rateConst γ O rho omega) :
    Filter.Tendsto (S.remainingArakiClockAt γ O rho omega)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun t => S.remainingArakiClockAt_nonneg γ hγ O rho omega t
  · exact hcontract
  · simpa using (exponentialArakiFactor_tendsto_zero rateConst hrate).mul_const
      (S.remainingArakiClockAt γ O rho omega 0)

/-- **Complex-action recovery at equilibrium.** Under positive exponential Araki contraction, the
remaining-clock master-weight modulus converges to one. -/
theorem remainingArakiWeightAt_norm_tendsto_one
    (rateConst S_R ħ γ : ℝ) (hrate : 0 < rateConst)
    (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (O : region) (rho omega : State O)
    (hcontract : S.HasExponentialArakiClockContraction rateConst γ O rho omega) :
    Filter.Tendsto
      (fun t => ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖)
      Filter.atTop (nhds 1) := by
  have hclock := S.remainingArakiClockAt_tendsto_zero
    rateConst γ hrate hγ O rho omega hcontract
  have hneg : Filter.Tendsto
      (fun t => -S.remainingArakiClockAt γ O rho omega t)
      Filter.atTop (nhds 0) := by
    simpa using hclock.neg
  have hexp := (Real.continuous_exp.tendsto 0).comp hneg
  simpa only [Function.comp_def, S.remainingArakiWeightAt_norm S_R ħ γ hħ,
    neg_zero, Real.exp_zero] using hexp

/-- **Type-III return-to-equilibrium package.** At every nonnegative base time, an existing right
Araki production rate is nonnegative; a positive exponential contraction drives the clock to zero
and restores unit complex-action modulus. -/
theorem typeIII_araki_return_to_equilibrium
    (rateConst S_R ħ γ : ℝ) (hrateConst : 0 < rateConst)
    (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤)
    (hcontract : S.HasExponentialArakiClockContraction rateConst γ O rho omega)
    (s : NNReal) (rate : ℝ)
    (hrate : S.HasRightArakiProductionRateAt γ O rho omega s rate) :
    0 ≤ rate ∧
      Filter.Tendsto (S.remainingArakiClockAt γ O rho omega)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun t => ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖)
        Filter.atTop (nhds 1) :=
  ⟨S.rightArakiProductionRateAt_nonneg γ hγ O rho omega hfix hfin s rate hrate,
    S.remainingArakiClockAt_tendsto_zero
      rateConst γ hrateConst hγ O rho omega hcontract,
    S.remainingArakiWeightAt_norm_tendsto_one
      rateConst S_R ħ γ hrateConst hħ hγ O rho omega hcontract⟩

end TypeIIIArakiPositiveTimeDynamics

/-! ## F. Caticha--Hadamard--Araki synthesis -/

variable {𝓕 𝓢 Ξ : Type*}
variable [AddCommGroup 𝓕] [Module ℂ 𝓕] [AddCommGroup 𝓢] [Module ℂ 𝓢]

/-- **Caticha/Hadamard/type-III/Araki synthesis.** On one supplied carrier, the Hadamard vacuum is
standard, the affiliated Caticha generator has real spectrum, local Araki relative entropy is
antitone, forward interval production is nonnegative, and the corresponding complex-action
amplitude is a Lyapunov monotone.  The theorem consumes an operator-algebraic Araki
data-processing datum; it does not infer it from the finite Gibbs model. -/
theorem caticha_hadamard_typeIII_araki_complexAction_chain
    {K : ContinuumCatichaKGData 𝓕 𝓢}
    {Q : ContinuumHadamardTwoPoint 𝓕 Ξ} {transport : Ξ → Ξ}
    {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData K Q transport N)
    (U : TypeIIIUnboundedDynamics N)
    {State : region → Type*} (S : TypeIIIArakiPositiveTimeDynamics N State)
    (S_R ħ γ : ℝ) (hħ : ħ ≠ 0) (hγ : 0 ≤ γ)
    (O : region) (rho omega : State O)
    (hfix : S.IsFixedReferenceAt O omega)
    (hfin : S.relativeEntropy O rho omega ≠ ⊤) :
    ReehSchlieder (N.toConcreteLocalNet.toLocalNet.alg O) A.vacuum ∧
      σ (U.generator O) ⊆ Set.range Complex.ofReal ∧
      Antitone (fun t => S.relativeEntropy O (S.stateAt O rho t) omega) ∧
      (∀ ⦃s t : NNReal⦄, s ≤ t →
        0 ≤ S.intervalArakiProduction γ O rho omega s t) ∧
      Monotone (fun t => ‖S.remainingArakiWeightAt S_R ħ γ O rho omega t‖) :=
  ⟨A.standard_vacuum O, U.spectrum_real O,
    S.relativeEntropy_antitone O rho omega hfix,
    fun {_ _} hst => S.intervalArakiProduction_nonneg γ hγ O rho omega hfix hfin hst,
    S.remainingArakiWeightAt_norm_monotone S_R ħ γ hħ hγ O rho omega hfix hfin⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.catichaTypeIIIUnboundedDynamics_spectrum_real where
  formalizes @ "claim:regional-continuum-caticha-generators-affiliated-with-type-iii-local-algebras-have-real-spectrum",
  requires @ "claim:real-measurable-mode-symbols-and-local-affiliation",
  supported_by @ "paper:ipek-caticha-covariant-entropic-dynamics",
  caveat @ "claim:does-not-classify-a-specific-hadamard-net-as-hyperfinite-type-iii1"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.relativeEntropy_antitone where
  formalizes @ "claim:local-araki-relative-entropy-to-a-stationary-reference-is-antitone-under-positive-time-type-iii-dynamics",
  requires @ "assumption:operator-araki-relative-entropy-and-its-data-processing-theorem-on-the-local-normal-state-carrier",
  supported_by @ "paper:araki-1976-relative-entropy-von-neumann-algebras",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:operator-data-processing-is-explicit-analytic-data-and-is-not-inferred-from-the-finite-diagonal-relative-entropy"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.intervalArakiProduction_cocycle where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.relativeEntropy_antitone",
  formalizes @ "claim:type-iii-araki-entropy-production-is-additive-over-adjacent-positive-time-intervals",
  requires @ "claim:local-araki-relative-entropy-to-a-stationary-reference-is-antitone-under-positive-time-type-iii-dynamics",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.intervalArakiProduction_add_residual_eq",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:exact-telescoping-identity-not-a-differentiable-spohn-rate-or-strict-relaxation-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiWeightAt_norm_monotone where
  formalizes @ "claim:type-iii-araki-information-loss-makes-the-remaining-clock-complex-action-amplitude-a-lyapunov-monotone",
  requires @ "claim:finite-initial-araki-relative-entropy-and-nonnegative-clock-calibration",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:amplitude-law-for-a-supplied-araki-positive-time-dynamics-not-construction-of-a-specific-interacting-aqft-semigroup"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiRestrictionData.quasifree_araki_local_covariance_chain where
  formalizes @ "claim:quasifree-state-isotony-and-araki-relative-entropy-restriction-data-processing-hold-on-one-nested-region-map",
  requires @ "assumption:a-region-restriction-map-intertwining-the-positive-time-dynamics-and-satisfying-operator-araki-data-processing",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony.quasifree_state_covariant",
  supported_by @ "paper:labuschagne-majewski-arxiv-2503-14107-quasi-free-states-and-the-net-of-von-neumann-algebras",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:local-covariance-interface-not-a-construction-of-normal-state-restriction-or-araki-monotonicity-for-a-specific-interacting-net"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.rightArakiProductionRate_nonneg where
  formalizes @ "claim:every-existing-right-araki-spohn-production-rate-is-nonnegative",
  requires @ "claim:finite-initial-araki-relative-entropy-stationary-reference-and-existence-of-the-right-rate-limit",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.intervalArakiProduction_nonneg",
  supported_by @ "paper:spohn-1978-entropy-production",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:sign-of-an-existing-right-limit-not-an-unconditional-differentiability-or-generator-identification-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiWeightAt_quantitative_recovery where
  formalizes @ "claim:an-explicit-exponential-araki-clock-contraction-gives-a-quantitative-complex-action-amplitude-recovery-bracket",
  requires @ "assumption:a-model-specific-detailed-balance-spectral-gap-or-logarithmic-sobolev-contraction-estimate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:conditional-quantitative-bound-not-a-derivation-of-a-logarithmic-sobolev-constant-or-strict-mixing-for-every-type-iii-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.rightArakiProductionRateAt_nonneg where
  formalizes @ "claim:every-existing-right-araki-spohn-production-rate-at-every-nonnegative-base-time-is-nonnegative",
  requires @ "claim:stationary-reference-finite-initial-relative-entropy-and-existence-of-the-shifted-right-rate-limit",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.intervalArakiProduction_nonneg",
  supported_by @ "paper:spohn-1978-entropy-production",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:sign-of-an-existing-shifted-limit-not-unconditional-differentiability-or-identification-with-a-specific-lindblad-generator"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiClockAt_tendsto_zero where
  formalizes @ "claim:positive-exponential-araki-relative-entropy-contraction-drives-the-remaining-clock-to-zero-at-infinite-positive-time",
  requires @ "assumption:a-model-specific-positive-detailed-balance-spectral-gap-or-logarithmic-sobolev-contraction-rate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.exponentialArakiFactor_tendsto_zero",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:conditional-clock-convergence-not-a-proof-that-every-type-iii-positive-time-dynamics-mixes-exponentially"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiWeightAt_norm_tendsto_one where
  formalizes @ "claim:araki-clock-relaxation-restores-unit-modulus-of-the-associated-complex-action-weight",
  requires @ "claim:positive-exponential-araki-clock-contraction-and-nonzero-action-scale",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiClockAt_tendsto_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:convergence-of-the-weight-modulus-only-not-convergence-of-phase-state-or-the-underlying-operator-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.typeIII_araki_return_to_equilibrium where
  formalizes @ "claim:type-iii-araki-return-to-equilibrium-combines-shifted-nonnegative-production-clock-relaxation-and-unit-complex-action-modulus-recovery",
  requires @ "claim:stationary-finite-reference-existing-shifted-rate-and-positive-exponential-clock-contraction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.rightArakiProductionRateAt_nonneg",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiWeightAt_norm_tendsto_one",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:conditional-scalar-return-package-not-a-construction-of-an-interacting-semigroup-a-unique-steady-state-or-operator-norm-convergence"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.caticha_hadamard_typeIII_araki_complexAction_chain where
  formalizes @ "claim:one-continuum-carrier-combines-standard-hadamard-vacuum-affiliated-caticha-generator-araki-h-theorem-and-complex-action-lyapunov-damping",
  requires @ "claim:concrete-type-iii-hadamard-aqft-data-self-adjoint-affiliated-generator-and-araki-data-processing-semigroup",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardTypeIIIAQFTData.standard_vacuum",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.TypeIIIUnboundedDynamics.spectrum_real",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:common-carrier-synthesis-not-a-proof-of-interacting-curved-qed-existence-hyperfinite-iii1-classification-or-strict-return-to-equilibrium"

zil_file_contract physlib.catichaTypeIIIUnboundedDynamics where
  promises "The real measurable continuum Ipek--Caticha multiplication generators assemble as self-adjoint affiliated unbounded dynamics on a supplied type-III local net, with real regional spectra. A separate operator-information carrier derives local Araki relative-entropy antitonicity, nonnegative additive interval production, and complex-action amplitude recovery from an explicit positive-time semigroup and Araki data-processing theorem. Nested-region restriction composes, intertwines evolution and contracts the Araki clock; every existing right production rate, including rates based at arbitrary nonnegative times, is nonnegative. An explicit positive exponential entropy-contraction estimate gives a quantitative amplitude-recovery bracket, forces the remaining clock to zero, and restores unit complex-action modulus at infinite positive time. The synthesis combines these laws with the standard Hadamard vacuum and affiliated Caticha generator."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_isSelfAdjoint",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.IsAffiliated"]
  forbids_substitutes ["finite-dimensional matrix generators",
    "type-III affiliation inferred from self-adjointness alone",
    "finite diagonal relative entropy relabelled as operator Araki relative entropy",
    "operator data processing inferred from type-III classification alone",
    "unconditional differentiability or a differential Spohn rate inferred from interval antitonicity alone",
    "a detailed-balance logarithmic-Sobolev constant inferred without model-specific analytic data",
    "state phase or operator convergence inferred from scalar modulus convergence alone",
    "existence or uniqueness of an equilibrium state inferred from a supplied contraction estimate"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.catichaTypeIIIUnboundedDynamics_spectrum_real,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.relativeEntropy_antitone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.intervalArakiProduction_cocycle,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiWeightAt_norm_monotone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiRestrictionData.quasifree_araki_local_covariance_chain,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.rightArakiProductionRate_nonneg,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiWeightAt_quantitative_recovery,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.rightArakiProductionRateAt_nonneg,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiClockAt_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.remainingArakiWeightAt_norm_tendsto_one,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.TypeIIIArakiPositiveTimeDynamics.typeIII_araki_return_to_equilibrium,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics.caticha_hadamard_typeIII_araki_complexAction_chain]

/- ZIL-END -/
