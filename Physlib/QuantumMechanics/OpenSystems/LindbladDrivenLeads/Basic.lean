/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Multiplication
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.HilbertSchmidtOperatorSpace
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Data.Matrix.Basis
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Lindblad-driven discretized leads

This file formalizes reusable parts of Schwarz, Goldstein, Dorda, Arrigoni,
Weichselbaum and von Delft, *Lindblad-driven discretized leads for
nonequilibrium steady-state transport in quantum impurity models: Recovering
the continuum limit*, Phys. Rev. B 94, 155142 (2016).

The formalization covers the one-level loss and gain rates, a bounded
finite-dimensional Lindblad generator on the existing Hilbert--Schmidt space,
Lorentzian broadening and the continuum-resolution criterion, and the
level-doubling identities that preserve hybridization while making scalar rate
matrices invariant under unitary basis changes.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Complex
open HilbertSchmidtOperatorSpace
open LownerHeinzTheorem
open scoped Matrix Topology

/-! ## One-level LDDL rates -/

/-- Admissible rate data for one discretized lead level. -/
structure RateData where
  /-- Total Lindblad driving rate. -/
  gamma : ℝ
  /-- Target occupation. -/
  occupation : ℝ
  gamma_pos : 0 < gamma
  occupation_nonneg : 0 ≤ occupation
  occupation_le_one : occupation ≤ 1

/-- Loss rate `λ⁽¹⁾ = γ(1-f)` from Eq. (39). -/
def lossRate (r : RateData) : ℝ :=
  r.gamma * (1 - r.occupation)

/-- Gain rate `λ⁽²⁾ = γf` from Eq. (39). -/
def gainRate (r : RateData) : ℝ :=
  r.gamma * r.occupation

/-- Sum `λ⁽⁺⁾ = λ⁽¹⁾ + λ⁽²⁾`. -/
def totalRate (r : RateData) : ℝ :=
  lossRate r + gainRate r

/-- Difference `λ⁽⁻⁾ = λ⁽¹⁾ - λ⁽²⁾`. -/
def imbalanceRate (r : RateData) : ℝ :=
  lossRate r - gainRate r

@[simp]
theorem lossRate_nonneg (r : RateData) : 0 ≤ lossRate r := by
  exact mul_nonneg r.gamma_pos.le (sub_nonneg.mpr r.occupation_le_one)

@[simp]
theorem gainRate_nonneg (r : RateData) : 0 ≤ gainRate r := by
  exact mul_nonneg r.gamma_pos.le r.occupation_nonneg

/-- Equation (42a), first identity: `λ⁽⁺⁾ = γ`. -/
@[simp]
theorem totalRate_eq_gamma (r : RateData) : totalRate r = r.gamma := by
  simp [totalRate, lossRate, gainRate]
  ring

/-- Equation (42a), second identity: `λ⁽⁻⁾ = γ(1-2f)`. -/
@[simp]
theorem imbalanceRate_eq (r : RateData) :
    imbalanceRate r = r.gamma * (1 - 2 * r.occupation) := by
  simp [imbalanceRate, lossRate, gainRate]
  ring

/-- Right-hand side of the occupation equation (37). -/
def occupationVectorField (r : RateData) (n : ℝ) : ℝ :=
  2 * gainRate r - 2 * totalRate r * n

/-- Equation (37) in relaxation form: `Ṅ = 2γ(f-N)`. -/
theorem occupationVectorField_eq (r : RateData) (n : ℝ) :
    occupationVectorField r n = 2 * r.gamma * (r.occupation - n) := by
  simp [occupationVectorField, gainRate]
  ring

/-- The target occupation is a steady point. -/
@[simp]
theorem occupationVectorField_target (r : RateData) :
    occupationVectorField r r.occupation = 0 := by
  rw [occupationVectorField_eq]
  ring

/-- The target occupation is the unique steady point for positive `γ`. -/
theorem occupationVectorField_eq_zero_iff (r : RateData) (n : ℝ) :
    occupationVectorField r n = 0 ↔ n = r.occupation := by
  rw [occupationVectorField_eq]
  constructor
  · intro h
    have hgamma : (2 * r.gamma) ≠ 0 :=
      mul_ne_zero (by norm_num) r.gamma_pos.ne'
    have hdiff : r.occupation - n = 0 :=
      (mul_eq_zero.mp h).resolve_left hgamma
    exact (sub_eq_zero.mp hdiff).symm
  · rintro rfl
    ring

/-- Equation (38) specialized by Eq. (39): the steady-state ratio is `f`. -/
theorem gainRate_div_totalRate (r : RateData) :
    gainRate r / totalRate r = r.occupation := by
  rw [totalRate_eq_gamma]
  simp [gainRate, r.gamma_pos.ne']

/-- One forward Euler step for the occupation relaxation equation. -/
def occupationEulerStep (r : RateData) (dt n : ℝ) : ℝ :=
  n + dt * occupationVectorField r n

/-- The target occupation is fixed by every Euler step. -/
@[simp]
theorem occupationEulerStep_target (r : RateData) (dt : ℝ) :
    occupationEulerStep r dt r.occupation = r.occupation := by
  simp [occupationEulerStep]

/-- Error propagation for one Euler step. -/
theorem occupationEulerStep_sub_target (r : RateData) (dt n : ℝ) :
    occupationEulerStep r dt n - r.occupation =
      (1 - 2 * dt * r.gamma) * (n - r.occupation) := by
  rw [occupationEulerStep, occupationVectorField_eq]
  ring

/-! ## Finite-dimensional Hilbert--Schmidt Lindblad generators -/

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ]

/-- Hamiltonian commutator part `-i(Hρ-ρH)`. -/
def hamiltonianPartHS (H : L ℋ) : L (HSOp ℋ) :=
  (-Complex.I) • (leftMulHS (ℋ := ℋ) H - rightMulHS (ℋ := ℋ) H)

/-- One GKSL dissipator `2JρJ† - J†Jρ - ρJ†J`. -/
def lindbladDissipatorHS (J : L ℋ) : L (HSOp ℋ) :=
  (2 : ℂ) • (leftMulHS (ℋ := ℋ) J * rightMulHS (ℋ := ℋ) (star J)) -
    leftMulHS (ℋ := ℋ) (star J * J) -
    rightMulHS (ℋ := ℋ) (star J * J)

/-- Weighted dissipator. -/
def weightedDissipatorHS (lambda : ℝ) (J : L ℋ) : L (HSOp ℋ) :=
  (lambda : ℂ) • lindbladDissipatorHS J

/-- Two-channel LDDL generator, corresponding to Eqs. (36) and (40). -/
def lddlGeneratorHS (H Jloss Jgain : L ℋ) (r : RateData) : L (HSOp ℋ) :=
  hamiltonianPartHS H +
    weightedDissipatorHS (lossRate r) Jloss +
    weightedDissipatorHS (gainRate r) Jgain

@[simp]
theorem hamiltonianPartHS_apply (H : L ℋ) (rho : HSOp ℋ) :
    toOp (hamiltonianPartHS H rho) =
      (-Complex.I) • (H * toOp rho - toOp rho * H) := by
  rfl

@[simp]
theorem lindbladDissipatorHS_apply (J : L ℋ) (rho : HSOp ℋ) :
    toOp (lindbladDissipatorHS J rho) =
      (2 : ℂ) • (J * toOp rho * star J) -
        (star J * J) * toOp rho - toOp rho * (star J * J) := by
  change
    (2 : ℂ) • (J * (toOp rho * star J)) -
        (star J * J) * toOp rho - toOp rho * (star J * J) = _
  simp only [mul_assoc]

/-- The generator is bounded because it is a continuous linear map on the
existing Hilbert--Schmidt space. -/
theorem lddlGeneratorHS_continuous (H Jloss Jgain : L ℋ) (r : RateData) :
    Continuous (lddlGeneratorHS H Jloss Jgain r) :=
  (lddlGeneratorHS H Jloss Jgain r).continuous

/-- Exponential evolution generated by the bounded Liouvillian. -/
def lddlEvolutionHS (H Jloss Jgain : L ℋ) (r : RateData) (t : ℝ) :
    L (HSOp ℋ) :=
  NormedSpace.exp ((t : ℂ) • lddlGeneratorHS H Jloss Jgain r)

@[simp]
theorem lddlEvolutionHS_zero (H Jloss Jgain : L ℋ) (r : RateData) :
    lddlEvolutionHS H Jloss Jgain r 0 = 1 := by
  simp [lddlEvolutionHS]

/-! ## One-level Green functions and Lorentzian broadening -/

/-- Unnormalized Lorentz peak `γ / ((ω-ε)²+γ²)`. -/
def lorentzPeak (gamma epsilon omega : ℝ) : ℝ :=
  gamma / ((omega - epsilon) ^ 2 + gamma ^ 2)

/-- Normalized Lorentzian `δγ(ω-ε)` from Eq. (34). -/
def lorentzian (gamma epsilon omega : ℝ) : ℝ :=
  lorentzPeak gamma epsilon omega / Real.pi

/-- Retarded Green function `(ω-ε+iγ)⁻¹`, Eq. (42b). -/
def retardedLeadGreen (gamma epsilon omega : ℝ) : ℂ :=
  (((omega - epsilon : ℝ) : ℂ) + Complex.I * gamma)⁻¹

/-- Keldysh Green function in rate form, Eq. (41b). -/
def keldyshLeadGreen (r : RateData) (epsilon omega : ℝ) : ℂ :=
  (-2 * Complex.I) * (imbalanceRate r : ℂ) /
    (((omega - epsilon) ^ 2 + r.gamma ^ 2 : ℝ) : ℂ)

/-- The Lorentz peak is nonnegative for positive broadening. -/
theorem lorentzPeak_nonneg (r : RateData) (epsilon omega : ℝ) :
    0 ≤ lorentzPeak r.gamma epsilon omega := by
  apply div_nonneg r.gamma_pos.le
  positivity

/-- The normalized Lorentzian is nonnegative. -/
theorem lorentzian_nonneg (r : RateData) (epsilon omega : ℝ) :
    0 ≤ lorentzian r.gamma epsilon omega := by
  exact div_nonneg (lorentzPeak_nonneg r epsilon omega) Real.pi_pos.le

/-- Equation (42c) written using `λ⁽⁻⁾ = γ(1-2f)`. -/
theorem keldyshLeadGreen_eq (r : RateData) (epsilon omega : ℝ) :
    keldyshLeadGreen r epsilon omega =
      (-2 * Complex.I) * ((r.gamma * (1 - 2 * r.occupation) : ℝ) : ℂ) /
        (((omega - epsilon) ^ 2 + r.gamma ^ 2 : ℝ) : ℂ) := by
  rw [keldyshLeadGreen, imbalanceRate_eq]

/-- The one-level denominator is positive for positive broadening. -/
theorem greenDenominator_pos (r : RateData) (epsilon omega : ℝ) :
    0 < (omega - epsilon) ^ 2 + r.gamma ^ 2 := by
  exact add_pos_of_nonneg_of_pos (sq_nonneg (omega - epsilon))
    (sq_pos_of_pos r.gamma_pos)

/-! ## Continuum-resolution criterion -/

/-- Discretization and broadening scales for one lead interval. -/
structure ResolutionData where
  /-- Level spacing or represented interval width. -/
  delta : ℝ
  /-- Lindblad broadening. -/
  gamma : ℝ
  /-- Smallest physical scale that must remain resolved. -/
  physicalScale : ℝ
  delta_nonneg : 0 ≤ delta
  gamma_pos : 0 < gamma
  gamma_lt_physicalScale : gamma < physicalScale

/-- Criterion (45): overlapping peaks that remain below the physical scale. -/
def IsContinuumResolved (s : ResolutionData) : Prop :=
  s.delta ≤ s.gamma ∧ s.gamma < s.physicalScale

/-- Matched broadening `γ=δ` satisfies the criterion when the spacing resolves
the physical scale. -/
theorem matchedBroadening_resolved (delta physicalScale : ℝ)
    (hdelta : 0 < delta) (hscale : delta < physicalScale) :
    IsContinuumResolved
      { delta := delta
        gamma := delta
        physicalScale := physicalScale
        delta_nonneg := hdelta.le
        gamma_pos := hdelta
        gamma_lt_physicalScale := hscale } := by
  exact ⟨le_rfl, hscale⟩

/-! ## Dominated convergence bridge for continuum observables -/

/-- A continuum observable obtained by integrating a complex-valued spectral
integrand against a measure. -/
def continuumObservable {X : Type*} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X) (f : X → ℂ) : ℂ :=
  ∫ x, f x ∂mu

/-- Once discretized spectral integrands converge almost everywhere and admit
one integrable dominating function, their observable integrals converge to the
continuum observable. -/
theorem continuumObservable_tendsto_of_dominated_convergence
    {X : Type*} [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    {F : ℕ → X → ℂ} {f : X → ℂ} (bound : X → ℝ)
    (hF_measurable : ∀ n, MeasureTheory.AEStronglyMeasurable (F n) mu)
    (hbound_integrable : MeasureTheory.Integrable bound mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖F n x‖ ≤ bound x)
    (hlimit : ∀ᵐ x ∂mu,
      Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (f x))) :
    Filter.Tendsto (fun n => continuumObservable mu (F n)) Filter.atTop
      (𝓝 (continuumObservable mu f)) := by
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hF_measurable hbound_integrable hbound hlimit

/-- Spectral integrand used for current and occupation observables. The first
factor is the broadened hybridization, while the other two encode the Fermi
window and impurity spectral response. -/
def transportIntegrand {X : Type*} (hybridization window spectral : X → ℂ)
    (x : X) : ℂ :=
  hybridization x * window x * spectral x

/-- If the discretized hybridization converges pointwise almost everywhere,
then the corresponding transport integrands converge pointwise. -/
theorem transportIntegrand_tendsto_of_hybridization
    {X : Type*} {hybridization : ℕ → X → ℂ} {continuum window spectral : X → ℂ}
    {x : X}
    (hhybridization : Filter.Tendsto (fun n => hybridization n x) Filter.atTop
      (𝓝 (continuum x))) :
    Filter.Tendsto
      (fun n => transportIntegrand (hybridization n) window spectral x)
      Filter.atTop
      (𝓝 (transportIntegrand continuum window spectral x)) := by
  exact (hhybridization.mul_const (window x)).mul_const (spectral x)

/-- Convergence of the hybridization factor, together with one integrable
bound for the complete transport integrands, implies convergence of the LDDL
current or occupation integral to its continuum expression. -/
theorem transportObservable_tendsto_of_hybridization
    {X : Type*} [MeasurableSpace X] {mu : MeasureTheory.Measure X}
    {hybridization : ℕ → X → ℂ} {continuum window spectral : X → ℂ}
    (bound : X → ℝ)
    (hmeasurable : ∀ n, MeasureTheory.AEStronglyMeasurable
      (transportIntegrand (hybridization n) window spectral) mu)
    (hbound_integrable : MeasureTheory.Integrable bound mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu,
      ‖transportIntegrand (hybridization n) window spectral x‖ ≤ bound x)
    (hhybridization : ∀ᵐ x ∂mu,
      Filter.Tendsto (fun n => hybridization n x) Filter.atTop
        (𝓝 (continuum x))) :
    Filter.Tendsto
      (fun n => continuumObservable mu
        (transportIntegrand (hybridization n) window spectral))
      Filter.atTop
      (𝓝 (continuumObservable mu
        (transportIntegrand continuum window spectral))) := by
  apply continuumObservable_tendsto_of_dominated_convergence
    bound hmeasurable hbound_integrable hbound
  filter_upwards [hhybridization] with x hx
  exact transportIntegrand_tendsto_of_hybridization hx

/-! ## Level doubling and local Lindblad rates -/

/-- The two auxiliary channels used by the local level-doubling setup. -/
abbrev AuxiliaryChannel := Fin 2

/-- Squared coupling weight: `1-f` for the empty channel and `f` for the filled
channel. -/
def couplingWeightSq (f : ℝ) (eta : AuxiliaryChannel) : ℝ :=
  if eta = 0 then 1 - f else f

/-- Coupling-amplitude weight from Eq. (65). -/
def couplingWeight (f : ℝ) (eta : AuxiliaryChannel) : ℝ :=
  Real.sqrt (couplingWeightSq f eta)

/-- Doubled coupling `ṽη`. -/
def doubledCoupling (v : ℂ) (f : ℝ) (eta : AuxiliaryChannel) : ℂ :=
  (couplingWeight f eta : ℂ) * v

/-- Local `λ̃⁽⁺⁾`, Eq. (68a). -/
def localRatePlus (gamma : ℝ) (_eta : AuxiliaryChannel) : ℝ :=
  gamma

/-- Local `λ̃⁽⁻⁾`, Eq. (68b). -/
def localRateMinus (gamma : ℝ) (eta : AuxiliaryChannel) : ℝ :=
  if eta = 0 then gamma else -gamma

/-- The squared level-doubling weights sum to one. -/
theorem sum_couplingWeightSq (f : ℝ) :
    ∑ eta : AuxiliaryChannel, couplingWeightSq f eta = 1 := by
  simp [couplingWeightSq]

/-- The amplitude weights square to the prescribed coupling weights. -/
theorem couplingWeight_sq (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (eta : AuxiliaryChannel) :
    couplingWeight f eta ^ 2 = couplingWeightSq f eta := by
  by_cases h : eta = 0
  · simp [couplingWeight, couplingWeightSq, h, Real.sq_sqrt (sub_nonneg.mpr hf1)]
  · simp [couplingWeight, couplingWeightSq, h, Real.sq_sqrt hf0]

/-- Equation (70a): level doubling preserves total coupling weight. -/
theorem sum_doubledCoupling_normSq (v : ℂ) (f : ℝ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    ∑ eta : AuxiliaryChannel, Complex.normSq (doubledCoupling v f eta) =
      Complex.normSq v := by
  have hnorm (eta : AuxiliaryChannel) :
      Complex.normSq (doubledCoupling v f eta) =
        couplingWeightSq f eta * Complex.normSq v := by
    rw [doubledCoupling, Complex.normSq_mul, Complex.normSq_ofReal,
      ← pow_two, couplingWeight_sq f hf0 hf1]
  simp_rw [hnorm]
  rw [← Finset.sum_mul]
  rw [sum_couplingWeightSq, one_mul]

/-- Equation (70b): signed doubled weights reproduce `γ(1-2f)`. -/
theorem sum_localRateMinus_mul_weightSq (gamma f : ℝ) :
    ∑ eta : AuxiliaryChannel,
      localRateMinus gamma eta * couplingWeightSq f eta =
        gamma * (1 - 2 * f) := by
  simp [localRateMinus, couplingWeightSq]
  ring

/-- Signed hybridization identity from Eqs. (65), (68b), and (70b). -/
theorem sum_localRateMinus_mul_doubledNormSq (gamma : ℝ) (v : ℂ) (f : ℝ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    ∑ eta : AuxiliaryChannel,
      localRateMinus gamma eta * Complex.normSq (doubledCoupling v f eta) =
        gamma * (1 - 2 * f) * Complex.normSq v := by
  have hnorm (eta : AuxiliaryChannel) :
      Complex.normSq (doubledCoupling v f eta) =
        couplingWeightSq f eta * Complex.normSq v := by
    rw [doubledCoupling, Complex.normSq_mul, Complex.normSq_ofReal,
      ← pow_two, couplingWeight_sq f hf0 hf1]
  simp_rw [hnorm, ← mul_assoc]
  rw [← Finset.sum_mul]
  rw [sum_localRateMinus_mul_weightSq]

/-- A scalar rate matrix is invariant under a unitary change of basis. -/
theorem scalarRateMatrix_unitaryInvariant {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (gamma : ℂ) :
    Uᴴ * (gamma • (1 : Matrix n n ℂ)) * U = gamma • 1 := by
  calc
    Uᴴ * (gamma • (1 : Matrix n n ℂ)) * U =
        gamma • (Uᴴ * (1 : Matrix n n ℂ) * U) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = gamma • (Uᴴ * U) := by simp
    _ = gamma • 1 := by rw [hU]

/-! ## Reused continuum pointwise operators -/

/-- Existing maximal-domain pointwise multiplication on doubled space. -/
def doubledSpacePointwiseOperator {d : ℕ} (f : Space (d + d) → ℂ) :
    SpaceDHilbertSpace (d + d) →ₗ.[ℂ] SpaceDHilbertSpace (d + d) :=
  SpaceDHilbertSpace.mulOperator MeasureTheory.volume f

/-- The existing pointwise operator has dense domain. -/
theorem doubledSpacePointwiseOperator_hasDenseDomain {d : ℕ}
    {f : Space (d + d) → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f) :
    (doubledSpacePointwiseOperator f).HasDenseDomain := by
  simpa [doubledSpacePointwiseOperator] using
    (SpaceDHilbertSpace.mulOperator_hasDenseDomain hf)

/-- The existing pointwise continuum multiplication operator is closable. -/
theorem doubledSpacePointwiseOperator_isClosable {d : ℕ}
    {f : Space (d + d) → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f) :
    (doubledSpacePointwiseOperator f).IsClosable := by
  simpa [doubledSpacePointwiseOperator] using
    (SpaceDHilbertSpace.mulOperator_isClosable hf)

end LindbladDrivenLeads
end QuantumMechanics
