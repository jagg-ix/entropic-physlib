/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Curvature
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
public import Physlib.QFT.PathIntegral.CurvedMeasurePathIntegral
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic

/-!
# Coordinate Maxwell fields and the complex Einstein bridge

This module provides the coordinate-calculus Maxwell kernel and connects it to
the existing momentum-space Maxwell-Faraday carrier
`PTSymmetricQFT.MaxwellFaraday.faraday`. The bridge keeps the derivative operator
and connection coefficients explicit:

* `coordinateFaradayTensor` is `F = dA` in coordinates.
* `homogeneousMaxwell_of_potential` proves the coordinate `d(dA) = 0` statement
  from mixed-partial symmetry.
* `curvedMaxwell_flatConnection_implies_wave_of_lorenzGauge` proves that the
  inhomogeneous Maxwell equation for a flat connection, Lorenz gauge, and
  commuting mixed partials gives the potential wave equation.
* `curvedMaxwell_implies_waveWithConnection_of_lorenzGauge` removes the
  flat-connection premise and retains both Christoffel-symbol corrections explicitly.
* `covariantSecondDerivVectorAt_commutator_eq_riemannAction` derives the vector
  Ricci commutator from the existing connection-built Riemann curvature.
* `metricCompatibleFaradayDivergenceAt_eq_wave_sub_gradDiv_sub_ricci` proves the
  invariant metric d'Alembertian / Lorenz-gradient / Ricci decomposition.
* `leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge` specializes the
  result to the repository's metric-built Levi-Civita connection.
* `maxwellWave_and_complexEinstein_split` attaches that Maxwell wave equation
  to the repository's matrix-based complex Einstein field equation.
* `maxwellWaveWithConnection_and_complexEinstein_split` provides the corresponding
  general-coordinate Maxwell--complex-Einstein bridge.
* `currentConnectedFunctional_eq_log_sourcePartition` attaches a coordinate
  current to the curved measure path-integral source functional.

-/

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QFT.PathIntegral

variable {ι : Type*}

/-- Coordinate vectors on a finite coordinate chart. -/
abbrev CoordinateVector (ι : Type*) := ι → ℝ

/-- A coordinate one-form field. -/
abbrev CoordinateOneForm (ι : Type*) := CoordinateVector ι → ι → ℝ

/-- A coordinate rank-two tensor field. -/
abbrev CoordinateTwoTensor (ι : Type*) := CoordinateVector ι → ι → ι → ℝ

/-- A coordinate vector current. -/
abbrev CoordinateCurrent (ι : Type*) := CoordinateVector ι → ι → ℝ

/-- Abstract coordinate partial derivative. -/
abbrev CoordinatePartial (ι : Type*) := (CoordinateVector ι → ℝ) → ι → CoordinateVector ι → ℝ

/-- Abstract Christoffel-symbol field `Gamma^i_{jk}`. -/
abbrev CoordinateConnection (ι : Type*) := CoordinateVector ι → ι → ι → ι → ℝ

/-- Partial derivatives distribute over subtraction. -/
def PartialSubRule (coordDeriv : CoordinatePartial ι) : Prop :=
  ∀ (f g : CoordinateVector ι → ℝ) (k : ι) (x : CoordinateVector ι),
    coordDeriv (fun y => f y - g y) k x = coordDeriv f k x - coordDeriv g k x

/-- Coordinate Faraday tensor from a potential one-form:
`F_{mu nu} = partial_mu A_nu - partial_nu A_mu`. -/
def coordinateFaradayTensor (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) :
    CoordinateTwoTensor ι :=
  fun x μ ν => coordDeriv (fun y => A y ν) μ x - coordDeriv (fun y => A y μ) ν x

/-- The coordinate Faraday tensor `F = dA` is antisymmetric. -/
lemma coordinateFaradayTensor_antisymm
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (x : CoordinateVector ι) (μ ν : ι) :
    coordinateFaradayTensor coordDeriv A x μ ν =
      -coordinateFaradayTensor coordDeriv A x ν μ := by
  unfold coordinateFaradayTensor
  ring

/-! ## Link to the existing momentum-space Maxwell-Faraday carrier -/

/-- Coordinate derivative specialization `partial_mu f = k_mu * f`, the
momentum-space convention used by `PTSymmetricQFT.MaxwellFaraday`. -/
def momentumCoordinatePartial (k : Fin 4 → ℝ) : CoordinatePartial (Fin 4) :=
  fun f μ x => k μ * f x

/-- Constant coordinate one-form corresponding to a momentum-space potential. -/
def constantCoordinatePotential (A : Fin 4 → ℝ) : CoordinateOneForm (Fin 4) :=
  fun _ μ => A μ

/-- The coordinate Maxwell-Faraday tensor reduces exactly to the existing
momentum-space carrier when `partial_mu` is specialized to multiplication by
`k_mu` and the potential is coordinate-constant. -/
lemma coordinateFaradayTensor_momentum_eq_faraday
    (k A : Fin 4 → ℝ) (x : CoordinateVector (Fin 4)) :
    coordinateFaradayTensor (momentumCoordinatePartial k) (constantCoordinatePotential A) x =
      fun μ ν => faraday k A μ ν := by
  funext μ ν
  simp [coordinateFaradayTensor, momentumCoordinatePartial, constantCoordinatePotential,
    faraday, Matrix.of_apply]

/-- Cyclic homogeneous Maxwell operator
`partial_mu F_{nu rho} + partial_nu F_{rho mu} + partial_rho F_{mu nu}`. -/
def homogeneousCyclic (coordDeriv : CoordinatePartial ι) (F : CoordinateTwoTensor ι)
    (μ ν ρ : ι) (x : CoordinateVector ι) : ℝ :=
  coordDeriv (fun y => F y ν ρ) μ x
    + coordDeriv (fun y => F y ρ μ) ν x
    + coordDeriv (fun y => F y μ ν) ρ x

/-- Mixed-partial commutator for one component of a potential. -/
def mixedPartialCommutator (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (μ ν ρ : ι) (x : CoordinateVector ι) : ℝ :=
  coordDeriv (fun y => coordDeriv (fun z => A z ρ) ν y) μ x
    - coordDeriv (fun y => coordDeriv (fun z => A z ρ) μ y) ν x

/-- Exact coordinate decomposition of `d(dA)` into mixed-partial commutators. -/
lemma homogeneousCyclic_faraday_eq_mixedPartialCommutatorSum
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (hSub : PartialSubRule coordDeriv) (μ ν ρ : ι) (x : CoordinateVector ι) :
    homogeneousCyclic coordDeriv (coordinateFaradayTensor coordDeriv A) μ ν ρ x =
      mixedPartialCommutator coordDeriv A μ ν ρ x
        + mixedPartialCommutator coordDeriv A ν ρ μ x
        + mixedPartialCommutator coordDeriv A ρ μ ν x := by
  unfold homogeneousCyclic coordinateFaradayTensor mixedPartialCommutator
  rw [hSub (fun y => coordDeriv (fun z => A z ρ) ν y)
      (fun y => coordDeriv (fun z => A z ν) ρ y) μ x]
  rw [hSub (fun y => coordDeriv (fun z => A z μ) ρ y)
      (fun y => coordDeriv (fun z => A z ρ) μ y) ν x]
  rw [hSub (fun y => coordDeriv (fun z => A z ν) μ y)
      (fun y => coordDeriv (fun z => A z μ) ν y) ρ x]
  ring

/-- Mixed-partial symmetry for every component of a potential. -/
def MixedPartialSymmetric (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) : Prop :=
  ∀ (μ ν ρ : ι) (x : CoordinateVector ι), mixedPartialCommutator coordDeriv A μ ν ρ x = 0

/-- Coordinate homogeneous Maxwell equation. -/
def MaxwellHomogeneous (coordDeriv : CoordinatePartial ι) (F : CoordinateTwoTensor ι) : Prop :=
  ∀ (μ ν ρ : ι) (x : CoordinateVector ι), homogeneousCyclic coordDeriv F μ ν ρ x = 0

/-- Homogeneous Maxwell equation for `F = dA` under mixed-partial symmetry. -/
lemma homogeneousMaxwell_of_potential
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (hSub : PartialSubRule coordDeriv) (hSymm : MixedPartialSymmetric coordDeriv A) :
    MaxwellHomogeneous coordDeriv (coordinateFaradayTensor coordDeriv A) := by
  intro μ ν ρ x
  rw [homogeneousCyclic_faraday_eq_mixedPartialCommutatorSum
    (coordDeriv := coordDeriv) (A := A) (hSub := hSub)]
  simp [hSymm μ ν ρ x, hSymm ν ρ μ x, hSymm ρ μ ν x]

/-- Covariant derivative of a contravariant rank-two tensor:
`nabla_k F^{ij} = partial_k F^{ij} + Gamma^i_{kl} F^{lj} + Gamma^j_{kl} F^{il}`. -/
def covariantDerivTwoContravariant [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι) (F : CoordinateTwoTensor ι)
    (k i j : ι) (x : CoordinateVector ι) : ℝ :=
  coordDeriv (fun y => F y i j) k x
    + (∑ l : ι, Γ x i k l * F x l j)
    + (∑ l : ι, Γ x j k l * F x i l)

/-- Covariant divergence `nabla_mu F^{mu nu}`. -/
def covariantDivTwoContravariant [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι) (F : CoordinateTwoTensor ι)
    (ν : ι) (x : CoordinateVector ι) : ℝ :=
  ∑ μ : ι, covariantDerivTwoContravariant coordDeriv Γ F μ μ ν x

/-- Flat partial divergence `partial_mu F^{mu nu}`. -/
def partialDivTwoContravariant [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (F : CoordinateTwoTensor ι)
    (ν : ι) (x : CoordinateVector ι) : ℝ :=
  ∑ μ : ι, coordDeriv (fun y => F y μ ν) μ x

/-! ## General-connection divergence decomposition -/

/-- The explicit Christoffel-symbol correction in `∇_μ F^{μν}`. It records both
contravariant-index connection terms and is therefore the exact difference between the coordinate
covariant divergence and the partial divergence used below. -/
def covariantDivergenceConnectionCorrection [Fintype ι]
    (Γ : CoordinateConnection ι) (F : CoordinateTwoTensor ι)
    (ν : ι) (x : CoordinateVector ι) : ℝ :=
  ∑ μ : ι,
    ((∑ l : ι, Γ x μ μ l * F x l ν)
      + (∑ l : ι, Γ x ν μ l * F x μ l))

/-- **[Covariant divergence = partial divergence + connection correction].** This is the
general-coordinate identity underlying the curved Maxwell potential equation; unlike the earlier
flat-connection reduction, no Christoffel coefficient is assumed to vanish. -/
lemma covariantDivTwoContravariant_eq_partial_add_connectionCorrection [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (F : CoordinateTwoTensor ι) (ν : ι) (x : CoordinateVector ι) :
    covariantDivTwoContravariant coordDeriv Γ F ν x =
      partialDivTwoContravariant coordDeriv F ν x
        + covariantDivergenceConnectionCorrection Γ F ν x := by
  unfold covariantDivTwoContravariant covariantDerivTwoContravariant
    partialDivTwoContravariant covariantDivergenceConnectionCorrection
  repeat rw [Finset.sum_add_distrib]
  ring

/-! ## Geometric curvature commutator and Maxwell wave identity -/

/-- The covariant derivative of a contravariant vector at one chart point,
`(nabla_mu V)^rho = partial_mu V^rho + Gamma^rho_{mu sigma} V^sigma`.
The value and first derivative are kept as pointwise jet data, matching the
repository's pointwise Schrödinger and covariant-Hessian carriers. -/
def covariantDerivVectorAt [Fintype ι] (Γ : ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (μ ρ : ι) : ℝ :=
  dV μ ρ + ∑ σ, (Γ ρ) μ σ * V σ

/-- The second covariant derivative of a vector at one chart point. The lower
derivative index on `nabla_nu V^rho` contributes the final negative Christoffel
term, so this is the full `(1,1)`-tensor derivative rather than a componentwise
second partial derivative. -/
def covariantSecondDerivVectorAt [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (μ ν ρ : ι) : ℝ :=
  ddV μ ν ρ
    + ∑ σ, ((dΓ μ ρ) ν σ * V σ + (Γ ρ) ν σ * dV μ σ)
    + ∑ l, (Γ ρ) μ l * covariantDerivVectorAt Γ V dV ν l
    - ∑ l, (Γ l) μ ν * covariantDerivVectorAt Γ V dV l ρ

/-- **[Ricci identity for a vector].** For a torsion-free connection and
commuting second partials,
`(nabla_mu nabla_nu - nabla_nu nabla_mu)V^rho = R^rho_{ sigma mu nu} V^sigma`.
The curvature on the right is the existing connection-built
`riemannFromConnection`; no curvature law is introduced as a premise. -/
lemma covariantSecondDerivVectorAt_commutator_eq_riemannAction [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hΓ : IsTorsionFree Γ)
    (hddV : ∀ μ ν ρ, ddV μ ν ρ = ddV ν μ ρ) (μ ν ρ : ι) :
    covariantSecondDerivVectorAt Γ dΓ V dV ddV μ ν ρ
        - covariantSecondDerivVectorAt Γ dΓ V dV ddV ν μ ρ =
      ∑ σ, riemannFromConnection Γ dΓ ρ σ μ ν * V σ := by
  have hΓcomp : ∀ l, (Γ l) μ ν = (Γ l) ν μ := by
    intro l
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hΓ l) ν) μ
  have hSwap (a b : ι) :
      (∑ σ, ∑ l, (Γ ρ) a l * (Γ l) b σ * V σ) =
        ∑ l, ∑ σ, (Γ ρ) a l * (Γ l) b σ * V σ := by
    rw [Finset.sum_comm]
  have hConnExpand (a b : ι) :
      (∑ l, (Γ ρ) a l * (dV b l + ∑ σ, (Γ l) b σ * V σ)) =
        (∑ l, (Γ ρ) a l * dV b l)
          + ∑ l, ∑ σ, (Γ ρ) a l * (Γ l) b σ * V σ := by
    calc
      _ = ∑ l, ((Γ ρ) a l * dV b l
          + (Γ ρ) a l * ∑ σ, (Γ l) b σ * V σ) := by
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = (∑ l, (Γ ρ) a l * dV b l)
          + ∑ l, (Γ ρ) a l * ∑ σ, (Γ l) b σ * V σ := Finset.sum_add_distrib
      _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun l _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
  unfold covariantSecondDerivVectorAt covariantDerivVectorAt riemannFromConnection
  rw [hddV μ ν ρ]
  simp_rw [hΓcomp]
  rw [hConnExpand μ ν, hConnExpand ν μ]
  repeat rw [Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib, Finset.sum_mul, add_mul, sub_mul]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [Finset.sum_sub_distrib]
  rw [hSwap μ ν, hSwap ν μ]
  ring

/-- The Ricci curvature acting on a vector, using the repository's contraction
`R_{sigma nu} = R^mu_{ sigma mu nu}`. -/
noncomputable def ricciActionAt [Fintype ι] (Γ : ι → Matrix ι ι ℝ)
    (dΓ : ι → ι → Matrix ι ι ℝ) (V : ι → ℝ) (ν : ι) : ℝ :=
  ∑ σ, ricciFromConnection Γ dΓ σ ν * V σ

/-- **[The contracted vector commutator is Ricci curvature].** Contracting the
upper vector index with the first derivative index in the Ricci identity gives
`sum_mu [nabla_mu,nabla_nu]V^mu = R_{sigma nu} V^sigma`. -/
lemma covariantSecondDerivVectorAt_commutator_contraction_eq_ricciAction [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hΓ : IsTorsionFree Γ)
    (hddV : ∀ μ ν ρ, ddV μ ν ρ = ddV ν μ ρ) (ν : ι) :
    (∑ μ, (covariantSecondDerivVectorAt Γ dΓ V dV ddV μ ν μ
      - covariantSecondDerivVectorAt Γ dΓ V dV ddV ν μ μ)) =
        ricciActionAt Γ dΓ V ν := by
  rw [Finset.sum_congr rfl fun μ _ =>
    covariantSecondDerivVectorAt_commutator_eq_riemannAction
      Γ dΓ V dV ddV hΓ hddV μ ν μ]
  unfold ricciActionAt ricciFromConnection
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ => by rw [Finset.sum_mul]

/-- The metric-contracted vector d'Alembertian `g^{mu alpha} nabla_mu nabla_alpha V^nu`
at one point. -/
def covariantVectorWaveAt [Fintype ι] (gInv : Matrix ι ι ℝ)
    (nabla2V : ι → ι → ι → ℝ) (ν : ι) : ℝ :=
  ∑ μ, ∑ α, gInv μ α * nabla2V μ α ν

/-- The raised gradient of the covariant divergence,
`nabla^nu(nabla_mu V^mu)`, at one point. -/
def covariantVectorGradDivAt [Fintype ι] (gInv : Matrix ι ι ℝ)
    (nabla2V : ι → ι → ι → ℝ) (ν : ι) : ℝ :=
  ∑ α, gInv ν α * ∑ μ, nabla2V α μ μ

/-- The raised Ricci endomorphism `R^nu_{ sigma} V^sigma`. -/
noncomputable def raisedRicciActionAt [Fintype ι] (gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (ν : ι) : ℝ :=
  ∑ α, gInv ν α * ricciActionAt Γ dΓ V α

/-- The divergence of `F^{mu nu} = nabla^mu V^nu - nabla^nu V^mu`
after metric compatibility removes derivatives of `gInv`. It is expressed in
second-covariant-derivative jet data so the curvature commutator remains visible. -/
def metricCompatibleFaradayDivergenceAt [Fintype ι] (gInv : Matrix ι ι ℝ)
    (nabla2V : ι → ι → ι → ℝ) (ν : ι) : ℝ :=
  covariantVectorWaveAt gInv nabla2V ν
    - ∑ α, gInv ν α * ∑ μ, nabla2V μ α μ

/-- **[Fully geometric Maxwell curvature identity].** For a torsion-free
connection and commuting second partials,
`nabla_mu F^{mu nu} = box_g V^nu - nabla^nu(nabla_mu V^mu) - R^nu_{ sigma}V^sigma`.
The Ricci term is not postulated: it is the contraction of the preceding
connection-built Riemann commutator. -/
lemma metricCompatibleFaradayDivergenceAt_eq_wave_sub_gradDiv_sub_ricci [Fintype ι]
    (gInv : Matrix ι ι ℝ) (Γ : ι → Matrix ι ι ℝ)
    (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hΓ : IsTorsionFree Γ)
    (hddV : ∀ μ ν ρ, ddV μ ν ρ = ddV ν μ ρ) (ν : ι) :
    metricCompatibleFaradayDivergenceAt gInv
        (covariantSecondDerivVectorAt Γ dΓ V dV ddV) ν =
      covariantVectorWaveAt gInv (covariantSecondDerivVectorAt Γ dΓ V dV ddV) ν
        - covariantVectorGradDivAt gInv
          (covariantSecondDerivVectorAt Γ dΓ V dV ddV) ν
        - raisedRicciActionAt gInv Γ dΓ V ν := by
  have hContract (α : ι) :=
    covariantSecondDerivVectorAt_commutator_contraction_eq_ricciAction
      Γ dΓ V dV ddV hΓ hddV α
  have hReorder (α : ι) :
      (∑ μ, covariantSecondDerivVectorAt Γ dΓ V dV ddV μ α μ) =
        (∑ μ, covariantSecondDerivVectorAt Γ dΓ V dV ddV α μ μ)
          + ricciActionAt Γ dΓ V α := by
    rw [← hContract α, Finset.sum_sub_distrib]
    ring
  unfold metricCompatibleFaradayDivergenceAt covariantVectorGradDivAt raisedRicciActionAt
  simp_rw [hReorder, mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- Pointwise geometric inhomogeneous Maxwell equation `nabla_mu F^{mu nu}=J^nu`. -/
def GeometricMaxwellInhomogeneousAt [Fintype ι] (gInv : Matrix ι ι ℝ)
    (nabla2V : ι → ι → ι → ℝ) (J : ι → ℝ) : Prop :=
  ∀ ν, metricCompatibleFaradayDivergenceAt gInv nabla2V ν = J ν

/-- Differentiated covariant Lorenz gauge `nabla^nu(nabla_mu V^mu)=0` at one point. -/
def CovariantLorenzGaugeGradientAt [Fintype ι] (gInv : Matrix ι ι ℝ)
    (nabla2V : ι → ι → ι → ℝ) : Prop :=
  ∀ ν, covariantVectorGradDivAt gInv nabla2V ν = 0

/-- The Ricci-coupled curved-spacetime vector wave equation in the sign convention
fixed by `riemannFromConnection`. -/
noncomputable def RicciCoupledVectorWaveEquationAt [Fintype ι] (gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V J : ι → ℝ) (nabla2V : ι → ι → ι → ℝ) : Prop :=
  ∀ ν, covariantVectorWaveAt gInv nabla2V ν - raisedRicciActionAt gInv Γ dΓ V ν = J ν

/-- **[Curved Maxwell in Lorenz gauge gives the Ricci-coupled wave equation].** -/
lemma geometricMaxwell_implies_ricciCoupledWave_of_lorenzGauge [Fintype ι]
    (gInv : Matrix ι ι ℝ) (Γ : ι → Matrix ι ι ℝ)
    (dΓ : ι → ι → Matrix ι ι ℝ)
    (V J : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hΓ : IsTorsionFree Γ)
    (hddV : ∀ μ ν ρ, ddV μ ν ρ = ddV ν μ ρ)
    (hMaxwell : GeometricMaxwellInhomogeneousAt gInv
      (covariantSecondDerivVectorAt Γ dΓ V dV ddV) J)
    (hGauge : CovariantLorenzGaugeGradientAt gInv
      (covariantSecondDerivVectorAt Γ dΓ V dV ddV)) :
    RicciCoupledVectorWaveEquationAt gInv Γ dΓ V J
      (covariantSecondDerivVectorAt Γ dΓ V dV ddV) := by
  intro ν
  have hIdentity := metricCompatibleFaradayDivergenceAt_eq_wave_sub_gradDiv_sub_ricci
    gInv Γ dΓ V dV ddV hΓ hddV ν
  rw [hGauge ν] at hIdentity
  have hSource := hMaxwell ν
  linarith

/-- **[Metric-built Levi-Civita Maxwell wave identity].** The preceding curved
Maxwell result specialized to `christoffelFromMetric`. The repository's
metric-to-Christoffel construction discharges both torsion-freeness and metric
compatibility, and the latter is returned alongside the Ricci-coupled wave equation. -/
lemma leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge
    [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (dΓ : ι → ι → Matrix ι ι ℝ)
    (V J : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hg : Matrix.transpose g = g) (hgi : Matrix.transpose gInv = gInv)
    (hinv : gInv * g = 1)
    (hdg : ∀ κ, Matrix.transpose (dg κ) = dg κ)
    (hddV : ∀ μ ν ρ, ddV μ ν ρ = ddV ν μ ρ)
    (hMaxwell : GeometricMaxwellInhomogeneousAt gInv
      (covariantSecondDerivVectorAt (christoffelFromMetric gInv dg) dΓ V dV ddV) J)
    (hGauge : CovariantLorenzGaugeGradientAt gInv
      (covariantSecondDerivVectorAt (christoffelFromMetric gInv dg) dΓ V dV ddV)) :
    IsMetricCompatible (christoffelFromMetric gInv dg) dg g
      ∧ RicciCoupledVectorWaveEquationAt gInv (christoffelFromMetric gInv dg) dΓ V J
        (covariantSecondDerivVectorAt (christoffelFromMetric gInv dg) dΓ V dV ddV) :=
  ⟨christoffelFromMetric_isMetricCompatible dg hg hgi hinv hdg,
    geometricMaxwell_implies_ricciCoupledWave_of_lorenzGauge
      gInv (christoffelFromMetric gInv dg) dΓ V J dV ddV
        (christoffelFromMetric_isTorsionFree gInv dg hdg) hddV hMaxwell hGauge⟩

/-! ## Geometric Maxwell identity on an entire coordinate chart -/

/-- The Ricci-coupled vector wave equation imposed at every point of a
coordinate chart.  The carrier `X` indexes chart points; metric, connection,
potential, source, and derivative jets may all vary with `x : X`. -/
def RicciCoupledVectorWaveEquationOnChart [Fintype ι] {X : Type*}
    (gInv : X → Matrix ι ι ℝ)
    (Γ : X → ι → Matrix ι ι ℝ) (dΓ : X → ι → ι → Matrix ι ι ℝ)
    (V J : X → ι → ℝ) (nabla2V : X → ι → ι → ι → ℝ) : Prop :=
  ∀ x, RicciCoupledVectorWaveEquationAt
    (gInv x) (Γ x) (dΓ x) (V x) (J x) (nabla2V x)

/-- **[Levi-Civita Maxwell identity on a coordinate chart].** If the metric
inverse law, metric symmetry, commuting second partials, Maxwell equation, and
Lorenz gauge hold at every chart point, then the metric-built connection is
metric compatible everywhere and the potential obeys the Ricci-coupled wave
equation everywhere.

This is the global chart-indexed lift of the pointwise jet theorem.  It does
not assert that arbitrary supplied jets arise from smooth manifold fields;
that analytic jet-realization step remains separate. -/
lemma leviCivitaMaxwell_implies_ricciCoupledWave_onChart
    [Fintype ι] [DecidableEq ι] {X : Type*}
    (g gInv : X → Matrix ι ι ℝ) (dg : X → ι → Matrix ι ι ℝ)
    (dΓ : X → ι → ι → Matrix ι ι ℝ)
    (V J : X → ι → ℝ) (dV : X → ι → ι → ℝ)
    (ddV : X → ι → ι → ι → ℝ)
    (hg : ∀ x, Matrix.transpose (g x) = g x)
    (hgi : ∀ x, Matrix.transpose (gInv x) = gInv x)
    (hinv : ∀ x, gInv x * g x = 1)
    (hdg : ∀ x κ, Matrix.transpose (dg x κ) = dg x κ)
    (hddV : ∀ x μ ν ρ, ddV x μ ν ρ = ddV x ν μ ρ)
    (hMaxwell : ∀ x, GeometricMaxwellInhomogeneousAt (gInv x)
      (covariantSecondDerivVectorAt
        (christoffelFromMetric (gInv x) (dg x)) (dΓ x) (V x) (dV x) (ddV x)) (J x))
    (hGauge : ∀ x, CovariantLorenzGaugeGradientAt (gInv x)
      (covariantSecondDerivVectorAt
        (christoffelFromMetric (gInv x) (dg x)) (dΓ x) (V x) (dV x) (ddV x))) :
    (∀ x, IsMetricCompatible
      (christoffelFromMetric (gInv x) (dg x)) (dg x) (g x))
      ∧ RicciCoupledVectorWaveEquationOnChart gInv
        (fun x => christoffelFromMetric (gInv x) (dg x)) dΓ V J
        (fun x => covariantSecondDerivVectorAt
          (christoffelFromMetric (gInv x) (dg x)) (dΓ x) (V x) (dV x) (ddV x)) := by
  constructor
  · intro x
    exact (leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge
      (g x) (gInv x) (dg x) (dΓ x) (V x) (J x) (dV x) (ddV x)
      (hg x) (hgi x) (hinv x) (hdg x) (hddV x) (hMaxwell x) (hGauge x)).1
  · intro x
    exact (leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge
      (g x) (gInv x) (dg x) (dΓ x) (V x) (J x) (dV x) (ddV x)
      (hg x) (hgi x) (hinv x) (hdg x) (hddV x) (hMaxwell x) (hGauge x)).2

/-! ## Geometric jets constructed from chart fields -/

/-- The first coordinate jet `∂_κ g_{μν}` constructed from a metric field. -/
def metricFirstJet (coordDeriv : CoordinatePartial ι)
    (g : CoordinateVector ι → Matrix ι ι ℝ)
    (x : CoordinateVector ι) (κ : ι) : Matrix ι ι ℝ :=
  Matrix.of fun μ ν => coordDeriv (fun y => g y μ ν) κ x

/-- Pointwise symmetry of a metric field induces symmetry of its constructed
first coordinate jet. -/
lemma metricFirstJet_transpose_eq [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (g : CoordinateVector ι → Matrix ι ι ℝ)
    (hg : ∀ x, Matrix.transpose (g x) = g x)
    (x : CoordinateVector ι) (κ : ι) :
    Matrix.transpose (metricFirstJet coordDeriv g x κ) =
      metricFirstJet coordDeriv g x κ := by
  ext μ ν
  simp only [Matrix.transpose_apply, metricFirstJet, Matrix.of_apply]
  apply congrArg (fun f : CoordinateVector ι → ℝ => coordDeriv f κ x)
  funext y
  simpa [Matrix.transpose_apply] using congrFun (congrFun (hg y) μ) ν

/-- The Levi-Civita connection field constructed pointwise from a metric and
its first coordinate jet. -/
noncomputable def leviCivitaConnectionField [Fintype ι]
    (coordDeriv : CoordinatePartial ι)
    (g gInv : CoordinateVector ι → Matrix ι ι ℝ) :
    CoordinateVector ι → ι → Matrix ι ι ℝ :=
  fun x => christoffelFromMetric (gInv x) (metricFirstJet coordDeriv g x)

/-- The first coordinate jet `∂_μ Γ^σ_{νρ}` constructed from a connection
field. -/
def connectionFirstJet (coordDeriv : CoordinatePartial ι)
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ)
    (x : CoordinateVector ι) (μ σ : ι) : Matrix ι ι ℝ :=
  Matrix.of fun ν ρ => coordDeriv (fun y => Γ y σ ν ρ) μ x

/-- The first coordinate jet `∂_μ V^ρ` constructed from a vector field. -/
def vectorFirstJet (coordDeriv : CoordinatePartial ι)
    (V : CoordinateVector ι → ι → ℝ)
    (x : CoordinateVector ι) (μ ρ : ι) : ℝ :=
  coordDeriv (fun y => V y ρ) μ x

/-- The second coordinate jet `∂_μ∂_ν V^ρ` constructed by iterating the same
coordinate derivative. -/
def vectorSecondJet (coordDeriv : CoordinatePartial ι)
    (V : CoordinateVector ι → ι → ℝ)
    (x : CoordinateVector ι) (μ ν ρ : ι) : ℝ :=
  coordDeriv (fun y => coordDeriv (fun z => V z ρ) ν y) μ x

/-- Mixed second coordinate derivatives commute on every component of a
vector field.  For a smooth coordinate derivative this is the local Schwarz
condition used by the Ricci commutator. -/
def VectorSecondPartialsCommute (coordDeriv : CoordinatePartial ι)
    (V : CoordinateVector ι → ι → ℝ) : Prop :=
  ∀ x μ ν ρ, vectorSecondJet coordDeriv V x μ ν ρ =
    vectorSecondJet coordDeriv V x ν μ ρ

/-- The native coordinate derivative on a finite real chart, obtained by
evaluating the Fréchet derivative in a coordinate basis direction. -/
noncomputable def frechetCoordinatePartial [Fintype ι] [DecidableEq ι] :
    CoordinatePartial ι :=
  fun f μ x => fderiv ℝ f x (Pi.single μ 1)

/-- Components of a `C²` vector field have commuting second partials for the
native Fréchet coordinate derivative.  This discharges the local Schwarz
premise used by the Ricci commutator from ordinary smoothness. -/
lemma vectorSecondPartialsCommute_frechet_of_contDiff
    [Fintype ι] [DecidableEq ι]
    (V : CoordinateVector ι → ι → ℝ)
    (hV : ∀ ρ, ContDiff ℝ 2 (fun x => V x ρ)) :
    VectorSecondPartialsCommute (frechetCoordinatePartial (ι := ι)) V := by
  intro x μ ν ρ
  let eμ : CoordinateVector ι := Pi.single μ 1
  let eν : CoordinateVector ι := Pi.single ν 1
  let f : CoordinateVector ι → ℝ := fun y => V y ρ
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hV ρ).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hEval (base e : CoordinateVector ι) :
      fderiv ℝ (fun y => fderiv ℝ f y e) x base =
        fderiv ℝ (fderiv ℝ f) x base e := by
    rw [fderiv_clm_apply hc (differentiableAt_const e)]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y eν) x eμ =
    fderiv ℝ (fun y => fderiv ℝ f y eμ) x eν
  rw [hEval eμ eν, hEval eν eμ]
  exact (hV ρ).contDiffAt.isSymmSndFDerivAt (by norm_num) eμ eν

/-- The second covariant derivative field obtained entirely from the metric,
inverse metric, vector field, and their coordinate derivatives. -/
noncomputable def leviCivitaSecondDerivVectorField [Fintype ι]
    (coordDeriv : CoordinatePartial ι)
    (g gInv : CoordinateVector ι → Matrix ι ι ℝ)
    (V : CoordinateVector ι → ι → ℝ) :
    CoordinateVector ι → ι → ι → ι → ℝ :=
  fun x => covariantSecondDerivVectorAt
    (leviCivitaConnectionField coordDeriv g gInv x)
    (connectionFirstJet coordDeriv
      (leviCivitaConnectionField coordDeriv g gInv) x)
    (V x) (vectorFirstJet coordDeriv V x) (vectorSecondJet coordDeriv V x)

/-- **[Field-realized Levi-Civita Maxwell curvature identity].** Metric,
connection, and vector jets are constructed from actual chart fields by one
coordinate derivative.  Under inverse-metric, symmetry, Maxwell, Lorenz, and
mixed-partial hypotheses, the constructed Levi-Civita connection is metric
compatible and its potential satisfies the Ricci-coupled vector wave equation
at every chart point. -/
lemma metricFieldMaxwell_implies_ricciCoupledWave_onChart
    [Fintype ι] [DecidableEq ι]
    (coordDeriv : CoordinatePartial ι)
    (g gInv : CoordinateVector ι → Matrix ι ι ℝ)
    (V J : CoordinateVector ι → ι → ℝ)
    (hg : ∀ x, Matrix.transpose (g x) = g x)
    (hgi : ∀ x, Matrix.transpose (gInv x) = gInv x)
    (hinv : ∀ x, gInv x * g x = 1)
    (hcomm : VectorSecondPartialsCommute coordDeriv V)
    (hMaxwell : ∀ x, GeometricMaxwellInhomogeneousAt (gInv x)
      (leviCivitaSecondDerivVectorField coordDeriv g gInv V x) (J x))
    (hGauge : ∀ x, CovariantLorenzGaugeGradientAt (gInv x)
      (leviCivitaSecondDerivVectorField coordDeriv g gInv V x)) :
    (∀ x, IsMetricCompatible
      (leviCivitaConnectionField coordDeriv g gInv x)
      (metricFirstJet coordDeriv g x) (g x))
      ∧ RicciCoupledVectorWaveEquationOnChart gInv
        (leviCivitaConnectionField coordDeriv g gInv)
        (fun x => connectionFirstJet coordDeriv
          (leviCivitaConnectionField coordDeriv g gInv) x)
        V J (leviCivitaSecondDerivVectorField coordDeriv g gInv V) := by
  exact leviCivitaMaxwell_implies_ricciCoupledWave_onChart
    g gInv (metricFirstJet coordDeriv g)
    (fun x => connectionFirstJet coordDeriv
      (leviCivitaConnectionField coordDeriv g gInv) x)
    V J (vectorFirstJet coordDeriv V) (vectorSecondJet coordDeriv V)
    hg hgi hinv (metricFirstJet_transpose_eq coordDeriv g hg)
    hcomm hMaxwell hGauge

/-- **[Smooth field-realized Levi-Civita Maxwell curvature identity].** For
the native Fréchet coordinate derivative, `C²` regularity of every vector
component supplies the mixed-partial identity.  Thus the metric and inverse
metric fields construct the Levi-Civita connection and curvature, while the
geometric Maxwell and Lorenz equations imply the Ricci-coupled vector wave
equation without a separately postulated Schwarz premise. -/
lemma contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart
    [Fintype ι] [DecidableEq ι]
    (g gInv : CoordinateVector ι → Matrix ι ι ℝ)
    (V J : CoordinateVector ι → ι → ℝ)
    (hg : ∀ x, Matrix.transpose (g x) = g x)
    (hgi : ∀ x, Matrix.transpose (gInv x) = gInv x)
    (hinv : ∀ x, gInv x * g x = 1)
    (hV : ∀ ρ, ContDiff ℝ 2 (fun x => V x ρ))
    (hMaxwell : ∀ x, GeometricMaxwellInhomogeneousAt (gInv x)
      (leviCivitaSecondDerivVectorField
        (frechetCoordinatePartial (ι := ι)) g gInv V x) (J x))
    (hGauge : ∀ x, CovariantLorenzGaugeGradientAt (gInv x)
      (leviCivitaSecondDerivVectorField
        (frechetCoordinatePartial (ι := ι)) g gInv V x)) :
    (∀ x, IsMetricCompatible
      (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv x)
      (metricFirstJet (frechetCoordinatePartial (ι := ι)) g x) (g x))
      ∧ RicciCoupledVectorWaveEquationOnChart gInv
        (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv)
        (fun x => connectionFirstJet (frechetCoordinatePartial (ι := ι))
          (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv) x)
        V J (leviCivitaSecondDerivVectorField
          (frechetCoordinatePartial (ι := ι)) g gInv V) := by
  exact metricFieldMaxwell_implies_ricciCoupledWave_onChart
    (frechetCoordinatePartial (ι := ι)) g gInv V J hg hgi hinv
    (vectorSecondPartialsCommute_frechet_of_contDiff V hV) hMaxwell hGauge

/-- With the coordinate convention `partial_mu F^{mu nu}`, the
momentum-specialized coordinate divergence is the negative of the existing
Greaves-Thomas Maxwell operator `F^{nu mu} k_mu`. This theorem records the
index-order sign convention instead of redefining the momentum-space operator. -/
lemma partialDiv_momentumCoordinateFaraday_eq_neg_maxwellOp
    (k A : Fin 4 → ℝ) (ν : Fin 4) (x : CoordinateVector (Fin 4)) :
    partialDivTwoContravariant (momentumCoordinatePartial k)
      (coordinateFaradayTensor (momentumCoordinatePartial k) (constantCoordinatePotential A)) ν x =
      -PTSymmetricQFT.PTTensorDynamics.maxwellOp (faraday k A) k ν := by
  unfold partialDivTwoContravariant coordinateFaradayTensor
  unfold momentumCoordinatePartial constantCoordinatePotential
  unfold PTSymmetricQFT.PTTensorDynamics.maxwellOp faraday
  simp only [Matrix.of_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro μ _
  ring

/-- The same momentum-specialized coordinate divergence is the existing
Heras/Maxwell four-current carrier `J^nu = partial_mu F^{mu nu}`. -/
lemma partialDiv_momentumCoordinateFaraday_eq_fourCurrent
    (k A : Fin 4 → ℝ) (ν : Fin 4) (x : CoordinateVector (Fin 4)) :
    partialDivTwoContravariant (momentumCoordinatePartial k)
      (coordinateFaradayTensor (momentumCoordinatePartial k) (constantCoordinatePotential A)) ν x =
      fourCurrent k A ν := by
  simp [partialDivTwoContravariant, coordinateFaradayTensor, momentumCoordinatePartial,
    constantCoordinatePotential, fourCurrent, faraday, Matrix.of_apply]

/-- The coordinate divergence current obtained from the momentum-specialized
Faraday tensor is conserved because it is definitionally the existing
`Electromagnetic.MaxwellContinuityCovariant.fourCurrent`. -/
lemma partialDiv_momentumCoordinateFaraday_conserved
    (k A : Fin 4 → ℝ) (x : CoordinateVector (Fin 4)) :
    (∑ ν : Fin 4,
      k ν * partialDivTwoContravariant (momentumCoordinatePartial k)
        (coordinateFaradayTensor (momentumCoordinatePartial k)
          (constantCoordinatePotential A)) ν x) = 0 := by
  have h := fourCurrent_conserved k A
  rw [show (∑ ν : Fin 4,
      k ν * partialDivTwoContravariant (momentumCoordinatePartial k)
        (coordinateFaradayTensor (momentumCoordinatePartial k) (constantCoordinatePotential A)) ν x)
      = ∑ ν : Fin 4, k ν * fourCurrent k A ν by
        refine Finset.sum_congr rfl ?_
        intro ν _
        rw [partialDiv_momentumCoordinateFaraday_eq_fourCurrent]]
  simpa using h

/-- A connection vanishes in the chosen coordinates. -/
def ConnectionVanishes (Γ : CoordinateConnection ι) : Prop :=
  ∀ (x : CoordinateVector ι) (i j k : ι), Γ x i j k = 0

/-- If the connection coefficients vanish, the covariant derivative reduces to
a partial derivative. -/
lemma covariantDerivTwoContravariant_eq_partial_of_connectionVanishes [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι) (F : CoordinateTwoTensor ι)
    (hΓ : ConnectionVanishes Γ) (k i j : ι) (x : CoordinateVector ι) :
    covariantDerivTwoContravariant coordDeriv Γ F k i j x =
      coordDeriv (fun y => F y i j) k x := by
  unfold covariantDerivTwoContravariant
  have hLeft : (∑ l : ι, Γ x i k l * F x l j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro l _
    rw [hΓ x i k l]
    simp
  have hRight : (∑ l : ι, Γ x j k l * F x i l) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro l _
    rw [hΓ x j k l]
    simp
  rw [hLeft, hRight]
  ring

/-- If the connection coefficients vanish, the covariant divergence is the partial divergence. -/
lemma covariantDivTwoContravariant_eq_partial_of_connectionVanishes [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι) (F : CoordinateTwoTensor ι)
    (hΓ : ConnectionVanishes Γ) (ν : ι) (x : CoordinateVector ι) :
    covariantDivTwoContravariant coordDeriv Γ F ν x =
      partialDivTwoContravariant coordDeriv F ν x := by
  simp [covariantDivTwoContravariant, partialDivTwoContravariant,
    covariantDerivTwoContravariant_eq_partial_of_connectionVanishes
      (coordDeriv := coordDeriv) (Γ := Γ) (F := F) hΓ]

/-- Flat divergence of a one-form potential, `partial_mu A^mu`. -/
def partialDivOneForm [Fintype ι] (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (x : CoordinateVector ι) : ℝ :=
  ∑ μ : ι, coordDeriv (fun y => A y μ) μ x

/-- Coordinate gradient of `partial . A`. -/
def gradPartialDivOneForm [Fintype ι] (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (ν : ι) (x : CoordinateVector ι) : ℝ :=
  ∑ μ : ι, coordDeriv (fun y => coordDeriv (fun z => A z μ) μ y) ν x

/-- Flat wave operator on a potential component. -/
def wavePotential [Fintype ι] (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (ν : ι) (x : CoordinateVector ι) : ℝ :=
  ∑ μ : ι, coordDeriv (fun y => coordDeriv (fun z => A z ν) μ y) μ x

/-- Divergence-level mixed-partial commutator. -/
def divergenceCommutator [Fintype ι] (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (ν : ι) (x : CoordinateVector ι) : ℝ :=
  ∑ μ : ι,
    (coordDeriv (fun y => coordDeriv (fun z => A z μ) ν y) μ x
      - coordDeriv (fun y => coordDeriv (fun z => A z μ) μ y) ν x)

/-- Exact flat identity for `F = dA`:
`partial_mu F^{mu nu} = box A_nu - partial_nu(partial . A) - comm(A,nu)`. -/
lemma partialDiv_faraday_eq_wave_sub_gradDiv_sub_commutator [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (hSub : PartialSubRule coordDeriv) (ν : ι) (x : CoordinateVector ι) :
    partialDivTwoContravariant coordDeriv (coordinateFaradayTensor coordDeriv A) ν x =
      wavePotential coordDeriv A ν x
        - gradPartialDivOneForm coordDeriv A ν x
        - divergenceCommutator coordDeriv A ν x := by
  unfold partialDivTwoContravariant coordinateFaradayTensor
  have hExpand :
      (∑ μ : ι, coordDeriv
        (fun y =>
          coordDeriv (fun z => A z ν) μ y - coordDeriv (fun z => A z μ) ν y)
        μ x) =
      ∑ μ : ι,
        (coordDeriv (fun y => coordDeriv (fun z => A z ν) μ y) μ x
          - coordDeriv (fun y => coordDeriv (fun z => A z μ) ν y) μ x) := by
    refine Finset.sum_congr rfl ?_
    intro μ _
    simpa using hSub
      (fun y => coordDeriv (fun z => A z ν) μ y)
      (fun y => coordDeriv (fun z => A z μ) ν y)
      μ x
  rw [hExpand]
  unfold wavePotential gradPartialDivOneForm divergenceCommutator
  repeat rw [Finset.sum_sub_distrib]
  ring

/-- Mixed-partial symmetry sufficient to remove the divergence commutator. -/
def DivergenceMixedPartialSymmetric
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) : Prop :=
  ∀ (μ ν : ι) (x : CoordinateVector ι),
    coordDeriv (fun y => coordDeriv (fun z => A z μ) ν y) μ x =
      coordDeriv (fun y => coordDeriv (fun z => A z μ) μ y) ν x

/-- Strong mixed-partial symmetry implies the divergence-level condition. -/
lemma divergenceMixedPartialSymmetric_of_mixedPartialSymmetric
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (h : MixedPartialSymmetric coordDeriv A) :
    DivergenceMixedPartialSymmetric coordDeriv A := by
  intro μ ν x
  have hμ := h μ ν μ x
  unfold mixedPartialCommutator at hμ
  exact sub_eq_zero.mp hμ

/-- The divergence commutator vanishes under divergence-level mixed-partial symmetry. -/
lemma divergenceCommutator_eq_zero_of_symmetry [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (hSymm : DivergenceMixedPartialSymmetric coordDeriv A) (ν : ι) (x : CoordinateVector ι) :
    divergenceCommutator coordDeriv A ν x = 0 := by
  unfold divergenceCommutator
  refine Finset.sum_eq_zero ?_
  intro μ _
  rw [hSymm μ ν x]
  ring

/-- Flat identity with commuting mixed partials:
`partial_mu F^{mu nu} = box A_nu - partial_nu(partial . A)`. -/
lemma partialDiv_faraday_eq_wave_sub_gradDiv_of_symmetry
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (hSub : PartialSubRule coordDeriv) (hSymm : DivergenceMixedPartialSymmetric coordDeriv A)
    (ν : ι) (x : CoordinateVector ι) :
    partialDivTwoContravariant coordDeriv (coordinateFaradayTensor coordDeriv A) ν x =
      wavePotential coordDeriv A ν x - gradPartialDivOneForm coordDeriv A ν x := by
  rw [partialDiv_faraday_eq_wave_sub_gradDiv_sub_commutator
    (coordDeriv := coordDeriv) (A := A) (hSub := hSub)]
  rw [divergenceCommutator_eq_zero_of_symmetry
    (coordDeriv := coordDeriv) (A := A) hSymm ν x]
  ring

/-- Lorenz gauge in flat coordinates. -/
def LorenzGauge [Fintype ι] (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) : Prop :=
  ∀ x : CoordinateVector ι, partialDivOneForm coordDeriv A x = 0

/-- Differentiated Lorenz-gauge closure. -/
def LorenzGaugeGradient [Fintype ι] (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) :
    Prop :=
  ∀ (ν : ι) (x : CoordinateVector ι), gradPartialDivOneForm coordDeriv A ν x = 0

/-- Lorenz gauge plus its differentiated closure. -/
def LorenzGaugeClosure [Fintype ι] (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) :
    Prop :=
  LorenzGauge coordDeriv A ∧ LorenzGaugeGradient coordDeriv A

/-- Under Lorenz gauge and commuting mixed partials, `partial_mu F^{mu nu} = box A_nu`. -/
lemma partialDiv_faraday_eq_wave_of_lorenzGauge
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (hSub : PartialSubRule coordDeriv) (hGauge : LorenzGaugeClosure coordDeriv A)
    (hSymm : DivergenceMixedPartialSymmetric coordDeriv A) (ν : ι) (x : CoordinateVector ι) :
    partialDivTwoContravariant coordDeriv (coordinateFaradayTensor coordDeriv A) ν x =
      wavePotential coordDeriv A ν x := by
  rcases hGauge with ⟨_, hGaugeGrad⟩
  rw [partialDiv_faraday_eq_wave_sub_gradDiv_of_symmetry
    (coordDeriv := coordDeriv) (A := A) (hSub := hSub) (hSymm := hSymm) ν x]
  rw [hGaugeGrad ν x]
  ring

/-- Inhomogeneous curved Maxwell equation `nabla_mu F^{mu nu} = J^nu`. -/
def MaxwellInhomogeneousCurved
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (F : CoordinateTwoTensor ι) (J : CoordinateCurrent ι) : Prop :=
  ∀ (ν : ι) (x : CoordinateVector ι), covariantDivTwoContravariant coordDeriv Γ F ν x = J x ν

/-- Flat inhomogeneous Maxwell equation `partial_mu F^{mu nu} = J^nu`. -/
def MaxwellInhomogeneousFlatTensor
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (F : CoordinateTwoTensor ι)
    (J : CoordinateCurrent ι) : Prop :=
  ∀ (ν : ι) (x : CoordinateVector ι), partialDivTwoContravariant coordDeriv F ν x = J x ν

/-- Flat inhomogeneous Maxwell equation written through a potential. -/
def MaxwellInhomogeneousFlatPotential
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) (J : CoordinateCurrent ι) : Prop :=
  MaxwellInhomogeneousFlatTensor coordDeriv (coordinateFaradayTensor coordDeriv A) J

/-- Flat wave equation for potential components. -/
def WaveEquationFlatPotential
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) (J : CoordinateCurrent ι) : Prop :=
  ∀ (ν : ι) (x : CoordinateVector ι), wavePotential coordDeriv A ν x = J x ν

/-- The general-coordinate potential equation obtained from `∇_μ F^{μν} = J^ν`
after writing `F = dA`, imposing the coordinate Lorenz-gauge closure, and
commuting the displayed partial derivatives. The Christoffel contribution remains
explicit rather than being discarded. -/
def WaveEquationPotentialWithConnection
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (A : CoordinateOneForm ι) (J : CoordinateCurrent ι) : Prop :=
  ∀ (ν : ι) (x : CoordinateVector ι),
    wavePotential coordDeriv A ν x
        + covariantDivergenceConnectionCorrection Γ
          (coordinateFaradayTensor coordDeriv A) ν x = J x ν

/-- **[Curved Maxwell potential equation with all connection terms retained].** General
inhomogeneous Maxwell, `F = dA`, Lorenz-gauge closure, and the stated mixed-partial symmetry imply
the sourced wave equation plus the exact Christoffel correction. This closes the earlier
flat-connection limitation without claiming that the coordinate correction has already been
repackaged as a metric d'Alembertian plus a Ricci term. -/
lemma curvedMaxwell_implies_waveWithConnection_of_lorenzGauge
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (A : CoordinateOneForm ι) (J : CoordinateCurrent ι)
    (hSub : PartialSubRule coordDeriv)
    (hCurved : MaxwellInhomogeneousCurved coordDeriv Γ
      (coordinateFaradayTensor coordDeriv A) J)
    (hGauge : LorenzGaugeClosure coordDeriv A)
    (hSymm : DivergenceMixedPartialSymmetric coordDeriv A) :
    WaveEquationPotentialWithConnection coordDeriv Γ A J := by
  intro ν x
  have hCov := hCurved ν x
  rw [covariantDivTwoContravariant_eq_partial_add_connectionCorrection,
    partialDiv_faraday_eq_wave_of_lorenzGauge
      (coordDeriv := coordDeriv) (A := A) (hSub := hSub)
      (hGauge := hGauge) (hSymm := hSymm)] at hCov
  exact hCov

/-- With vanishing connection coefficients, curved inhomogeneous Maxwell is
flat Maxwell. -/
lemma maxwellInhomogeneousCurved_of_connectionVanishes_iff_flat
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (F : CoordinateTwoTensor ι) (J : CoordinateCurrent ι) (hΓ : ConnectionVanishes Γ) :
    MaxwellInhomogeneousCurved coordDeriv Γ F J ↔
      MaxwellInhomogeneousFlatTensor coordDeriv F J := by
  constructor
  · intro h ν x
    have hx : covariantDivTwoContravariant coordDeriv Γ F ν x = J x ν := h ν x
    simpa [covariantDivTwoContravariant_eq_partial_of_connectionVanishes
      (coordDeriv := coordDeriv) (Γ := Γ) (F := F) hΓ ν x] using hx
  · intro h ν x
    have hx : partialDivTwoContravariant coordDeriv F ν x = J x ν := h ν x
    simpa [covariantDivTwoContravariant_eq_partial_of_connectionVanishes
      (coordDeriv := coordDeriv) (Γ := Γ) (F := F) hΓ ν x] using hx

/-- Flat Maxwell plus Lorenz gauge and commuting mixed partials imply the wave equation. -/
lemma flatMaxwellPotential_implies_wave_of_lorenzGauge
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) (J : CoordinateCurrent ι)
    (hSub : PartialSubRule coordDeriv)
    (hMaxwell : MaxwellInhomogeneousFlatPotential coordDeriv A J)
    (hGauge : LorenzGaugeClosure coordDeriv A)
    (hSymm : DivergenceMixedPartialSymmetric coordDeriv A) :
    WaveEquationFlatPotential coordDeriv A J := by
  intro ν x
  have hDiv :
      partialDivTwoContravariant coordDeriv (coordinateFaradayTensor coordDeriv A) ν x = J x ν :=
    hMaxwell ν x
  have hWave :
      partialDivTwoContravariant coordDeriv (coordinateFaradayTensor coordDeriv A) ν x =
        wavePotential coordDeriv A ν x :=
    partialDiv_faraday_eq_wave_of_lorenzGauge
      (coordDeriv := coordDeriv) (A := A) (hSub := hSub) (hGauge := hGauge) (hSymm := hSymm) ν x
  calc
    wavePotential coordDeriv A ν x =
        partialDivTwoContravariant coordDeriv (coordinateFaradayTensor coordDeriv A) ν x := by
      simpa using hWave.symm
    _ = J x ν := hDiv

/-- Curved Maxwell on a flat connection, in Lorenz gauge, gives the potential wave equation. -/
lemma curvedMaxwell_flatConnection_implies_wave_of_lorenzGauge
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (A : CoordinateOneForm ι) (J : CoordinateCurrent ι)
    (hSub : PartialSubRule coordDeriv) (hΓ : ConnectionVanishes Γ)
    (hCurved : MaxwellInhomogeneousCurved coordDeriv Γ (coordinateFaradayTensor coordDeriv A) J)
    (hGauge : LorenzGaugeClosure coordDeriv A)
    (hSymm : DivergenceMixedPartialSymmetric coordDeriv A) :
    WaveEquationFlatPotential coordDeriv A J := by
  have hFlat : MaxwellInhomogeneousFlatPotential coordDeriv A J :=
    (maxwellInhomogeneousCurved_of_connectionVanishes_iff_flat
      (coordDeriv := coordDeriv) (Γ := Γ)
      (F := coordinateFaradayTensor coordDeriv A) (J := J) hΓ).1 hCurved
  exact flatMaxwellPotential_implies_wave_of_lorenzGauge
    (coordDeriv := coordDeriv) (A := A) (J := J) hSub hFlat hGauge hSymm

/-- Coordinate Maxwell plus the repository's complex Einstein equation give both
the wave equation and the real/imaginary Einstein split. -/
lemma maxwellWave_and_complexEinstein_split
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (A : CoordinateOneForm ι) (J : CoordinateCurrent ι)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ) (κ : ℝ)
    (hSub : PartialSubRule coordDeriv) (hΓ : ConnectionVanishes Γ)
    (hCurved : MaxwellInhomogeneousCurved coordDeriv Γ (coordinateFaradayTensor coordDeriv A) J)
    (hGauge : LorenzGaugeClosure coordDeriv A)
    (hSymm : DivergenceMixedPartialSymmetric coordDeriv A)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    WaveEquationFlatPotential coordDeriv A J
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  refine ⟨?_, ?_⟩
  · exact curvedMaxwell_flatConnection_implies_wave_of_lorenzGauge
      (coordDeriv := coordDeriv) (Γ := Γ) (A := A) (J := J)
      hSub hΓ hCurved hGauge hSymm
  · exact (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp hEFE

/-- **[General curved Maxwell + complex Einstein split].** The electromagnetic side now retains
the exact Christoffel correction instead of requiring a chart with vanishing connection, while the
existing complex Einstein equation still splits into its real Einstein equation and imaginary
cosmological-sector equation. -/
lemma maxwellWaveWithConnection_and_complexEinstein_split
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (A : CoordinateOneForm ι) (J : CoordinateCurrent ι)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ) (κ : ℝ)
    (hSub : PartialSubRule coordDeriv)
    (hCurved : MaxwellInhomogeneousCurved coordDeriv Γ
      (coordinateFaradayTensor coordDeriv A) J)
    (hGauge : LorenzGaugeClosure coordDeriv A)
    (hSymm : DivergenceMixedPartialSymmetric coordDeriv A)
    (hEFE : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    WaveEquationPotentialWithConnection coordDeriv Γ A J
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  refine ⟨?_, ?_⟩
  · exact curvedMaxwell_implies_waveWithConnection_of_lorenzGauge
      (coordDeriv := coordDeriv) (Γ := Γ) (A := A) (J := J)
      hSub hCurved hGauge hSymm
  · exact (complexEinsteinFieldEquation_iff_einstein Ric scalarR g Λ T S κ).mp hEFE

/-- A coordinate current sampled along a field configuration as a complex path-integral source. -/
def currentSource {α : Type*} (chart : α → CoordinateVector ι)
    (J : CoordinateCurrent ι) (ν : ι) : α → ℂ :=
  fun x => (J (chart x) ν : ℂ)

/-- The connected functional for a coordinate current is the log of the
current-coupled partition. -/
lemma currentConnectedFunctional_eq_log_sourcePartition
    {α : Type*} [MeasurableSpace α] (c : CurvedMeasurePathIntegralModel α)
    (chart : α → CoordinateVector ι) (J : CoordinateCurrent ι) (ν : ι) :
    c.connectedGeneratingFunctional (currentSource chart J ν) =
      Complex.log (c.sourceCoupledPartition (currentSource chart J ν)) := by
  rfl

/-- **[The partition is the exponential of the connected functional]** `Z[J] = e^{W[J]}` on the
nonvanishing locus. The substantive converse of the definitional `W[J] = log Z[J]`: recovering the
partition from the connected functional goes through `Complex.exp_log`, so it holds exactly when the
current-coupled partition does not vanish — the generating identity behind connected-correlator
calculus (`∂W/∂J` = connected one-point, `∂²W/∂J²` = connected two-point). -/
lemma sourcePartition_eq_exp_currentConnectedFunctional
    {α : Type*} [MeasurableSpace α] (c : CurvedMeasurePathIntegralModel α)
    (chart : α → CoordinateVector ι) (J : CoordinateCurrent ι) (ν : ι)
    (h : c.sourceCoupledPartition (currentSource chart J ν) ≠ 0) :
    c.sourceCoupledPartition (currentSource chart J ν) =
      Complex.exp (c.connectedGeneratingFunctional (currentSource chart J ν)) := by
  rw [currentConnectedFunctional_eq_log_sourcePartition, Complex.exp_log h]

/-! ## Coordinate-free Levi-Civita curvature and chart equivalence -/

/-- The bundled coordinate derivative of a Christoffel column is its first
coordinate jet plus the quadratic connection term. -/
lemma coordinateCovariantDerivative_connectionColumn_apply [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (μ ν σ ρ : ι)
    (hΓ : ∀ τ, DifferentiableAt ℝ (fun y => Γ y τ ν σ) x) :
    coordinateCovariantDerivative Γ (fun y τ => Γ y τ ν σ) x
      (Pi.single μ 1) ρ =
      connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x μ ρ ν σ +
        ∑ l, (Γ x ρ) μ l * (Γ x l) ν σ := by
  rw [coordinateCovariantDerivative_apply]
  rw [tangentSectionFDeriv_apply_component (hσ := hΓ)]
  simp [connectionFirstJet, frechetCoordinatePartial, Pi.single_apply,
    Finset.sum_ite_eq']

set_option backward.isDefEq.respectTransparency false in
/-- **Coordinate-free/coordinate curvature equivalence.** The curvature of the
bundled covariant derivative, evaluated on the coordinate basis, is exactly
the existing `riemannFromConnection`; no second curvature carrier is introduced. -/
lemma coordinateCovariantCurvature_basis_eq_riemannFromConnection
    [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (hΓ : ∀ ρ μ σ, DifferentiableAt ℝ (fun y => Γ y ρ μ σ) x)
    (ρ σ μ ν : ι) :
    manifoldCovariantCurvatureAction (coordinateCovariantDerivative Γ)
        (fun _ => Pi.single σ 1) (fun _ => Pi.single μ 1)
        (fun _ => Pi.single ν 1) x ρ =
      riemannFromConnection (Γ x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) ρ σ μ ν := by
  have hcol (a : ι) :
      (fun y => coordinateCovariantDerivative Γ (fun _ => Pi.single σ 1) y
          (Pi.single a 1)) = fun y τ => Γ y τ a σ := by
    funext y τ
    exact coordinateCovariantDerivative_constantBasis_apply Γ y σ a τ
  have hbracket :
      VectorField.mlieBracket (modelWithCornersSelf ℝ (CoordinateVector ι))
        (fun _ => Pi.single μ 1) (fun _ => Pi.single ν 1) x = 0 := by
    rw [← VectorField.mlieBracketWithin_univ]
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    rw [VectorField.lieBracketWithin_univ]
    simp [VectorField.lieBracket]
  unfold manifoldCovariantCurvatureAction
  rw [hcol ν, hcol μ, hbracket, map_zero, sub_zero]
  change coordinateCovariantDerivative Γ (fun y τ => Γ y τ ν σ) x
      (Pi.single μ 1) ρ -
    coordinateCovariantDerivative Γ (fun y τ => Γ y τ μ σ) x
      (Pi.single ν 1) ρ = _
  rw [coordinateCovariantDerivative_connectionColumn_apply Γ x μ ν σ ρ
    (fun τ => hΓ τ ν σ)]
  rw [coordinateCovariantDerivative_connectionColumn_apply Γ x ν μ σ ρ
    (fun τ => hΓ τ μ σ)]
  unfold riemannFromConnection
  ring

/-- Contracting the coordinate-free curvature coefficients gives precisely
the repository's connection-built Ricci tensor. -/
lemma coordinateCovariantCurvature_ricci_eq_ricciFromConnection
    [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (hΓ : ∀ ρ μ σ, DifferentiableAt ℝ (fun y => Γ y ρ μ σ) x)
    (σ ν : ι) :
    (∑ μ, manifoldCovariantCurvatureAction (coordinateCovariantDerivative Γ)
        (fun _ => Pi.single σ 1) (fun _ => Pi.single μ 1)
        (fun _ => Pi.single ν 1) x μ) =
      ricciFromConnection (Γ x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) σ ν := by
  unfold ricciFromConnection
  apply Finset.sum_congr rfl
  intro μ _
  exact coordinateCovariantCurvature_basis_eq_riemannFromConnection Γ x hΓ μ σ μ ν

/-- The coordinate curvature with fixed second and fourth indices, bundled as
an endomorphism. Its matrix is exactly the existing connection-built Riemann
tensor, with output index in the row and contracted input index in the column. -/
noncomputable def coordinateCurvatureEndomorphismAt [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (σ ν : ι) : CoordinateVector ι →ₗ[ℝ] CoordinateVector ι :=
  Matrix.toLin' fun ρ μ =>
    riemannFromConnection (Γ x)
      (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) ρ σ μ ν

set_option backward.isDefEq.respectTransparency false in
/-- On a coordinate basis vector, the bundled curvature endomorphism is the
coordinate-free curvature action of the repository's covariant derivative. -/
lemma coordinateCurvatureEndomorphismAt_basis_apply
    [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (hΓ : ∀ ρ μ σ, DifferentiableAt ℝ (fun y => Γ y ρ μ σ) x)
    (σ μ ν : ι) :
    coordinateCurvatureEndomorphismAt Γ x σ ν (Pi.single μ 1) =
      manifoldCovariantCurvatureAction (coordinateCovariantDerivative Γ)
        (fun _ => Pi.single σ 1) (fun _ => Pi.single μ 1)
        (fun _ => Pi.single ν 1) x := by
  funext ρ
  rw [coordinateCurvatureEndomorphismAt, Matrix.toLin'_apply,
    Matrix.mulVec_single_one,
    coordinateCovariantCurvature_basis_eq_riemannFromConnection Γ x hΓ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The basis-independent linear trace of the coordinate curvature
endomorphism is exactly the existing Ricci contraction. -/
lemma coordinateCurvatureEndomorphismAt_trace_eq_ricciFromConnection
    [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (σ ν : ι) :
    LinearMap.trace ℝ (CoordinateVector ι)
        (coordinateCurvatureEndomorphismAt Γ x σ ν) =
      ricciFromConnection (Γ x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) σ ν := by
  rw [coordinateCurvatureEndomorphismAt,
    LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ ι),
    LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', Matrix.trace]
  simp [Matrix.diag_apply, ricciFromConnection]

/-- The intrinsic Ricci-trace carrier specialized to a coordinate chart is
the repository's coordinate Ricci tensor. This is the exact contraction
bridge between the coordinate-free and coordinate implementations. -/
lemma coordinateCurvatureRicciTrace_eq_ricciFromConnection
    [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (σ ν : ι) :
    PseudoRiemannianMetric.curvatureRicciTraceAt
        (modelWithCornersSelf ℝ (CoordinateVector ι)) x
        (coordinateCurvatureEndomorphismAt Γ x σ ν) =
      ricciFromConnection (Γ x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) σ ν := by
  exact coordinateCurvatureEndomorphismAt_trace_eq_ricciFromConnection Γ x σ ν

/-! ## Trace form of the complete coordinate Maxwell operator -/

/-- Raise one covariant-Hessian index with `gInv`, obtaining the endomorphism
whose linear trace is the coordinate Bochner wave component. -/
noncomputable def coordinateBochnerEndomorphismAt [Fintype ι] [DecidableEq ι]
    (gInv : Matrix ι ι ℝ) (nabla2V : ι → ι → ι → ℝ) (ν : ι) :
    CoordinateVector ι →ₗ[ℝ] CoordinateVector ι :=
  Matrix.toLin' (gInv * Matrix.of fun μ α => nabla2V μ α ν)

/-- For a symmetric inverse metric, the linear trace of the raised Hessian
endomorphism is exactly the existing coordinate vector wave operator. -/
lemma coordinateBochnerEndomorphismAt_trace_eq_wave
    [Fintype ι] [DecidableEq ι]
    (gInv : Matrix ι ι ℝ) (nabla2V : ι → ι → ι → ℝ) (ν : ι)
    (hgi : Matrix.transpose gInv = gInv) :
    LinearMap.trace ℝ (CoordinateVector ι)
        (coordinateBochnerEndomorphismAt gInv nabla2V ν) =
      covariantVectorWaveAt gInv nabla2V ν := by
  rw [coordinateBochnerEndomorphismAt,
    LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ ι),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.trace]
  unfold covariantVectorWaveAt
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro α _
  have hs := congrFun (congrFun hgi μ) α
  simp only [Matrix.transpose_apply] at hs
  rw [← hs]

/-- The Ricci action written solely as traces of the coordinate curvature
endomorphisms. -/
noncomputable def coordinateRicciTraceActionAt [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (V : ι → ℝ) (ν : ι) : ℝ :=
  ∑ σ, LinearMap.trace ℝ (CoordinateVector ι)
    (coordinateCurvatureEndomorphismAt Γ x σ ν) * V σ

/-- The curvature-trace action is the repository's existing
`ricciActionAt`. -/
lemma coordinateRicciTraceActionAt_eq_ricciActionAt
    [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (V : ι → ℝ) (ν : ι) :
    coordinateRicciTraceActionAt Γ x V ν =
      ricciActionAt (Γ x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) V ν := by
  unfold coordinateRicciTraceActionAt ricciActionAt
  apply Finset.sum_congr rfl
  intro σ _
  rw [coordinateCurvatureEndomorphismAt_trace_eq_ricciFromConnection]

/-- Raise the trace-defined Ricci covector with the inverse metric. -/
noncomputable def coordinateRaisedRicciTraceActionAt
    [Fintype ι] [DecidableEq ι]
    (gInv : Matrix ι ι ℝ)
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (V : ι → ℝ) (ν : ι) : ℝ :=
  ∑ α, gInv ν α * coordinateRicciTraceActionAt Γ x V α

/-- Raising after curvature trace gives the existing raised Ricci action. -/
lemma coordinateRaisedRicciTraceActionAt_eq_raisedRicciActionAt
    [Fintype ι] [DecidableEq ι]
    (gInv : Matrix ι ι ℝ)
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (V : ι → ℝ) (ν : ι) :
    coordinateRaisedRicciTraceActionAt gInv Γ x V ν =
      raisedRicciActionAt gInv (Γ x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) V ν := by
  unfold coordinateRaisedRicciTraceActionAt raisedRicciActionAt
  apply Finset.sum_congr rfl
  intro α _
  rw [coordinateRicciTraceActionAt_eq_ricciActionAt]

/-- **Complete chart-equivalence theorem.** The existing coordinate
Ricci-coupled Maxwell equation is exactly the equation obtained by subtracting
the raised curvature trace from the Bochner trace. Thus both contractions are
basis-independent linear traces even though the right-hand presentation uses
chart components. -/
lemma ricciCoupledVectorWaveEquationAt_iff_traceContractions
    [Fintype ι] [DecidableEq ι]
    (gInv : Matrix ι ι ℝ)
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ) (x : CoordinateVector ι)
    (V J : ι → ℝ) (nabla2V : ι → ι → ι → ℝ)
    (hgi : Matrix.transpose gInv = gInv) :
    RicciCoupledVectorWaveEquationAt gInv (Γ x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) V J nabla2V ↔
      ∀ ν, LinearMap.trace ℝ (CoordinateVector ι)
          (coordinateBochnerEndomorphismAt gInv nabla2V ν) -
        coordinateRaisedRicciTraceActionAt gInv Γ x V ν = J ν := by
  constructor
  · intro h ν
    rw [coordinateBochnerEndomorphismAt_trace_eq_wave gInv nabla2V ν hgi]
    rw [coordinateRaisedRicciTraceActionAt_eq_raisedRicciActionAt]
    exact h ν
  · intro h ν
    rw [← coordinateBochnerEndomorphismAt_trace_eq_wave gInv nabla2V ν hgi]
    rw [← coordinateRaisedRicciTraceActionAt_eq_raisedRicciActionAt]
    exact h ν

/-- The pointwise trace equivalence assembles over the whole coordinate
domain. This is the chart-level endpoint used by the intrinsic open-cover
theorem: no preferred frame occurs on the right-hand side. -/
lemma ricciCoupledVectorWaveEquationOnChart_iff_traceContractions
    [Fintype ι] [DecidableEq ι]
    (gInv : CoordinateVector ι → Matrix ι ι ℝ)
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ)
    (V J : CoordinateVector ι → ι → ℝ)
    (nabla2V : CoordinateVector ι → ι → ι → ι → ℝ)
    (hgi : ∀ x, Matrix.transpose (gInv x) = gInv x) :
    RicciCoupledVectorWaveEquationOnChart gInv Γ
        (fun x => connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x)
        V J nabla2V ↔
      ∀ x ν, LinearMap.trace ℝ (CoordinateVector ι)
          (coordinateBochnerEndomorphismAt (gInv x) (nabla2V x) ν) -
        coordinateRaisedRicciTraceActionAt (gInv x) Γ x (V x) ν = J x ν := by
  constructor
  · intro h x
    exact (ricciCoupledVectorWaveEquationAt_iff_traceContractions
      (gInv x) Γ x (V x) (J x) (nabla2V x) (hgi x)).mp (h x)
  · intro h x
    exact (ricciCoupledVectorWaveEquationAt_iff_traceContractions
      (gInv x) Γ x (V x) (J x) (nabla2V x) (hgi x)).mpr (h x)

/-! ## Ricci contraction and the algebraic Bianchi identity -/

/-- A torsion-free connection and a lower-index-symmetric connection jet obey
the first algebraic Bianchi identity. -/
lemma riemannFromConnection_firstBianchi [Fintype ι]
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (hΓ : IsTorsionFree Γ)
    (hdΓ : ∀ κ ρ, Matrix.transpose (dΓ κ ρ) = dΓ κ ρ) :
    FirstBianchi (riemannFromConnection Γ dΓ) := by
  intro ρ σ μ ν
  have hd1 : (dΓ ν ρ) σ μ = (dΓ ν ρ) μ σ := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hdΓ ν ρ) μ) σ
  have hd2 : (dΓ σ ρ) μ ν = (dΓ σ ρ) ν μ := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hdΓ σ ρ) ν) μ
  have hd3 : (dΓ μ ρ) σ ν = (dΓ μ ρ) ν σ := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hdΓ μ ρ) ν) σ
  have hq1 : (∑ l, (Γ ρ) ν l * (Γ l) σ μ) =
      ∑ l, (Γ ρ) ν l * (Γ l) μ σ := by
    apply Finset.sum_congr rfl
    intro l _
    have h := congrFun (congrFun (hΓ l) μ) σ
    simp only [Matrix.transpose_apply] at h
    rw [h]
  have hq2 : (∑ l, (Γ ρ) σ l * (Γ l) μ ν) =
      ∑ l, (Γ ρ) σ l * (Γ l) ν μ := by
    apply Finset.sum_congr rfl
    intro l _
    have h := congrFun (congrFun (hΓ l) ν) μ
    simp only [Matrix.transpose_apply] at h
    rw [h]
  have hq3 : (∑ l, (Γ ρ) μ l * (Γ l) σ ν) =
      ∑ l, (Γ ρ) μ l * (Γ l) ν σ := by
    apply Finset.sum_congr rfl
    intro l _
    have h := congrFun (congrFun (hΓ l) ν) σ
    simp only [Matrix.transpose_apply] at h
    rw [h]
  unfold riemannFromConnection
  rw [hd1, hd2, hd3, hq1, hq2, hq3]
  ring

/-- Differentiating a pointwise torsion-free Christoffel field preserves the
symmetry of its two lower connection indices. -/
lemma connectionFirstJet_transpose_eq_of_torsionFree
    (coordDeriv : CoordinatePartial ι)
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ)
    (hΓ : ∀ x, IsTorsionFree (Γ x)) (x : CoordinateVector ι) (κ ρ : ι) :
    Matrix.transpose (connectionFirstJet coordDeriv Γ x κ ρ) =
      connectionFirstJet coordDeriv Γ x κ ρ := by
  ext μ ν
  simp only [Matrix.transpose_apply, connectionFirstJet, Matrix.of_apply]
  apply congrArg (fun f : CoordinateVector ι → ℝ => coordDeriv f κ x)
  funext y
  simpa [Matrix.transpose_apply] using (congrFun (congrFun (hΓ y ρ) ν) μ).symm

/-- The coordinate-free curvature of a torsion-free bundled chart connection
obeys the first Bianchi identity on the coordinate basis. -/
lemma coordinateCovariantCurvature_firstBianchi [Fintype ι] [DecidableEq ι]
    (Γ : CoordinateVector ι → ι → Matrix ι ι ℝ)
    (hΓdiff : ∀ x ρ μ σ, DifferentiableAt ℝ (fun y => Γ y ρ μ σ) x)
    (hΓtor : ∀ x, IsTorsionFree (Γ x)) (x : CoordinateVector ι) :
    FirstBianchi (fun ρ σ μ ν =>
      manifoldCovariantCurvatureAction (coordinateCovariantDerivative Γ)
        (fun _ => Pi.single σ 1) (fun _ => Pi.single μ 1)
        (fun _ => Pi.single ν 1) x ρ) := by
  have hFB := riemannFromConnection_firstBianchi (Γ x)
    (connectionFirstJet (frechetCoordinatePartial (ι := ι)) Γ x) (hΓtor x)
    (connectionFirstJet_transpose_eq_of_torsionFree
      (frechetCoordinatePartial (ι := ι)) Γ hΓtor x)
  intro ρ σ μ ν
  simp only
  rw [coordinateCovariantCurvature_basis_eq_riemannFromConnection Γ x
    (hΓdiff x) ρ σ μ ν]
  rw [coordinateCovariantCurvature_basis_eq_riemannFromConnection Γ x
    (hΓdiff x) ρ μ ν σ]
  rw [coordinateCovariantCurvature_basis_eq_riemannFromConnection Γ x
    (hΓdiff x) ρ ν σ μ]
  exact hFB ρ σ μ ν

/-! ## Bundled geometric Maxwell chain -/

/-- **Bundled geometric curved-Maxwell chain.** Smooth metric data construct a
torsion-free Mathlib covariant derivative. Its coordinate-free curvature has
the repository's Ricci contraction and first Bianchi identity, while the same
connection gives the general Ricci-coupled Maxwell wave equation on the chart.

The connection-component differentiability premise is the regularity needed
to evaluate the Fréchet curvature. It does not assume a curvature equation. -/
lemma contDiffMetricFieldMaxwell_bundledGeometry_onChart
    [Fintype ι] [DecidableEq ι]
    (g gInv : CoordinateVector ι → Matrix ι ι ℝ)
    (V J : CoordinateVector ι → ι → ℝ)
    (hg : ∀ x, Matrix.transpose (g x) = g x)
    (hgi : ∀ x, Matrix.transpose (gInv x) = gInv x)
    (hinv : ∀ x, gInv x * g x = 1)
    (hΓdiff : ∀ x ρ μ σ, DifferentiableAt ℝ
      (fun y => leviCivitaConnectionField
        (frechetCoordinatePartial (ι := ι)) g gInv y ρ μ σ) x)
    (hV : ∀ ρ, ContDiff ℝ 2 (fun x => V x ρ))
    (hMaxwell : ∀ x, GeometricMaxwellInhomogeneousAt (gInv x)
      (leviCivitaSecondDerivVectorField
        (frechetCoordinatePartial (ι := ι)) g gInv V x) (J x))
    (hGauge : ∀ x, CovariantLorenzGaugeGradientAt (gInv x)
      (leviCivitaSecondDerivVectorField
        (frechetCoordinatePartial (ι := ι)) g gInv V x)) :
    (metricLeviCivitaCovariantDerivative gInv
      (metricFirstJet (frechetCoordinatePartial (ι := ι)) g)).torsion = 0
      ∧ (∀ x σ ν,
        (∑ μ, manifoldCovariantCurvatureAction
          (metricLeviCivitaCovariantDerivative gInv
            (metricFirstJet (frechetCoordinatePartial (ι := ι)) g))
          (fun _ => Pi.single σ 1) (fun _ => Pi.single μ 1)
          (fun _ => Pi.single ν 1) x μ) =
        ricciFromConnection
          (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv x)
          (connectionFirstJet (frechetCoordinatePartial (ι := ι))
            (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv) x)
          σ ν)
      ∧ (∀ x, FirstBianchi (fun ρ σ μ ν =>
        manifoldCovariantCurvatureAction
          (metricLeviCivitaCovariantDerivative gInv
            (metricFirstJet (frechetCoordinatePartial (ι := ι)) g))
          (fun _ => Pi.single σ 1) (fun _ => Pi.single μ 1)
          (fun _ => Pi.single ν 1) x ρ))
      ∧ ((∀ x, IsMetricCompatible
        (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv x)
        (metricFirstJet (frechetCoordinatePartial (ι := ι)) g x) (g x))
        ∧ RicciCoupledVectorWaveEquationOnChart gInv
          (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv)
          (fun x => connectionFirstJet (frechetCoordinatePartial (ι := ι))
            (leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv) x)
          V J (leviCivitaSecondDerivVectorField
            (frechetCoordinatePartial (ι := ι)) g gInv V)) := by
  let Γ := leviCivitaConnectionField (frechetCoordinatePartial (ι := ι)) g gInv
  have hjet : ∀ x κ,
      Matrix.transpose (metricFirstJet (frechetCoordinatePartial (ι := ι)) g x κ) =
        metricFirstJet (frechetCoordinatePartial (ι := ι)) g x κ :=
    metricFirstJet_transpose_eq (frechetCoordinatePartial (ι := ι)) g hg
  have htor : ∀ x, IsTorsionFree (Γ x) := by
    intro x
    exact christoffelFromMetric_isTorsionFree (gInv x)
      (metricFirstJet (frechetCoordinatePartial (ι := ι)) g x) (hjet x)
  constructor
  · exact metricLeviCivitaCovariantDerivative_torsion_eq_zero gInv
      (metricFirstJet (frechetCoordinatePartial (ι := ι)) g) hjet
  constructor
  · intro x σ ν
    exact coordinateCovariantCurvature_ricci_eq_ricciFromConnection Γ x
      (hΓdiff x) σ ν
  constructor
  · intro x
    exact coordinateCovariantCurvature_firstBianchi Γ hΓdiff htor x
  · exact contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart
      g gInv V J hg hgi hinv hV hMaxwell hGauge

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein

end
