/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
public import Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.PosDef
meta import Zil

/-!
# Yang-Mills gauge dynamics

This module adds the non-Abelian gauge-field dynamics layer requested by the
Wilson/Chern-Simons path-integral work:

* the Yang-Mills curvature
  `F_{mu nu} = partial_mu A_nu - partial_nu A_mu + [A_mu,A_nu]`;
* the gauge transformation of a connection
  `A_mu ↦ U A_mu U⁻¹ + U partial_mu U⁻¹`;
* the adjoint transformation of curvature/current
  `F_{mu nu} ↦ U F_{mu nu} U⁻¹`, `J_nu ↦ U J_nu U⁻¹`;
* the equation of motion
  `D_mu F^{mu nu} = J^nu`, with
  `D_mu F^{mu nu} = partial_mu F^{mu nu} + [A_mu,F^{mu nu}]`;
* gauge covariance of the equation, conditional on the standard covariance
  identity for the covariant divergence;
* the Abelian/commutative reduction to the repository's existing coordinate
  Maxwell equation `partial_mu F^{mu nu}=J^nu`.

The file deliberately separates three layers:

1. algebraic identities Lean proves directly;
2. gauge-covariance obligations (`GaugeCurvatureCovariant`,
   `GaugeCovariantDivergence`) that are normally proved from product-rule and
   inverse-derivative identities for the chosen field class;
3. existing Maxwell infrastructure, reused as the commutative shadow.

## Local source anchors

Local files inspected under `Downloads`:

* `stationary-points-yangmill-action-gauge-sadun1992.pdf` — first page states
  the Yang-Mills variational equations in the form
  `partial^mu F_{mu nu} + [A^mu,F_{mu nu}] = 0`.
* `Yang-Mills extension of the Loop Quantum Gravity-corrected Maxwell equations-2408.10366v3.pdf`
  — explicitly motivates the Abelian Maxwell to non-Abelian Yang-Mills
  extension.
* `The action of a general gauge field theory- Minimum or stationary -bishop1986.pdf`
  — gauge action/stationarity source context.


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics

open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein

variable {X ι 𝔤 : Type*}


/-- A gauge potential/connection one-form in coordinates. -/
abbrev GaugePotential (X ι 𝔤 : Type*) := X → ι → 𝔤

/-- A gauge curvature/field-strength two-tensor in coordinates. -/
abbrev GaugeCurvature (X ι 𝔤 : Type*) := X → ι → ι → 𝔤

/-- A gauge current. -/
abbrev GaugeCurrent (X ι 𝔤 : Type*) := X → ι → 𝔤

/-- Abstract coordinate derivative acting componentwise on gauge-algebra valued
fields. -/
abbrev GaugePartial (X ι 𝔤 : Type*) := (X → 𝔤) → ι → X → 𝔤

/-- Yang-Mills field strength
`F_{mu nu}=partial_mu A_nu-partial_nu A_mu+[A_mu,A_nu]`. -/
def yangMillsCurvature [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (A : GaugePotential X ι 𝔤) :
    GaugeCurvature X ι 𝔤 :=
  fun x μ ν =>
    deriv (fun y => A y ν) μ x
      - deriv (fun y => A y μ) ν x
      + ⁅A x μ, A x ν⁆

/-- Matrix-valued Yang-Mills curvature written with the existing gluon Lie
bracket.  This is the concrete bridge from the gauge-field dynamics layer to
the repository's non-Abelian gluon self-interaction infrastructure. -/
lemma yangMillsCurvature_matrix_eq_dA_plus_gluonLieBracket {n : ℕ}
    (deriv : GaugePartial X ι (Matrix (Fin n) (Fin n) ℂ))
    (A : GaugePotential X ι (Matrix (Fin n) (Fin n) ℂ))
    (x : X) (μ ν : ι) :
    yangMillsCurvature deriv A x μ ν =
      deriv (fun y => A y ν) μ x - deriv (fun y => A y μ) ν x + ⁅A x μ, A x ν⁆ := by
  rfl

/-- The Yang-Mills curvature is antisymmetric in its two indices. -/
lemma yangMillsCurvature_antisymm [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (A : GaugePotential X ι 𝔤)
    (x : X) (μ ν : ι) :
    yangMillsCurvature deriv A x μ ν =
      -yangMillsCurvature deriv A x ν μ := by
  simp [yangMillsCurvature, Ring.lie_def]
  noncomm_ring

/-- In the Abelian/commutative case the Yang-Mills curvature is just `dA`. -/
lemma yangMillsCurvature_eq_exteriorDerivative_of_comm [CommRing 𝔤]
    (deriv : GaugePartial X ι 𝔤) (A : GaugePotential X ι 𝔤)
    (x : X) (μ ν : ι) :
    yangMillsCurvature deriv A x μ ν =
      deriv (fun y => A y ν) μ x - deriv (fun y => A y μ) ν x := by
  simp [yangMillsCurvature, Ring.lie_def, mul_comm]


/-- Gauge-adjoint action `phi ↦ U phi U⁻¹`.  The caller supplies `Uinv`,
which is normally the pointwise inverse of `U`. -/
def gaugeAdjoint [Mul 𝔤] (U Uinv : X → 𝔤) (φ : X → 𝔤) : X → 𝔤 :=
  fun x => U x * φ x * Uinv x

/-- Gauge transformation of the connection:
`A_mu ↦ U A_mu U⁻¹ + U partial_mu U⁻¹`. -/
def gaugeTransformPotential [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (U Uinv : X → 𝔤)
    (A : GaugePotential X ι 𝔤) : GaugePotential X ι 𝔤 :=
  fun x μ => U x * A x μ * Uinv x + U x * deriv Uinv μ x

@[simp]
lemma gaugeTransformPotential_apply [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (U Uinv : X → 𝔤)
    (A : GaugePotential X ι 𝔤) (x : X) (μ : ι) :
    gaugeTransformPotential deriv U Uinv A x μ =
      U x * A x μ * Uinv x + U x * deriv Uinv μ x :=
  rfl

/-- Gauge transformation of curvature: `F_{mu nu} ↦ U F_{mu nu} U⁻¹`. -/
def gaugeTransformCurvature [Mul 𝔤]
    (U Uinv : X → 𝔤) (F : GaugeCurvature X ι 𝔤) :
    GaugeCurvature X ι 𝔤 :=
  fun x μ ν => gaugeAdjoint U Uinv (fun y => F y μ ν) x

/-- Gauge transformation of current: `J_nu ↦ U J_nu U⁻¹`. -/
def gaugeTransformCurrent [Mul 𝔤]
    (U Uinv : X → 𝔤) (J : GaugeCurrent X ι 𝔤) :
    GaugeCurrent X ι 𝔤 :=
  fun x ν => gaugeAdjoint U Uinv (fun y => J y ν) x

@[simp]
lemma gaugeTransformCurvature_apply [Mul 𝔤]
    (U Uinv : X → 𝔤) (F : GaugeCurvature X ι 𝔤)
    (x : X) (μ ν : ι) :
    gaugeTransformCurvature U Uinv F x μ ν = U x * F x μ ν * Uinv x :=
  rfl

@[simp]
lemma gaugeTransformCurrent_apply [Mul 𝔤]
    (U Uinv : X → 𝔤) (J : GaugeCurrent X ι 𝔤)
    (x : X) (ν : ι) :
    gaugeTransformCurrent U Uinv J x ν = U x * J x ν * Uinv x :=
  rfl

/-- The standard curvature covariance obligation:
`F[A^U] = U F[A] U⁻¹`.

For concrete smooth matrix-valued fields this follows from the Leibniz rule and
`partial_mu(U⁻¹)=-U⁻¹(partial_mu U)U⁻¹`.  It is kept explicit here because
those analytic/smooth-field hypotheses live in the chosen realization. -/
def GaugeCurvatureCovariant [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (U Uinv : X → 𝔤)
    (A : GaugePotential X ι 𝔤) : Prop :=
  ∀ (μ ν : ι) (x : X),
    yangMillsCurvature deriv (gaugeTransformPotential deriv U Uinv A) x μ ν =
      gaugeTransformCurvature U Uinv (yangMillsCurvature deriv A) x μ ν


/-- Covariant derivative of the curvature component:
`D_mu F^{mu nu}=partial_mu F^{mu nu}+[A_mu,F^{mu nu}]`. -/
def yangMillsCovariantDerivativeCurvature [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤)
    (μ ν : ι) (x : X) : 𝔤 :=
  deriv (fun y => F y μ ν) μ x + ⁅A x μ, F x μ ν⁆

/-- Yang-Mills covariant divergence `D_mu F^{mu nu}`. -/
def yangMillsDivergence [Fintype ι] [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤)
    (ν : ι) (x : X) : 𝔤 :=
  ∑ μ : ι, yangMillsCovariantDerivativeCurvature deriv A F μ ν x

/-- Yang-Mills equation of motion `D_mu F^{mu nu}=J^nu`. -/
def YangMillsEquation [Fintype ι] [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤)
    (J : GaugeCurrent X ι 𝔤) : Prop :=
  ∀ (ν : ι) (x : X), yangMillsDivergence deriv A F ν x = J x ν

/-- Yang-Mills equation with the curvature constrained to be the curvature of
the connection: `D_mu F[A]^{mu nu}=J^nu`. -/
def YangMillsPotentialEquation [Fintype ι] [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤)
    (A : GaugePotential X ι 𝔤) (J : GaugeCurrent X ι 𝔤) : Prop :=
  YangMillsEquation deriv A (yangMillsCurvature deriv A) J

/-- Gauge covariance of the covariant divergence:
`D[A^U]_mu (U F U⁻¹)^{mu nu}=U(D[A]_mu F^{mu nu})U⁻¹`. -/
def GaugeCovariantDivergence [Fintype ι] [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (U Uinv : X → 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤) : Prop :=
  ∀ (ν : ι) (x : X),
    yangMillsDivergence deriv
        (gaugeTransformPotential deriv U Uinv A)
        (gaugeTransformCurvature U Uinv F) ν x =
      gaugeAdjoint U Uinv (fun y => yangMillsDivergence deriv A F ν y) x

/-- If the covariant divergence transforms adjointly and the current transforms
adjointly, then the Yang-Mills equation is gauge invariant. -/
lemma yangMillsEquation_gauge_covariant [Fintype ι] [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (U Uinv : X → 𝔤)
    (A : GaugePotential X ι 𝔤) (F : GaugeCurvature X ι 𝔤)
    (J : GaugeCurrent X ι 𝔤)
    (hCov : GaugeCovariantDivergence deriv U Uinv A F)
    (hYM : YangMillsEquation deriv A F J) :
    YangMillsEquation deriv
      (gaugeTransformPotential deriv U Uinv A)
      (gaugeTransformCurvature U Uinv F)
      (gaugeTransformCurrent U Uinv J) := by
  intro ν x
  rw [hCov ν x]
  simp [gaugeAdjoint, gaugeTransformCurrent, hYM ν x]

/-- Gauge covariance of the potential form of Yang-Mills.  This is the usual
statement that `D_mu F[A]^{mu nu}=J^nu` is preserved by
`A↦UAU⁻¹+UdU⁻¹`, provided curvature and divergence covariance are available
for the chosen smooth field class. -/
lemma yangMillsPotentialEquation_gauge_covariant [Fintype ι] [Ring 𝔤]
    (deriv : GaugePartial X ι 𝔤) (U Uinv : X → 𝔤)
    (A : GaugePotential X ι 𝔤) (J : GaugeCurrent X ι 𝔤)
    (hF : GaugeCurvatureCovariant deriv U Uinv A)
    (hDiv : GaugeCovariantDivergence deriv U Uinv A (yangMillsCurvature deriv A))
    (hYM : YangMillsPotentialEquation deriv A J) :
    YangMillsPotentialEquation deriv
      (gaugeTransformPotential deriv U Uinv A)
      (gaugeTransformCurrent U Uinv J) := by
  intro ν x
  have hFext :
      yangMillsCurvature deriv (gaugeTransformPotential deriv U Uinv A) =
        gaugeTransformCurvature U Uinv (yangMillsCurvature deriv A) := by
    funext x μ ν
    exact hF μ ν x
  rw [hFext]
  exact yangMillsEquation_gauge_covariant
    (deriv := deriv) (U := U) (Uinv := Uinv)
    (A := A) (F := yangMillsCurvature deriv A) (J := J) hDiv hYM ν x


/-- The real/Abelian Yang-Mills curvature is exactly the repository's
coordinate Faraday tensor. -/
lemma yangMillsCurvature_real_eq_coordinateFaradayTensor
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) :
    yangMillsCurvature (X := CoordinateVector ι) (ι := ι) (𝔤 := ℝ) coordDeriv A =
      coordinateFaradayTensor coordDeriv A := by
  funext x μ ν
  simp [yangMillsCurvature, coordinateFaradayTensor, Ring.lie_def, mul_comm]

/-- The real/Abelian Yang-Mills divergence is the flat Maxwell divergence. -/
lemma yangMillsDivergence_real_eq_partialDiv [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (F : CoordinateTwoTensor ι) (ν : ι) (x : CoordinateVector ι) :
    yangMillsDivergence (X := CoordinateVector ι) (ι := ι) (𝔤 := ℝ)
      coordDeriv A F ν x =
        partialDivTwoContravariant coordDeriv F ν x := by
  simp [yangMillsDivergence, yangMillsCovariantDerivativeCurvature,
    partialDivTwoContravariant, Ring.lie_def, mul_comm]

/-- The commutative/real Yang-Mills equation is exactly flat inhomogeneous
Maxwell in the existing coordinate Maxwell API. -/
lemma yangMillsPotentialEquation_real_iff_maxwellFlatPotential [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (J : CoordinateCurrent ι) :
    YangMillsPotentialEquation (X := CoordinateVector ι) (ι := ι) (𝔤 := ℝ)
      coordDeriv A J ↔
        MaxwellInhomogeneousFlatPotential coordDeriv A J := by
  constructor
  · intro h ν x
    specialize h ν x
    simpa [YangMillsPotentialEquation, YangMillsEquation,
      MaxwellInhomogeneousFlatPotential, MaxwellInhomogeneousFlatTensor,
      yangMillsDivergence, yangMillsCovariantDerivativeCurvature,
      partialDivTwoContravariant, yangMillsCurvature, coordinateFaradayTensor,
      Ring.lie_def, mul_comm] using h
  · intro h ν x
    specialize h ν x
    simpa [YangMillsPotentialEquation, YangMillsEquation,
      MaxwellInhomogeneousFlatPotential, MaxwellInhomogeneousFlatTensor,
      yangMillsDivergence, yangMillsCovariantDerivativeCurvature,
      partialDivTwoContravariant, yangMillsCurvature, coordinateFaradayTensor,
      Ring.lie_def, mul_comm] using h

/-- In the momentum-space Abelian specialization, Yang-Mills current
conservation is exactly the existing Maxwell continuity theorem. -/
lemma yangMills_momentumAbelian_current_conserved
    (k A : Fin 4 → ℝ) (x : CoordinateVector (Fin 4)) :
    (∑ ν : Fin 4,
      k ν * yangMillsDivergence
        (X := CoordinateVector (Fin 4)) (ι := Fin 4) (𝔤 := ℝ)
        (momentumCoordinatePartial k)
        (constantCoordinatePotential A)
        (yangMillsCurvature
          (X := CoordinateVector (Fin 4)) (ι := Fin 4) (𝔤 := ℝ)
          (momentumCoordinatePartial k)
          (constantCoordinatePotential A)) ν x) = 0 := by
  simpa [yangMillsDivergence, yangMillsCovariantDerivativeCurvature,
    yangMillsCurvature, Ring.lie_def, partialDivTwoContravariant,
    coordinateFaradayTensor, momentumCoordinatePartial, constantCoordinatePotential,
    mul_comm] using partialDiv_momentumCoordinateFaraday_conserved k A x


/-! ### The Yang-Mills action and its gauge invariance -/

/-- **[The Yang-Mills action is gauge invariant] `Tr((U F U⁻¹)²) = Tr(F²)`.** Under a gauge transformation
`F ↦ U F U⁻¹` (adjoint action, with `V = U⁻¹`), the trace of `F²` is invariant — the trace's cyclicity
together with `V U = 1` cancels the conjugation. This is *why* the Yang-Mills action `−¼ Tr(F²)` is
well defined. -/
lemma trace_conj_sq_eq {n : ℕ} (F U V : Matrix (Fin n) (Fin n) ℂ) (h : U * V = 1) :
    ((U * F * V) * (U * F * V)).trace = (F * F).trace := by
  have hVU : V * U = 1 := mul_eq_one_comm.mp h
  have step1 : (U * F * V) * (U * F * V) = U * (F * V * U * F) * V := by
    simp only [Matrix.mul_assoc]
  rw [step1, Matrix.trace_mul_cycle, hVU, Matrix.one_mul, Matrix.mul_assoc F V U, hVU,
    Matrix.mul_one]

/-- **The Yang-Mills Lagrangian density** `L = −¼ Tr(F_{μν} F^{μν})` — the gauge-invariant scalar built
from the matrix-valued field strength. -/
noncomputable def yangMillsLagrangianDensity {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  -(1 / 4) * (F * F).trace

/-- **[Gauge invariance of the Yang-Mills Lagrangian] `L[U F U⁻¹] = L[F]`.** The `−¼ Tr(F²)` density is
unchanged by an adjoint gauge transformation of the curvature. -/
lemma yangMillsLagrangianDensity_gauge_invariant {n : ℕ}
    (F U V : Matrix (Fin n) (Fin n) ℂ) (h : U * V = 1) :
    yangMillsLagrangianDensity (U * F * V) = yangMillsLagrangianDensity F := by
  unfold yangMillsLagrangianDensity
  rw [trace_conj_sq_eq F U V h]


open scoped Matrix ComplexOrder

/-! ### The Yang-Mills action is bounded below -/

/-- **The Yang-Mills energy density** `‖F‖² = Tr(Fᴴ F)` — the Hilbert–Schmidt (Frobenius) norm² of the
matrix-valued field strength, the Euclidean Yang-Mills action density `¼ Tr(F_{μν}F^{μν})` written with the
Hermitian conjugate so as to be manifestly real and non-negative. -/
noncomputable def yangMillsEnergyDensity {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (Fᴴ * F).trace

/-- **[The Yang-Mills action is bounded below] `0 ≤ Tr(Fᴴ F)`.** The energy density is the trace of the
positive-semidefinite matrix `Fᴴ F`, hence non-negative: the Yang-Mills action has a stable vacuum, its
minimum (zero) reached exactly at vanishing field strength. This is the positivity that makes the theory's
dynamics well posed. -/
lemma yangMillsEnergyDensity_nonneg {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ yangMillsEnergyDensity F :=
  (Matrix.posSemidef_conjTranspose_mul_self F).trace_nonneg

/-- **[Gauge invariance of the Yang-Mills energy] `Tr((U F Uᴴ)ᴴ (U F Uᴴ)) = Tr(Fᴴ F)`** for unitary `U`
(`Uᴴ U = 1`). The Hilbert–Schmidt norm of the field strength is unchanged by a unitary gauge transformation
— the energy density is gauge invariant, so the non-negativity bound is gauge independent. -/
lemma yangMillsEnergyDensity_gauge_invariant {n : ℕ}
    (F U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    yangMillsEnergyDensity (U * F * Uᴴ) = yangMillsEnergyDensity F := by
  unfold yangMillsEnergyDensity
  have key : (U * F * Uᴴ)ᴴ * (U * F * Uᴴ) = U * (Fᴴ * F) * Uᴴ := by
    have h1 : (U * F * Uᴴ)ᴴ = U * Fᴴ * Uᴴ := by
      simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [h1]
    calc U * Fᴴ * Uᴴ * (U * F * Uᴴ)
        = U * Fᴴ * (Uᴴ * U) * F * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Fᴴ * 1 * F * Uᴴ := by rw [hU]
      _ = U * (Fᴴ * F) * Uᴴ := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [key, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

end Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsLagrangianDensity_gauge_invariant where
  formalizes @ "claim:the-yang-mills-lagrangian-density-minus-one-quarter-trace-f-squared-is-invariant-under-adjoint-gauge-transformations",
  supported_by @ "paper:yang-mills-1954-isotopic-spin-gauge-invariance"

zil attach Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsEnergyDensity_nonneg where
  formalizes @ "claim:the-yang-mills-action-density-trace-of-f-hermitian-times-f-is-non-negative-so-the-action-is-bounded-below-with-a-stable-vacuum",
  supported_by @ "paper:yang-mills-1954-isotopic-spin-gauge-invariance"

zil attach Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsEnergyDensity_gauge_invariant where
  formalizes @ "claim:the-yang-mills-energy-density-is-invariant-under-a-unitary-gauge-transformation-so-the-non-negativity-bound-is-gauge-independent",
  requires @ "claim:the-yang-mills-action-density-trace-of-f-hermitian-times-f-is-non-negative-so-the-action-is-bounded-below-with-a-stable-vacuum"

zil_file_contract physlib.yangMillsGaugeDynamics where
  promises "Non-abelian Yang-Mills gauge dynamics at the algebraic level: the Lagrangian density minus one quarter trace of F squared is invariant under adjoint gauge transformations; the Yang-Mills action density, the trace of F-Hermitian times F, is non-negative so the action is bounded below with a stable vacuum; and that energy density is invariant under unitary gauge transformations, making the positivity bound gauge independent."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsCurvature",
    "lean:Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsLagrangianDensity",
    "lean:Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsEnergyDensity"]
  forbids_substitutes ["a first-principles derivation of the Yang-Mills equations of motion from a variational principle, only the algebraic action identities are carried",
    "a proof of the Yang-Mills mass gap, which is not addressed"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsLagrangianDensity_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsEnergyDensity_nonneg,
    Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsEnergyDensity_gauge_invariant]

/- ZIL-END -/
