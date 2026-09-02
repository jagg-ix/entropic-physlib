/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills
public import Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
meta import Zil

/-!
# Sánchez's Yang/Ernst `R` gauge and finite-temperature caloron

This module formalizes the algebraic and PDE/metric core of N. Sánchez,
*Connection between the self-dual Yang--Mills and general relativity Einstein
equations*, Phys. Lett. **144B** (1984) 217--220.

The implementation reuses the repository's non-Abelian curvature and
self-dual Hodge carriers.  It adds:

* the exact determinant-one `2 × 2` `R`-gauge matrix of eq. (6), together
  with its lower/upper triangular factorization and non-singularity;
* the displayed holomorphic compatibility equations (9) and all three
  modified Yang/Ernst equations (8), represented on a genuine complex-linear
  coordinate derivative;
* a proof that the paper's null-Killing ansatz `P = V`, `C = -V` solves the
  complete displayed system when the two `z` derivatives vanish;
* the corresponding metric block `[[V⁻¹,-1],[1,0]]`;
* the coth caloron profile and its exact imaginary-time period `β`, followed
  by periodicity of the induced `R`-gauge metric block.

## Honest scope

The `2 × 2` matrix is the complex `(Y,Z)` block used by Sánchez, not a new
global pseudo-Riemannian metric bundle.  `ModifiedYangErnstSystem` formalizes
the three displayed second-order equations and the displayed holomorphic half
of the first-order compatibility equations; the paper denotes the other half
by complex conjugation.  The caloron theorem proves exact periodicity of the
closed coth profile.  Completeness, absence of curvature singularities, finite
Yang--Mills action, and the global gravitational-instanton extension require
additional analytic hypotheses and are not inferred from periodicity.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

/-! ## A. The determinant-one `R`-gauge metric block -/

/-- Sánchez eq. (6):
`g = [[V⁻¹, C V⁻¹], [P V⁻¹, V + P C V⁻¹]]`. -/
noncomputable def rGaugeMatrix (V P C : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![V⁻¹, C * V⁻¹; P * V⁻¹, V + P * C * V⁻¹]

/-- Lower triangular factor in an exact `LU` factorization of `rGaugeMatrix`. -/
noncomputable def rGaugeLower (V P : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![V⁻¹, 0; P * V⁻¹, 1]

/-- Upper triangular factor in an exact `LU` factorization of `rGaugeMatrix`. -/
noncomputable def rGaugeUpper (V C : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, C; 0, V]

/-- The paper's `R`-gauge parametrization is exactly triangular:
`g(V,P,C) = L(V,P) U(V,C)`. -/
@[zil_level physical_theorem]
theorem rGaugeMatrix_eq_lower_mul_upper (V P C : ℂ) :
    rGaugeMatrix V P C = rGaugeLower V P * rGaugeUpper V C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rGaugeMatrix, rGaugeLower, rGaugeUpper, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- The `R`-gauge block has determinant one whenever `V` is nonzero. -/
@[zil_level physical_theorem]
theorem rGaugeMatrix_det (V P C : ℂ) (hV : V ≠ 0) :
    (rGaugeMatrix V P C).det = 1 := by
  rw [rGaugeMatrix_eq_lower_mul_upper, Matrix.det_mul, Matrix.det_fin_two,
    Matrix.det_fin_two]
  simp [rGaugeLower, rGaugeUpper, hV]

/-- Hence the `R`-gauge block is non-singular; the determinant condition is
derived rather than stored in a metric certificate. -/
@[zil_level physical_theorem]
theorem rGaugeMatrix_nonsingular (V P C : ℂ) (hV : V ≠ 0) :
    IsUnit (rGaugeMatrix V P C).det := by
  rw [rGaugeMatrix_det V P C hV]
  exact isUnit_one

/-- Under Sánchez's null-Killing ansatz `P = V`, `C = -V`, the metric block
reduces exactly to `[[V⁻¹,-1],[1,0]]`, the matrix form of eq. (15). -/
@[zil_level physical_theorem]
theorem rGauge_nullKilling_matrix (V : ℂ) (hV : V ≠ 0) :
    rGaugeMatrix V V (-V) = !![V⁻¹, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rGaugeMatrix, hV]

/-! ## B. Modified Yang/Ernst equations on a complex-linear derivative -/

/-- A complex-linear coordinate derivative.  Unlike a bare function-valued
derivative, this carrier proves differentiation of zero and negation, which is
exactly what the null-Killing reduction needs. -/
abbrev ComplexPartial (X : Type*) :=
  (X → ℂ) →ₗ[ℂ] (Fin 4 → X → ℂ)

/-- The two displayed equations in Sánchez (9); the paper obtains the other
two by complex conjugation.  Indices `0,1,2,3` represent `y,ybar,z,zbar`. -/
def RGaugeCompatibility {X : Type*} (D : ComplexPartial X)
    (V P C : X → ℂ) : Prop :=
  (∀ x, V x * D V 1 x + P x * D C 1 x = D C 2 x) ∧
  (∀ x, V x * D P 0 x - P x * D V 0 x = -D V 3 x)

/-- First scalar residual in Sánchez eq. (8). -/
def modifiedYangVResidual {X : Type*} (D : ComplexPartial X)
    (V P C : X → ℂ) (x : X) : ℂ :=
  (V x ^ 2 + P x * C x) *
      (V x * D (fun q => D V 1 q) 0 x -
        D V 0 x * D V 1 x + D P 1 x * D C 0 x) +
    (V x * D (fun q => D V 3 q) 2 x -
      D V 2 x * D V 3 x + D P 3 x * D C 2 x)

/-- Second scalar residual in Sánchez eq. (8). -/
noncomputable def modifiedYangPResidual {X : Type*} (D : ComplexPartial X)
    (V P C : X → ℂ) (x : X) : ℂ :=
  (V x ^ 2 + P x * C x) *
      D (fun q => (V q)⁻¹ ^ 2 * D P 0 q) 0 x +
    D (fun q => (V q)⁻¹ ^ 2 * D P 3 q) 2 x

/-- Third scalar residual in Sánchez eq. (8). -/
noncomputable def modifiedYangCResidual {X : Type*} (D : ComplexPartial X)
    (V P C : X → ℂ) (x : X) : ℂ :=
  (V x ^ 2 + P x * C x) *
      D (fun q => (V q)⁻¹ ^ 2 * D C 1 q) 1 x +
    D (fun q => (V q)⁻¹ ^ 2 * D C 2 q) 3 x

/-- The displayed Sánchez modified Yang/Ernst PDE system: the first-order
`R`-gauge compatibility equations plus all three second-order residuals. -/
def ModifiedYangErnstSystem {X : Type*} (D : ComplexPartial X)
    (V P C : X → ℂ) : Prop :=
  RGaugeCompatibility D V P C ∧
  (∀ x, modifiedYangVResidual D V P C x = 0) ∧
  (∀ x, modifiedYangPResidual D V P C x = 0) ∧
  (∀ x, modifiedYangCResidual D V P C x = 0)

/-- The null-Killing ansatz satisfies the first-order `R`-gauge equations. -/
@[zil_level physical_theorem]
theorem nullKilling_rGaugeCompatibility {X : Type*}
    (D : ComplexPartial X) (V : X → ℂ)
    (hZ : ∀ x, D V 2 x = 0)
    (hZbar : ∀ x, D V 3 x = 0) :
    RGaugeCompatibility D V V (-V) := by
  constructor
  · intro x
    rw [show D (-V) = -D V by exact D.map_neg V]
    simp only [Pi.neg_apply, hZ]
    ring
  · intro x
    rw [hZbar]
    ring

/-- **Sánchez null-Killing solution.** If `V` is independent of `z,zbar`,
then `P = V`, `C = -V` solves every displayed modified Yang/Ernst equation,
not merely the determinant condition. -/
@[zil_level physical_theorem]
theorem nullKilling_solves_modifiedYangErnst {X : Type*}
    (D : ComplexPartial X) (V : X → ℂ)
    (hZ : ∀ x, D V 2 x = 0)
    (hZbar : ∀ x, D V 3 x = 0) :
    ModifiedYangErnstSystem D V V (-V) := by
  have hneg : D (-V) = -D V := D.map_neg V
  refine ⟨nullKilling_rGaugeCompatibility D V hZ hZbar, ?_, ?_, ?_⟩
  · intro x
    simp only [modifiedYangVResidual, Pi.neg_apply, hZ, hZbar,
      hneg, zero_mul, mul_zero, sub_zero, add_zero]
    rw [show V x ^ 2 + V x * -V x = 0 by ring, zero_mul, zero_add,
      show (fun _ : X => (0 : ℂ)) = 0 by rfl, D.map_zero, Pi.zero_apply]
    change V x * 0 = 0
    ring
  · intro x
    have hfun : (fun q => (V q)⁻¹ ^ 2 * D V 3 q) = 0 := by
      funext q
      simp [hZbar q]
    simp only [modifiedYangPResidual, Pi.neg_apply]
    rw [show V x ^ 2 + V x * -V x = 0 by ring, zero_mul, hfun, D.map_zero,
      Pi.zero_apply, zero_add]
    rfl
  · intro x
    have hfun : (fun q => (V q)⁻¹ ^ 2 * D (-V) 2 q) = 0 := by
      funext q
      rw [hneg]
      simp [hZ q]
    simp only [modifiedYangCResidual, Pi.neg_apply]
    rw [show V x ^ 2 + V x * -V x = 0 by ring, zero_mul, hfun, D.map_zero,
      Pi.zero_apply, zero_add]
    rfl

/-! ## C. The `'t Hooft` endpoint is the flat `R`-gauge geometry -/

/-- The metric endpoint selected by the paper's `'t Hooft` compatibility
reduction: `V = 1`, `P = C = 0`. -/
noncomputable def tHooftFlatRGaugeMetric : Matrix (Fin 2) (Fin 2) ℂ :=
  rGaugeMatrix 1 0 0

/-- Sánchez's observation after eq. (14), made exact: the `'t Hooft`
compatibility endpoint is the constant identity metric block. -/
@[zil_level physical_theorem]
theorem tHooftFlatRGaugeMetric_eq_one :
    tHooftFlatRGaugeMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tHooftFlatRGaugeMetric, rGaugeMatrix]

/-- Its real metric is also the identity, so it feeds the repository's real
Levi--Civita/Riemann contraction API without a second metric carrier. -/
@[zil_level physical_theorem]
theorem tHooftFlatRGaugeMetric_realPart :
    tHooftFlatRGaugeMetric.map Complex.re =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [tHooftFlatRGaugeMetric_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The constant metric's Levi--Civita connection in its global affine chart. -/
def tHooftFlatConnection : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ => 0

/-- Coordinate derivative of the constant zero connection. -/
def tHooftFlatConnectionDeriv :
    Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ _ => 0

/-- **The paper's `'t Hooft` reduction is geometrically flat.**  The
connection-derived Riemann tensor and its Ricci contraction vanish for the
identity `R`-gauge endpoint.  This reuses `riemannFromConnection` rather than
declaring “flat” as a certificate attached to the ansatz. -/
@[zil_level physical_theorem]
theorem tHooftRGauge_flat_curvature :
    (∀ ρ σ μ ν,
      riemannFromConnection tHooftFlatConnection
        tHooftFlatConnectionDeriv ρ σ μ ν = 0) ∧
    ricciMatrixFromConnection tHooftFlatConnection
      tHooftFlatConnectionDeriv = 0 := by
  constructor
  · intro ρ σ μ ν
    exact riemannFromConnection_flat ρ σ μ ν
  · ext σ ν
    simp [ricciMatrixFromConnection, ricciFromConnection,
      tHooftFlatConnection, tHooftFlatConnectionDeriv,
      riemannFromConnection]

/-- The complete metric/curvature statement behind the paper's sentence that
the constrained `'t Hooft` ansatz gives a trivial gravitational metric. -/
@[zil_level physical_theorem]
theorem tHooftRGauge_reduces_to_flat_geometry :
    tHooftFlatRGaugeMetric.map Complex.re =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (∀ ρ σ μ ν,
      riemannFromConnection tHooftFlatConnection
        tHooftFlatConnectionDeriv ρ σ μ ν = 0) ∧
    ricciMatrixFromConnection tHooftFlatConnection
      tHooftFlatConnectionDeriv = 0 :=
  ⟨tHooftFlatRGaugeMetric_realPart,
    tHooftRGauge_flat_curvature.1,
    tHooftRGauge_flat_curvature.2⟩

/-! ## D. The coth caloron and periodic metric block -/

/-- Complex hyperbolic cotangent, defined from Mathlib's `tanh`. -/
noncomputable def complexCoth (z : ℂ) : ℂ := (Complex.tanh z)⁻¹

/-- `coth` has imaginary period `π i`, inherited from `Complex.tanh_periodic`. -/
@[zil_level physical_theorem]
theorem complexCoth_add_pi_mul_I (z : ℂ) :
    complexCoth (z + Real.pi * Complex.I) = complexCoth z := by
  simp [complexCoth]

/-- The one-centre finite-temperature inverse profile displayed after Sánchez
eq. (17), with `τ` the imaginary-time coordinate. -/
noncomputable def sanchezCaloronInverse
    (β a x3 : ℝ) (τ : ℝ) : ℂ :=
  1 + ((Real.pi / β * a : ℝ) : ℂ) *
    complexCoth (((Real.pi / β : ℝ) : ℂ) *
      ((x3 : ℂ) + Complex.I * (τ : ℂ)))

/-- The closed coth profile is exactly periodic under `τ ↦ τ + β`. -/
@[zil_level physical_theorem]
theorem sanchezCaloronInverse_periodic
    (β a x3 : ℝ) (hβ : β ≠ 0) :
    Function.Periodic (sanchezCaloronInverse β a x3) β := by
  intro τ
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  unfold sanchezCaloronInverse
  rw [show (((Real.pi / β : ℝ) : ℂ) *
          ((x3 : ℂ) + Complex.I * ((τ + β : ℝ) : ℂ))) =
        (((Real.pi / β : ℝ) : ℂ) *
          ((x3 : ℂ) + Complex.I * (τ : ℂ))) +
          Real.pi * Complex.I by
      push_cast
      field_simp [hβc]
      ring]
  rw [complexCoth_add_pi_mul_I]

/-- The corresponding `V` profile is the inverse of the displayed expression. -/
noncomputable def sanchezCaloronV
    (β a x3 : ℝ) (τ : ℝ) : ℂ :=
  (sanchezCaloronInverse β a x3 τ)⁻¹

/-- Inversion preserves the exact imaginary-time period. -/
@[zil_level physical_theorem]
theorem sanchezCaloronV_periodic
    (β a x3 : ℝ) (hβ : β ≠ 0) :
    Function.Periodic (sanchezCaloronV β a x3) β := by
  intro τ
  simp only [sanchezCaloronV, sanchezCaloronInverse_periodic β a x3 hβ τ]

/-- The null-Killing `R`-gauge metric block generated by the caloron profile. -/
noncomputable def sanchezNullCaloronMetric
    (β a x3 : ℝ) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rGaugeMatrix (sanchezCaloronV β a x3 τ)
    (sanchezCaloronV β a x3 τ) (-sanchezCaloronV β a x3 τ)

/-- The finite-temperature periodicity lifts pointwise to the induced metric
block, rather than being asserted as separate metric data. -/
@[zil_level physical_theorem]
theorem sanchezNullCaloronMetric_periodic
    (β a x3 : ℝ) (hβ : β ≠ 0) :
    Function.Periodic (sanchezNullCaloronMetric β a x3) β := by
  intro τ
  simp only [sanchezNullCaloronMetric,
    sanchezCaloronV_periodic β a x3 hβ τ]

/-- When the inverse profile is nonzero, the periodic caloron metric block is
non-degenerate with determinant one at every imaginary time. -/
@[zil_level physical_theorem]
theorem sanchezNullCaloronMetric_det
    (β a x3 τ : ℝ)
    (hprofile : sanchezCaloronInverse β a x3 τ ≠ 0) :
    (sanchezNullCaloronMetric β a x3 τ).det = 1 := by
  apply rGaugeMatrix_det
  exact inv_ne_zero hprofile

end Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.rGaugeMatrix_det where
  formalizes @ "claim:sanchez-r-gauge-parametrization-has-determinant-one-and-is-nondegenerate-whenever-v-is-nonzero",
  supported_by @ "paper:sanchez1984:eq6",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-the-exact-complex-two-by-two-y-z-metric-block-not-yet-a-global-complete-four-dimensional-riemannian-metric"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.nullKilling_solves_modifiedYangErnst where
  formalizes @ "claim:the-null-killing-ansatz-p-equals-v-and-c-equals-minus-v-solves-the-displayed-sanchez-modified-yang-ernst-system-when-v-is-independent-of-z-and-zbar",
  supported_by @ "paper:sanchez1984:eq8",
  supported_by @ "paper:sanchez1984:eq9",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:z-and-zbar-independence-is-the-explicit-null-killing-hypothesis-and-the-conjugate-half-of-equation-nine-is-not-hidden-inside-the-displayed-holomorphic-system"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.tHooftRGauge_reduces_to_flat_geometry where
  formalizes @ "claim:the-sanchez-r-gauge-compatibility-reduction-of-the-t-hooft-ansatz-lands-on-the-identity-metric-with-vanishing-connection-derived-riemann-and-ricci-curvature",
  supported_by @ "paper:sanchez1984:after-eq14",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.riemannFromConnection_flat",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:this-proves-the-gravitational-r-gauge-endpoint-is-flat-it-does-not-say-that-a-nontrivial-yang-mills-t-hooft-instanton-has-zero-gauge-curvature"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.sanchezCaloronInverse_periodic where
  formalizes @ "claim:the-sanchez-coth-finite-temperature-profile-is-exactly-periodic-in-imaginary-time-with-period-beta",
  supported_by @ "lean:Complex.tanh_periodic",
  supported_by @ "paper:sanchez1984:caloron-after-eq17",
  epistemic_status @ "risky",
  caveat @ "claim:periodicity-does-not-by-itself-prove-finite-action-curvature-regularity-geodesic-completeness-or-a-global-gravitational-instanton"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.sanchezNullCaloronMetric_periodic where
  formalizes @ "claim:the-finite-temperature-periodicity-of-the-caloron-profile-is-inherited-by-the-null-killing-r-gauge-metric-block",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.sanchezCaloronV_periodic",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.rGauge_nullKilling_matrix",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:this-is-pointwise-periodicity-and-conditional-nondegeneracy-of-the-complex-metric-block-not-a-proof-of-global-caloron-moduli-space-compactness"

zil_file_contract physlib.sanchezYangErnstCaloron where
  promises "The exact determinant-one Sanchez R-gauge matrix is factorized and proved non-singular. The displayed first-order compatibility equations and all three modified Yang/Ernst residuals are defined on a complex-linear continuum derivative, and the null-Killing ansatz P=V, C=-V is proved to solve them under explicit z,zbar independence. The paper's constrained t-Hooft endpoint is proved to be the identity metric with zero connection-derived Riemann and Ricci curvature. The finite-temperature coth profile is proved beta-periodic and that periodicity lifts to the induced R-gauge metric block, whose determinant is one under the visible nonzero-profile hypothesis."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics.yangMillsCurvature",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills.antiSelfDual_iff_sdProj_zero",
    "lean:Complex.tanh_periodic"
  ]
  forbids_substitutes [
    "calling the two-by-two complex R-gauge block a completed global pseudo-Riemannian metric",
    "calling imaginary-time periodicity a proof of finite action or geodesic completeness",
    "claiming the null-Killing ansatz solves the unconstrained four-coordinate system without its explicit derivative hypotheses"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.rGaugeMatrix_eq_lower_mul_upper,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.rGaugeMatrix_det,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.nullKilling_solves_modifiedYangErnst,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.tHooftRGauge_reduces_to_flat_geometry,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.sanchezCaloronInverse_periodic,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.sanchezNullCaloronMetric_periodic,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SanchezYangErnstCaloron.sanchezNullCaloronMetric_det
  ]

/- ZIL-END -/
