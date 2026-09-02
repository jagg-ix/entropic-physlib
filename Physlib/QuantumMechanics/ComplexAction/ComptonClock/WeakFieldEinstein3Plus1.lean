/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-!
# A sourced linearized `3+1` weak-field Einstein carrier

The exact `1+1` demonstrator in `NewtonianLimitCurvatureAPI` has identically zero Einstein tensor.
This module supplies the smallest honest sourced spacetime carrier needed by the holographic-Newton
integration: a static Newtonian-gauge perturbation of mostly-minus Minkowski space in `3+1` dimensions.

The first carrier lets the potential vary along one Cartesian axis.  This is plane symmetry, not a
reduction of the spacetime index type: every metric, connection, Ricci, stress-energy, and field-equation
carrier is a `Matrix (Fin 4) (Fin 4)`.  The final section generalizes the same construction to a static
potential `Φ(x,y,z)` with an arbitrary symmetric spatial Hessian.  Writing `q = Φ/c²`, the covariant
perturbation is

`h = diag(2q, 2q, 2q, 2q)`, so `g = η + h` with `η = diag(1,-1,-1,-1)`.

The connection is computed by the existing general `christoffelFromMetric` construction using the flat
inverse metric.  Curvature is then truncated consistently at first order: the `∂Γ` terms are retained and
the quadratic `ΓΓ = O(h²)` terms are discarded.  The source-bearing `R₀₀` component is computed through the
existing `ricciFromConnection` contraction; the isotropic Newtonian-gauge Ricci matrix packages the four
standard first-order diagonal components without repeating the expensive generic contraction componentwise.

The resulting tensors are

* `R_μν^(1) = (Φ''/c²) diag(1,1,1,1)`,
* `R^(1) = -2 Φ''/c²`,
* `G_μν^(1) = diag(2Φ''/c²,0,0,0)`.

Consequently, for rest dust `T = diag(ρc²,0,0,0)`, the full matrix equation
`G^(1) = (8πG/c⁴)T` follows first from the one-dimensional Poisson relation `Φ'' = 4πGρ` and then, in the
general static carrier, from `∂ₓ²Φ + ∂ᵧ²Φ + ∂𝓏²Φ = 4πGρ`.  These are linearized `3+1` field equations,
not exact nonlinear solutions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

/-! ## A. The `3+1` metric perturbation and its Levi-Civita connection -/

/-- The mostly-minus Minkowski metric `η = diag(1,-1,-1,-1)` on the concrete `Fin 4` index type. -/
noncomputable def minkowskiMetric4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- The isotropic Newtonian-gauge perturbation `h = diag(2Φ/c²,2Φ/c²,2Φ/c²,2Φ/c²)`. -/
noncomputable def weakFieldPerturbation4 (Φ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 * Φ / c ^ 2, 0, 0, 0;
     0, 2 * Φ / c ^ 2, 0, 0;
     0, 0, 2 * Φ / c ^ 2, 0;
     0, 0, 0, 2 * Φ / c ^ 2]

/-- The linearized weak-field metric carrier `g = η + h`. -/
noncomputable def weakFieldMetric4 (Φ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  minkowskiMetric4 + weakFieldPerturbation4 Φ c

/-- The coordinate derivatives `∂_κ g`: static and plane-symmetric, with only `∂₁g` nonzero. -/
noncomputable def weakFieldMetricDeriv4 (dΦ c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![0,
    !![2 * dΦ / c ^ 2, 0, 0, 0;
       0, 2 * dΦ / c ^ 2, 0, 0;
       0, 0, 2 * dΦ / c ^ 2, 0;
       0, 0, 0, 2 * dΦ / c ^ 2],
    0,
    0]

/-- The first-order Levi-Civita connection obtained from `η⁻¹ = η` and `∂h = ∂g`. -/
noncomputable def weakFieldLinearizedLeviCivita4 (dΦ c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  christoffelFromMetric minkowskiMetric4 (weakFieldMetricDeriv4 dΦ c)

/-- The explicit component array of the metric-derived first-order connection. -/
noncomputable def weakFieldLinearizedConnection4 (dΦ c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  let q := dΦ / c ^ 2
  ![!![0, q, 0, 0; q, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![q, 0, 0, 0; 0, -q, 0, 0; 0, 0, q, 0; 0, 0, 0, q],
    !![0, 0, 0, 0; 0, 0, -q, 0; 0, -q, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 0, 0, 0, -q; 0, 0, 0, 0; 0, -q, 0, 0]]

/-- The metric construction gives `Γ¹₀₀ = Φ'/c²`, the Newtonian acceleration component. -/
lemma weakFieldLinearizedLeviCivita4_100 (dΦ c : ℝ) :
    weakFieldLinearizedLeviCivita4 dΦ c 1 0 0 = dΦ / c ^ 2 := by
  unfold weakFieldLinearizedLeviCivita4 christoffelFromMetric
  rw [Matrix.of_apply]
  rw [Fin.sum_univ_four]
  norm_num [minkowskiMetric4, weakFieldMetricDeriv4, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  ring_nf

/-- The metric-derived first-order connection is torsion-free. -/
lemma weakFieldLinearizedLeviCivita4_isTorsionFree (dΦ c : ℝ) :
    IsTorsionFree (weakFieldLinearizedLeviCivita4 dΦ c) := by
  apply christoffelFromMetric_isTorsionFree
  intro κ
  ext μ ν
  fin_cases κ <;> fin_cases μ <;> fin_cases ν <;>
    rfl

/-! ## B. First-order curvature from the metric-derived connection -/

/-- The connection derivatives `∂_κ Γ`: only `∂₁Γ` is nonzero, replacing `Φ'` by `Φ''`. -/
noncomputable def weakFieldLinearizedConnDeriv4 (d2Φ c : ℝ) :
    Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![0, weakFieldLinearizedConnection4 d2Φ c, 0, 0]

/-- The isotropic first-order Ricci carrier `R^(1) = (Φ''/c²) I₄`. -/
noncomputable def weakFieldLinearizedRicci4 (d2Φ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (d2Φ / c ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- The linearized Ricci matrix is `(Φ''/c²)` times the Euclidean diagonal. -/
lemma weakFieldLinearizedRicci4_eq (d2Φ c : ℝ) :
    weakFieldLinearizedRicci4 d2Φ c =
      !![d2Φ / c ^ 2, 0, 0, 0;
         0, d2Φ / c ^ 2, 0, 0;
         0, 0, d2Φ / c ^ 2, 0;
         0, 0, 0, d2Φ / c ^ 2] := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [weakFieldLinearizedRicci4, Matrix.smul_apply, Matrix.one_apply]

/-- The source-bearing `R₀₀^(1)` is derived from `∂Γ-∂Γ` using the existing connection-curvature API. -/
lemma weakFieldLinearized_ricci00_from_connection (d2Φ c : ℝ) :
    ricciFromConnection (fun _ => 0) (weakFieldLinearizedConnDeriv4 d2Φ c) 0 0 =
      d2Φ / c ^ 2 := by
  simp [ricciFromConnection, riemannFromConnection, weakFieldLinearizedConnDeriv4,
    weakFieldLinearizedConnection4, Fin.sum_univ_four]

/-- The packaged Ricci matrix has the same `00` component as the connection-derived contraction. -/
lemma weakFieldLinearizedRicci4_apply_00_eq_connection (d2Φ c : ℝ) :
    weakFieldLinearizedRicci4 d2Φ c 0 0 =
      ricciFromConnection (fun _ => 0) (weakFieldLinearizedConnDeriv4 d2Φ c) 0 0 := by
  rw [weakFieldLinearized_ricci00_from_connection]
  simp [weakFieldLinearizedRicci4, Matrix.smul_apply]

/-- The scalar curvature is the Minkowski trace of the linearized Ricci matrix. -/
noncomputable def weakFieldLinearizedScalar4 (d2Φ c : ℝ) : ℝ :=
  ricciScalarContraction minkowskiMetric4 (weakFieldLinearizedRicci4 d2Φ c)

/-- `R^(1) = -2 Φ''/c²`. -/
lemma weakFieldLinearizedScalar4_eq (d2Φ c : ℝ) :
    weakFieldLinearizedScalar4 d2Φ c = -2 * d2Φ / c ^ 2 := by
  rw [weakFieldLinearizedScalar4, weakFieldLinearizedRicci4_eq]
  simp [ricciScalarContraction, minkowskiMetric4, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_four]
  ring

/-- The first-order Einstein tensor of the `3+1` plane-symmetric weak field. -/
noncomputable def weakFieldLinearizedEinstein4 (d2Φ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  einsteinTensor (weakFieldLinearizedRicci4 d2Φ c)
    (weakFieldLinearizedScalar4 d2Φ c) minkowskiMetric4

/-- `G^(1) = diag(2Φ''/c²,0,0,0)`: unlike the exact `1+1` carrier, it can support rest dust. -/
lemma weakFieldLinearizedEinstein4_eq (d2Φ c : ℝ) :
    weakFieldLinearizedEinstein4 d2Φ c =
      !![2 * d2Φ / c ^ 2, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  rw [weakFieldLinearizedEinstein4, weakFieldLinearizedRicci4_eq,
    weakFieldLinearizedScalar4_eq]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [einsteinTensor, minkowskiMetric4] <;>
    ring

/-! ## C. The sourced Einstein equation and its complex extension -/

/-- Rest-dust stress energy `T = diag(ρc²,0,0,0)`. -/
noncomputable def restDustStressEnergy4 (ρ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ρ * c ^ 2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- The plane-symmetric Poisson equation implies the complete linearized `3+1` Einstein matrix equation. -/
theorem weakFieldLinearizedEFE4_of_poisson (G c ρ d2Φ : ℝ) (hc : c ≠ 0)
    (hPoisson : d2Φ = 4 * Real.pi * G * ρ) :
    einsteinFieldEquation (weakFieldLinearizedRicci4 d2Φ c)
      (weakFieldLinearizedScalar4 d2Φ c) minkowskiMetric4
      (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4) := by
  unfold einsteinFieldEquation
  rw [← weakFieldLinearizedEinstein4, weakFieldLinearizedEinstein4_eq]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [restDustStressEnergy4, Matrix.smul_apply, smul_eq_mul] <;>
    field_simp [hc] <;>
    nlinarith [hPoisson]

/-- Conversely, the complete linearized `3+1` rest-dust Einstein equation recovers Poisson's equation. -/
theorem poisson_of_weakFieldLinearizedEFE4 (G c ρ d2Φ : ℝ) (hc : c ≠ 0)
    (hEFE : einsteinFieldEquation (weakFieldLinearizedRicci4 d2Φ c)
      (weakFieldLinearizedScalar4 d2Φ c) minkowskiMetric4
      (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)) :
    d2Φ = 4 * Real.pi * G * ρ := by
  unfold einsteinFieldEquation at hEFE
  rw [← weakFieldLinearizedEinstein4, weakFieldLinearizedEinstein4_eq] at hEFE
  have h00 := congrFun (congrFun hEFE 0) 0
  simp [restDustStressEnergy4, Matrix.smul_apply, smul_eq_mul] at h00
  field_simp [hc] at h00
  nlinarith

/-- The sourced linearized `3+1` Einstein equation is equivalent to the plane-symmetric Poisson equation. -/
theorem weakFieldLinearizedEFE4_iff_poisson (G c ρ d2Φ : ℝ) (hc : c ≠ 0) :
    einsteinFieldEquation (weakFieldLinearizedRicci4 d2Φ c)
        (weakFieldLinearizedScalar4 d2Φ c) minkowskiMetric4
        (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
      ↔ d2Φ = 4 * Real.pi * G * ρ :=
  ⟨poisson_of_weakFieldLinearizedEFE4 G c ρ d2Φ hc,
    weakFieldLinearizedEFE4_of_poisson G c ρ d2Φ hc⟩

/-- Adding the explicit imaginary-sector equation gives the complex linearized `3+1` field equation. -/
theorem weakFieldLinearizedComplexEFE4_of_poisson
    (G c ρ d2Φ : ℝ) (Λ S : Matrix (Fin 4) (Fin 4) ℝ)
    (hc : c ≠ 0) (hPoisson : d2Φ = 4 * Real.pi * G * ρ)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    complexEinsteinFieldEquation (weakFieldLinearizedEinstein4 d2Φ c) Λ
      (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  rw [complexEinsteinFieldEquation_iff]
  exact ⟨weakFieldLinearizedEFE4_of_poisson G c ρ d2Φ hc hPoisson, hImaginary⟩

/-! ## D. General static spatial potential and the complete connection-derived Ricci matrix -/

/-- The spatial Laplacian `∇²Φ = ∂ₓ²Φ + ∂ᵧ²Φ + ∂𝓏²Φ` at the point represented by the carrier. -/
def spatialLaplacian3 (dxxΦ dyyΦ dzzΦ : ℝ) : ℝ :=
  dxxΦ + dyyΦ + dzzΦ

/-- A single spatial derivative of the isotropic Newtonian-gauge metric perturbation. -/
noncomputable def weakFieldMetricSpatialDerivative4 (dΦ c : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 * dΦ / c ^ 2, 0, 0, 0;
     0, 2 * dΦ / c ^ 2, 0, 0;
     0, 0, 2 * dΦ / c ^ 2, 0;
     0, 0, 0, 2 * dΦ / c ^ 2]

/-- `∂_κg` for a general static potential with gradient `(∂ₓΦ,∂ᵧΦ,∂𝓏Φ)`. -/
noncomputable def weakFieldMetricDeriv4Spatial (dxΦ dyΦ dzΦ c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![0,
    weakFieldMetricSpatialDerivative4 dxΦ c,
    weakFieldMetricSpatialDerivative4 dyΦ c,
    weakFieldMetricSpatialDerivative4 dzΦ c]

/-- The metric-derived first-order Levi-Civita connection for a general static spatial gradient. -/
noncomputable def weakFieldLinearizedLeviCivita4Spatial (dxΦ dyΦ dzΦ c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  christoffelFromMetric minkowskiMetric4 (weakFieldMetricDeriv4Spatial dxΦ dyΦ dzΦ c)

/-- The static four-gradient `(0,∂ₓΦ/c²,∂ᵧΦ/c²,∂𝓏Φ/c²)` used by the closed Christoffel formula. -/
def weakFieldSpatialGradient4 (dxΦ dyΦ dzΦ c : ℝ) : Fin 4 → ℝ :=
  ![0, dxΦ / c ^ 2, dyΦ / c ^ 2, dzΦ / c ^ 2]

/-- The concrete Kronecker delta on the `Fin 4` spacetime indices. -/
def kronecker4 (μ ν : Fin 4) : ℝ :=
  if μ = ν then 1 else 0

/-- The diagonal sign of the mostly-minus Minkowski inverse metric. -/
def minkowskiSign4 (μ : Fin 4) : ℝ :=
  if μ = 0 then 1 else -1

/--
The evaluated first-order Christoffel array for a general static spatial gradient, written in the
compact index formula `Γ^ρ_μν = η^{ρρ}(δ_ρν q_μ + δ_ρμ q_ν - δ_μν q_ρ)`.
-/
noncomputable def weakFieldLinearizedConnection4Spatial (dxΦ dyΦ dzΦ c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  fun ρ μ ν =>
    minkowskiSign4 ρ *
      (kronecker4 ρ ν * weakFieldSpatialGradient4 dxΦ dyΦ dzΦ c μ
        + kronecker4 ρ μ * weakFieldSpatialGradient4 dxΦ dyΦ dzΦ c ν
        - kronecker4 μ ν * weakFieldSpatialGradient4 dxΦ dyΦ dzΦ c ρ)

/-- The time-upper-index Christoffel matrix agrees with the compact indexed formula. -/
lemma weakFieldLinearizedLeviCivita4Spatial_upper0
    (dxΦ dyΦ dzΦ c : ℝ) :
    weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 0 =
      weakFieldLinearizedConnection4Spatial dxΦ dyΦ dzΦ c 0 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [weakFieldLinearizedLeviCivita4Spatial, christoffelFromMetric, minkowskiMetric4,
      weakFieldMetricDeriv4Spatial, weakFieldMetricSpatialDerivative4,
      weakFieldLinearizedConnection4Spatial, weakFieldSpatialGradient4,
      kronecker4, minkowskiSign4, Fin.sum_univ_four] <;>
    ring

/-- The first spatial upper-index Christoffel matrix agrees with the compact indexed formula. -/
lemma weakFieldLinearizedLeviCivita4Spatial_upper1
    (dxΦ dyΦ dzΦ c : ℝ) :
    weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 1 =
      weakFieldLinearizedConnection4Spatial dxΦ dyΦ dzΦ c 1 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [weakFieldLinearizedLeviCivita4Spatial, christoffelFromMetric, minkowskiMetric4,
      weakFieldMetricDeriv4Spatial, weakFieldMetricSpatialDerivative4,
      weakFieldLinearizedConnection4Spatial, weakFieldSpatialGradient4,
      kronecker4, minkowskiSign4, Fin.sum_univ_four] <;>
    ring

/-- The second spatial upper-index Christoffel matrix agrees with the compact indexed formula. -/
lemma weakFieldLinearizedLeviCivita4Spatial_upper2
    (dxΦ dyΦ dzΦ c : ℝ) :
    weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 2 =
      weakFieldLinearizedConnection4Spatial dxΦ dyΦ dzΦ c 2 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [weakFieldLinearizedLeviCivita4Spatial, christoffelFromMetric, minkowskiMetric4,
      weakFieldMetricDeriv4Spatial, weakFieldMetricSpatialDerivative4,
      weakFieldLinearizedConnection4Spatial, weakFieldSpatialGradient4,
      kronecker4, minkowskiSign4, Fin.sum_univ_four] <;>
    ring

/-- The third spatial upper-index Christoffel matrix agrees with the compact indexed formula. -/
lemma weakFieldLinearizedLeviCivita4Spatial_upper3
    (dxΦ dyΦ dzΦ c : ℝ) :
    weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 3 =
      weakFieldLinearizedConnection4Spatial dxΦ dyΦ dzΦ c 3 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [weakFieldLinearizedLeviCivita4Spatial, christoffelFromMetric, minkowskiMetric4,
      weakFieldMetricDeriv4Spatial, weakFieldMetricSpatialDerivative4,
      weakFieldLinearizedConnection4Spatial, weakFieldSpatialGradient4,
      kronecker4, minkowskiSign4, Fin.sum_univ_four] <;>
    ring

/--
The compact indexed Christoffel array is exactly the result of the general metric-to-connection
construction for every upper and lower spacetime index.
-/
lemma weakFieldLinearizedLeviCivita4Spatial_eq_connection
    (dxΦ dyΦ dzΦ c : ℝ) :
    weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c =
      weakFieldLinearizedConnection4Spatial dxΦ dyΦ dzΦ c := by
  funext ρ
  fin_cases ρ
  · exact weakFieldLinearizedLeviCivita4Spatial_upper0 dxΦ dyΦ dzΦ c
  · exact weakFieldLinearizedLeviCivita4Spatial_upper1 dxΦ dyΦ dzΦ c
  · exact weakFieldLinearizedLeviCivita4Spatial_upper2 dxΦ dyΦ dzΦ c
  · exact weakFieldLinearizedLeviCivita4Spatial_upper3 dxΦ dyΦ dzΦ c

/-- The metric construction gives the three Newtonian acceleration symbols `Γⁱ₀₀ = ∂ᵢΦ/c²`. -/
lemma weakFieldLinearizedLeviCivita4Spatial_acceleration (dxΦ dyΦ dzΦ c : ℝ) :
    weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 1 0 0 = dxΦ / c ^ 2
      ∧ weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 2 0 0 = dyΦ / c ^ 2
      ∧ weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 3 0 0 = dzΦ / c ^ 2 := by
  rw [weakFieldLinearizedLeviCivita4Spatial_eq_connection]
  simp [weakFieldLinearizedConnection4Spatial, weakFieldSpatialGradient4,
    kronecker4, minkowskiSign4]

/-- The metric-derived connection for the general static potential is torsion-free. -/
lemma weakFieldLinearizedLeviCivita4Spatial_isTorsionFree (dxΦ dyΦ dzΦ c : ℝ) :
    IsTorsionFree (weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c) := by
  apply christoffelFromMetric_isTorsionFree
  intro κ
  ext μ ν
  fin_cases κ <;> fin_cases μ <;> fin_cases ν <;> rfl

/--
The derivatives `∂_κΓ` obtained by inserting each row of the symmetric spatial Hessian into the
linearized connection.  The time derivative vanishes because the potential is static.
-/
noncomputable def weakFieldLinearizedConnDeriv4Spatial
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) :
    Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![0,
    weakFieldLinearizedConnection4Spatial dxxΦ dxyΦ dxzΦ c,
    weakFieldLinearizedConnection4Spatial dxyΦ dyyΦ dyzΦ c,
    weakFieldLinearizedConnection4Spatial dxzΦ dyzΦ dzzΦ c]

/--
The connection derivative built directly from the metric-derived Levi-Civita family by inserting
the three rows of the symmetric spatial Hessian.
-/
noncomputable def weakFieldLinearizedLeviCivitaDeriv4Spatial
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) :
    Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![0,
    weakFieldLinearizedLeviCivita4Spatial dxxΦ dxyΦ dxzΦ c,
    weakFieldLinearizedLeviCivita4Spatial dxyΦ dyyΦ dyzΦ c,
    weakFieldLinearizedLeviCivita4Spatial dxzΦ dyzΦ dzzΦ c]

/-- The compact Hessian derivative is exactly the derivative of the metric-derived connection. -/
lemma weakFieldLinearizedLeviCivitaDeriv4Spatial_eq_connectionDeriv
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) :
    weakFieldLinearizedLeviCivitaDeriv4Spatial
        dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c =
      weakFieldLinearizedConnDeriv4Spatial
        dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c := by
  ext κ ρ μ ν
  fin_cases κ <;>
    simp [weakFieldLinearizedLeviCivitaDeriv4Spatial,
      weakFieldLinearizedConnDeriv4Spatial,
      weakFieldLinearizedLeviCivita4Spatial_eq_connection]

/-- The `∂Γ-∂Γ` Ricci contraction after the quadratic connection is set to zero. -/
noncomputable def linearizedRicciMatrixFromConnectionDeriv {ι : Type*} [Fintype ι]
    (dΓ : ι → ι → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun σ ν => ∑ μ, ((dΓ μ μ) ν σ - (dΓ ν μ) μ σ)

/-- Setting `Γ = 0` in the reusable curvature API leaves exactly the linear `∂Γ-∂Γ` contraction. -/
lemma ricciMatrixFromConnection_zero_eq_linearized {ι : Type*} [Fintype ι]
    (dΓ : ι → ι → Matrix ι ι ℝ) :
    ricciMatrixFromConnection (fun _ => 0) dΓ =
      linearizedRicciMatrixFromConnectionDeriv dΓ := by
  ext σ ν
  simp [ricciMatrixFromConnection, ricciFromConnection, riemannFromConnection,
    linearizedRicciMatrixFromConnectionDeriv]

/--
The complete first-order Ricci matrix of the general static carrier.  Unlike the plane-symmetric
packaging above, every component is defined directly by the existing `∂Γ-∂Γ` Ricci contraction.
-/
noncomputable def weakFieldLinearizedRicci4Spatial
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ricciMatrixFromConnection (fun _ => 0)
    (weakFieldLinearizedLeviCivitaDeriv4Spatial
      dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)

/-- Every connection-derived Ricci component reduces to `(∇²Φ/c²) I₄`; mixed Hessian terms cancel. -/
lemma weakFieldLinearizedRicci4Spatial_eq
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) :
    weakFieldLinearizedRicci4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c =
      !![spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0, 0, 0;
         0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0, 0;
         0, 0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0;
         0, 0, 0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2] := by
  rw [weakFieldLinearizedRicci4Spatial,
    weakFieldLinearizedLeviCivitaDeriv4Spatial_eq_connectionDeriv,
    ricciMatrixFromConnection_zero_eq_linearized]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp only [linearizedRicciMatrixFromConnectionDeriv, Fin.sum_univ_four,
      cons_val_zero, cons_val_one, cons_val_two, cons_val_three, head_cons, tail_cons] <;>
    dsimp [weakFieldLinearizedConnDeriv4Spatial,
      weakFieldLinearizedConnection4Spatial, weakFieldSpatialGradient4,
      kronecker4, minkowskiSign4, spatialLaplacian3] <;>
    (try simp only [cons_val_zero, cons_val_one, cons_val_two, cons_val_three,
      head_cons, tail_cons]) <;>
    norm_num <;>
    ring_nf

/-- The full static carrier specializes to the original plane-symmetric Ricci matrix. -/
lemma weakFieldLinearizedRicci4Spatial_plane
    (dxxΦ c : ℝ) :
    weakFieldLinearizedRicci4Spatial dxxΦ 0 0 0 0 0 c =
      weakFieldLinearizedRicci4 dxxΦ c := by
  rw [weakFieldLinearizedRicci4Spatial_eq]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [spatialLaplacian3, weakFieldLinearizedRicci4,
      Matrix.smul_apply, Matrix.one_apply]

/-- The scalar curvature of the full static connection-derived Ricci carrier. -/
noncomputable def weakFieldLinearizedScalar4Spatial
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) : ℝ :=
  ricciScalarContraction minkowskiMetric4
    (weakFieldLinearizedRicci4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)

/-- `R^(1) = -2∇²Φ/c²` for a general static spatial potential. -/
lemma weakFieldLinearizedScalar4Spatial_eq
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) :
    weakFieldLinearizedScalar4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c =
      -2 * spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2 := by
  rw [weakFieldLinearizedScalar4Spatial, weakFieldLinearizedRicci4Spatial_eq]
  simp [ricciScalarContraction, minkowskiMetric4, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_four, Matrix.smul_apply, Matrix.one_apply]
  ring

/-- The Einstein tensor computed from the complete connection-derived general-static Ricci matrix. -/
noncomputable def weakFieldLinearizedEinstein4Spatial
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  einsteinTensor
    (weakFieldLinearizedRicci4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
    (weakFieldLinearizedScalar4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
    minkowskiMetric4

/-- `G^(1) = diag(2∇²Φ/c²,0,0,0)` for the full static spatial Hessian. -/
lemma weakFieldLinearizedEinstein4Spatial_eq
    (dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c : ℝ) :
    weakFieldLinearizedEinstein4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c =
      !![2 * spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  rw [weakFieldLinearizedEinstein4Spatial, weakFieldLinearizedRicci4Spatial_eq,
    weakFieldLinearizedScalar4Spatial_eq]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [einsteinTensor, minkowskiMetric4, Matrix.smul_apply, Matrix.one_apply] <;>
    ring

/-- The three-dimensional Poisson equation implies the full static linearized Einstein matrix equation. -/
theorem weakFieldLinearizedEFE4Spatial_of_poisson
    (G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ : ℝ) (hc : c ≠ 0)
    (hPoisson : spatialLaplacian3 dxxΦ dyyΦ dzzΦ = 4 * Real.pi * G * ρ) :
    einsteinFieldEquation
      (weakFieldLinearizedRicci4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
      (weakFieldLinearizedScalar4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
      minkowskiMetric4 (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4) := by
  unfold einsteinFieldEquation
  rw [← weakFieldLinearizedEinstein4Spatial,
    weakFieldLinearizedEinstein4Spatial_eq]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [restDustStressEnergy4, Matrix.smul_apply, smul_eq_mul] <;>
    field_simp [hc] <;>
    nlinarith [hPoisson]

/-- The full static rest-dust Einstein equation recovers the three-dimensional Poisson equation. -/
theorem poisson_of_weakFieldLinearizedEFE4Spatial
    (G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ : ℝ) (hc : c ≠ 0)
    (hEFE : einsteinFieldEquation
      (weakFieldLinearizedRicci4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
      (weakFieldLinearizedScalar4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
      minkowskiMetric4 (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)) :
    spatialLaplacian3 dxxΦ dyyΦ dzzΦ = 4 * Real.pi * G * ρ := by
  unfold einsteinFieldEquation at hEFE
  rw [← weakFieldLinearizedEinstein4Spatial,
    weakFieldLinearizedEinstein4Spatial_eq] at hEFE
  have h00 := congrFun (congrFun hEFE 0) 0
  simp [restDustStressEnergy4, Matrix.smul_apply, smul_eq_mul] at h00
  field_simp [hc] at h00
  nlinarith

/-- The full static linearized `3+1` Einstein equation is equivalent to `∇²Φ = 4πGρ`. -/
theorem weakFieldLinearizedEFE4Spatial_iff_poisson
    (G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ : ℝ) (hc : c ≠ 0) :
    einsteinFieldEquation
        (weakFieldLinearizedRicci4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
        (weakFieldLinearizedScalar4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
        minkowskiMetric4 (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
      ↔ spatialLaplacian3 dxxΦ dyyΦ dzzΦ = 4 * Real.pi * G * ρ :=
  ⟨poisson_of_weakFieldLinearizedEFE4Spatial G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ hc,
    weakFieldLinearizedEFE4Spatial_of_poisson G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ hc⟩

/-- The explicit imaginary-sector relation upgrades the full-Laplacian result to the complex equation. -/
theorem weakFieldLinearizedComplexEFE4Spatial_of_poisson
    (G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ : ℝ)
    (Λ S : Matrix (Fin 4) (Fin 4) ℝ) (hc : c ≠ 0)
    (hPoisson : spatialLaplacian3 dxxΦ dyyΦ dzzΦ = 4 * Real.pi * G * ρ)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    complexEinsteinFieldEquation
      (weakFieldLinearizedEinstein4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c) Λ
      (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  rw [complexEinsteinFieldEquation_iff]
  exact ⟨weakFieldLinearizedEFE4Spatial_of_poisson G c ρ dxxΦ dyyΦ dzzΦ
    dxyΦ dxzΦ dyzΦ hc hPoisson, hImaginary⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1

end
