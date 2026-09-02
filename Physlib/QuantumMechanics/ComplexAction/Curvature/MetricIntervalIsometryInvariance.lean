/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness
meta import Zil

/-!
# The invariant interval of a metric, and its Levi-Civita connection

For any metric `g` (any dimension), the **metric distance / interval** `I_g(v) = v ⬝ᵥ (g *ᵥ v)`
is invariant under every isometry of `g`, and the metric's unique Levi-Civita connection
(`LeviCivitaUniqueness`) is the canonical connection compatible with it.  This is the general
statement behind the concrete `(1,1)` Minkowski / Nagao–Nielsen invariant interval: the specific
hyperbolic-boost invariance is the case `g = diag(1,−1)`, `Lᵀ g L = g`.

* `metricInterval_isometry_invariant` — for any `L` with `Lᵀ g L = g`, `I_g(L·v) = I_g(v)`: the
  interval is invariant under the isometry group of the metric.  **The invariant interval.**
* `metricInterval_smul` — `I_{λg}(v) = λ · I_g(v)`: a Weyl rescaling scales the interval by the
  conformal factor.
* `weylRescale_connection_invariant_interval_scales` — the pairing with the connection: a
  *constant* Weyl rescaling leaves the Levi-Civita connection **invariant**
  (`christoffelFromMetric_const_rescale_invariant`) while scaling the interval by `λ`.  So the
  connection is the conformally-invariant content and the interval carries the one global scale
  — the curved-space analogue of Malament's residual dilation.
* `dilationGroup` — the multiplicative group `ℝˣ` represented by scalar linear automorphisms.
* `dilationMatrix_conformal` — a scalar dilation is conformal: `Dᵀ g D = r² g`.
* `metricInterval_dilation` — the interval of a dilated vector scales quadratically by `r²`.
* `dilationWeyl_connection_invariant_interval_invariant` — compensating `v ↦ rv` by the
  constant Weyl rescaling `g ↦ r⁻²g` preserves both the interval and the connection.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance

open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness
open scoped Matrix

/-!

## A. Metric intervals and isometries

-/

/-- **The metric distance / invariant interval** of a metric `g`:
`I_g(v) = ∑_{μν} v^μ g_{μν} v^ν`. -/
def metricInterval {ι : Type*} [Fintype ι] (g : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  v ⬝ᵥ (g *ᵥ v)

/-- **The invariant interval.**  For any metric `g` and any isometry `L` (`Lᵀ g L = g`), the
metric interval is unchanged: `I_g(L·v) = I_g(v)`.  The `(1,1)` Minkowski / Nagao–Nielsen
boost-invariance is the special case `g = diag(1,−1)`. -/
@[zil_level bridge_theorem]
theorem metricInterval_isometry_invariant {ι : Type*} [Fintype ι]
    (g L : Matrix ι ι ℝ) (hL : Lᵀ * g * L = g) (v : ι → ℝ) :
    metricInterval g (L *ᵥ v) = metricInterval g v := by
  have hlemma : ∀ (A : Matrix ι ι ℝ) (x y : ι → ℝ), (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
    intro A x y
    rw [dotProduct_comm (A *ᵥ x) y, Matrix.dotProduct_mulVec,
      dotProduct_comm (y ᵥ* A) x, Matrix.mulVec_transpose]
  unfold metricInterval
  rw [hlemma L v (g *ᵥ (L *ᵥ v)), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL]

/-!

## B. Constant Weyl rescaling

-/

/-- **A Weyl rescaling scales the interval by the conformal factor** `I_{λg}(v) = λ · I_g(v)`. -/
@[zil_level physical_theorem]
theorem metricInterval_smul {ι : Type*} [Fintype ι] (lam : ℝ) (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    metricInterval (lam • g) v = lam * metricInterval g v := by
  unfold metricInterval
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **The connection is conformally invariant; the interval carries the scale.**  A constant Weyl
rescaling `g ↦ λg` (`λ ≠ 0`) leaves the Levi-Civita connection invariant
(`christoffelFromMetric_const_rescale_invariant`) while scaling the metric interval by `λ`.  The
connection sees the metric only up to the global constant; the invariant interval carries it —
the curved-space analogue of Malament's residual conformal dilation. -/
@[zil_level bridge_theorem]
theorem weylRescale_connection_invariant_interval_scales {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    christoffelFromMetric (lam⁻¹ • gInv) (fun κ => lam • dg κ) = christoffelFromMetric gInv dg
      ∧ metricInterval (lam • g) v = lam * metricInterval g v :=
  ⟨christoffelFromMetric_const_rescale_invariant gInv dg hlam, metricInterval_smul lam g v⟩

/-!

## C. The dilation group

The nonzero real scalars act as linear automorphisms.  The bundled monoid homomorphism records
identity, composition, and inverse through the group laws of `ℝˣ` and linear equivalences.

-/

/-- The dilation-group representation of `ℝˣ` on real coordinate vectors. -/
def dilationGroup (ι : Type*) : ℝˣ →* ((ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :=
  DistribMulAction.toModuleAut ℝ (ι → ℝ)

/-- A bundled dilation acts by scalar multiplication. -/
lemma dilationGroup_apply (ι : Type*) (r : ℝˣ) (v : ι → ℝ) :
    dilationGroup ι r v = (r : ℝ) • v := by
  rfl

/-- The coordinate matrix of scalar dilation by `r`. -/
def dilationMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ) : Matrix ι ι ℝ :=
  r • 1

/-- The unit scale gives the identity dilation matrix. -/
@[simp]
lemma dilationMatrix_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    dilationMatrix (ι := ι) 1 = 1 := by
  simp [dilationMatrix]

/-- Matrix multiplication realizes composition of scalar dilations. -/
lemma dilationMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (r s : ℝ) :
    dilationMatrix (ι := ι) (r * s) = dilationMatrix r * dilationMatrix s := by
  simp [dilationMatrix, smul_smul, mul_comm]

/-- A nonzero dilation is inverted by dilation with the reciprocal scale. -/
lemma dilationMatrix_mul_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℝ} (hr : r ≠ 0) : dilationMatrix (ι := ι) r * dilationMatrix r⁻¹ = 1 := by
  rw [← dilationMatrix_mul]
  simp [dilationMatrix, hr]

/-- The scalar dilation matrix acts on a coordinate vector by scalar multiplication. -/
lemma dilationMatrix_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (v : ι → ℝ) : dilationMatrix (ι := ι) r *ᵥ v = r • v := by
  simp [dilationMatrix, Matrix.smul_mulVec]

/-- The bundled dilation group and its matrix presentation act identically. -/
@[zil_level bridge_theorem]
lemma dilationGroup_apply_eq_dilationMatrix_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝˣ) (v : ι → ℝ) : dilationGroup ι r v = dilationMatrix (r : ℝ) *ᵥ v := by
  rw [dilationGroup_apply, dilationMatrix_mulVec]

/-!

## D. Dilation covariance and Weyl compensation

-/

/-- A scalar dilation of a vector scales its metric interval quadratically. -/
@[zil_level physical_theorem]
theorem metricInterval_dilation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    metricInterval g (dilationMatrix r *ᵥ v) = r ^ 2 * metricInterval g v := by
  rw [dilationMatrix_mulVec]
  unfold metricInterval
  simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- A scalar dilation is a conformal transformation of any metric, with factor `r²`. -/
@[zil_level bridge_theorem]
theorem dilationMatrix_conformal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (g : Matrix ι ι ℝ) :
    (dilationMatrix r)ᵀ * g * dilationMatrix r = r ^ 2 • g := by
  simp [dilationMatrix, Matrix.transpose_smul, smul_smul]
  ring_nf

/-- The inverse-square Weyl rescaling exactly compensates a nonzero vector dilation. -/
@[zil_level bridge_theorem]
lemma metricInterval_compensated_dilation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℝ} (hr : r ≠ 0) (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    metricInterval ((r ^ 2)⁻¹ • g) (dilationMatrix r *ᵥ v) = metricInterval g v := by
  rw [metricInterval_smul, metricInterval_dilation]
  field_simp

/-- **Dilation/Weyl invariant geometry.**  A nonzero scalar dilation is accompanied by the
constant Weyl factor `r⁻²`.  The Levi-Civita connection is unchanged and the rescaled metric
evaluated on the dilated vector has exactly the original interval. -/
@[zil_level bridge_theorem]
theorem dilationWeyl_connection_invariant_interval_invariant {ι : Type*}
    [Fintype ι] [DecidableEq ι] (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (r : ℝˣ) (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    let lam := (((r : ℝ) ^ 2)⁻¹)
    christoffelFromMetric (lam⁻¹ • gInv) (fun κ => lam • dg κ) =
        christoffelFromMetric gInv dg
      ∧ metricInterval (lam • g) (dilationGroup ι r v) = metricInterval g v := by
  dsimp only
  constructor
  · exact (weylRescale_connection_invariant_interval_scales gInv dg
      (inv_ne_zero (pow_ne_zero 2 r.ne_zero)) g v).1
  · rw [dilationGroup_apply_eq_dilationMatrix_mulVec]
    exact metricInterval_compensated_dilation r.ne_zero g v

end Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance

zil attach metricInterval_isometry_invariant where
  formalizes @ "claim:metric-interval-is-invariant-under-any-metric-isometry"

zil attach metricInterval_smul where
  supported_by @ "lean:christoffelFromMetric_const_rescale_invariant",
  formalizes @ "claim:constant-weyl-rescaling-scales-the-metric-interval"

zil attach weylRescale_connection_invariant_interval_scales where
  supported_by @ "lean:christoffelFromMetric_const_rescale_invariant",
  supported_by @ "lean:metricInterval_smul",
  formalizes @ "claim:constant-weyl-rescaling-preserves-connection-and-scales-interval",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.\
    christoffelFromMetric_const_rescale_invariant"

zil attach dilationGroup_apply_eq_dilationMatrix_mulVec where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.dilationGroup_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.dilationMatrix_mulVec",
  formalizes @ "claim:bundled-dilation-group-equals-scalar-matrix-action"

zil attach metricInterval_dilation where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.dilationMatrix_mulVec",
  formalizes @ "claim:dilating-a-vector-by-r-scales-its-metric-interval-by-r-squared"

zil attach dilationMatrix_conformal where
  formalizes @ "claim:scalar-dilation-is-conformal-with-factor-r-squared"

zil attach metricInterval_compensated_dilation where
  supported_by @ "lean:metricInterval_dilation",
  supported_by @ "lean:metricInterval_smul",
  formalizes @ "claim:inverse-square-weyl-factor-compensates-dilation"

zil attach dilationWeyl_connection_invariant_interval_invariant where
  supported_by @ "lean:dilationGroup_apply_eq_dilationMatrix_mulVec",
  supported_by @ "lean:metricInterval_compensated_dilation",
  supported_by @ "lean:weylRescale_connection_invariant_interval_scales",
  formalizes @ "claim:dilation-weyl-pair-preserves-connection-and-interval"

zil_file_contract physlib.metricIntervalIsometryInvariance where
  promises "Metric intervals, the real dilation group, and constant-Weyl compensation."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.\
      christoffelFromMetric"
  ]
  forbids_substitutes [
    "dropping the isometry condition L transpose g L equals g",
    "calling a generic scalar dilation an isometry of the fixed metric",
    "claiming connection invariance for a position-dependent Weyl factor",
    "omitting derivative corrections for a local Weyl rescaling"
  ]
  witnessed_by [
    metricInterval_isometry_invariant,
    metricInterval_smul,
    weylRescale_connection_invariant_interval_scales,
    dilationGroup_apply_eq_dilationMatrix_mulVec,
    metricInterval_dilation,
    dilationMatrix_conformal,
    metricInterval_compensated_dilation,
    dilationWeyl_connection_invariant_interval_invariant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.metricIntervalIsometryInvariance
