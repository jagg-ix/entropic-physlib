/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
public import Physlib.QuantumMechanics.ComplexAction.EinsteinCartanAxialTorsion
public import Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral
meta import Zil

/-!
# Metric dilations across tetrad, Cartan, Palatini, and affine gravity

This module transports the constant-Weyl/dilation action of
`MetricIntervalIsometryInvariance` through existing gravity carriers:

* a cotetrad rescaling `E ↦ r⁻¹E` and coordinate dilation `x ↦ rx` preserve the
  tetrad proper separation;
* the Einstein--Cartan Hehl--Datta contact density is quadratic in an axial-current dilation;
* the Dadhich--Pons projective connection is unchanged when the Levi-Civita part undergoes the
  compensated constant-Weyl transformation;
* the Eddington and pure-Lovelock trace-reversed affine tensors are invariant under
  `g ↦ λg`, `g⁻¹ ↦ λ⁻¹g⁻¹`; their first-integral constants transform as
  `c ↦ c / λ`.

## Honest scope

The results are finite-index, pointwise algebra. The Weyl factor is constant. The Ricci and matter
tensors are held fixed in the affine covariance results; no conformal weight for matter is inferred.
The axial-current dilation is an algebraic rescaling, not a derived conformal transformation of a
Dirac spinor. The Dadhich--Pons projective covector is held fixed. No new field equation,
variational principle, or global spacetime evolution is asserted.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped Matrix BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations

open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.EinsteinCartanAxialTorsion
open Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-!

## A. Tetrad realization of the compensated dilation

-/

/-- Rescaling a cotetrad by `r` rescales its reconstructed metric by `r²`. -/
@[zil_level bridge_theorem]
lemma tetradMetric_smul {d : ℕ} (r : ℝ)
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    tetradMetric (r • E) = r ^ 2 • tetradMetric E := by
  simp [tetradMetric, Matrix.transpose_smul, smul_smul]
  ring_nf

/-- The tetrad proper-separation quadratic form is the general `metricInterval`. -/
@[zil_level bridge_theorem]
lemma properSeparationSq_eq_metricInterval {d : ℕ}
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x : (Fin 1 ⊕ Fin d) → ℝ) :
    properSeparationSq E x = metricInterval (tetradMetric E) x := rfl

/-- **Tetrad dilation/Weyl invariance.** The inverse coframe rescaling `E ↦ r⁻¹E`
compensates the coordinate-vector dilation `x ↦ rx`, preserving proper separation exactly. -/
@[zil_level bridge_theorem]
theorem tetradDilationWeyl_properSeparation_invariant {d : ℕ}
    (r : ℝˣ) (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x : (Fin 1 ⊕ Fin d) → ℝ) :
    properSeparationSq ((r : ℝ)⁻¹ • E)
        (dilationGroup (Fin 1 ⊕ Fin d) r x) = properSeparationSq E x := by
  rw [properSeparationSq_eq_metricInterval, properSeparationSq_eq_metricInterval,
    tetradMetric_smul, dilationGroup_apply_eq_dilationMatrix_mulVec]
  simpa [inv_pow] using
    metricInterval_compensated_dilation r.ne_zero (tetradMetric E) x

/-!

## B. Einstein--Cartan axial-current scaling

-/

/-- The Einstein--Cartan axial-current norm is the Euclidean metric interval. -/
@[zil_level bridge_theorem]
lemma axialCurrentNormSq_eq_metricInterval_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] (J5 : ι → ℝ) :
    axialCurrentNormSq J5 = metricInterval (1 : Matrix ι ι ℝ) J5 := by
  simp [axialCurrentNormSq, metricInterval, Matrix.one_mulVec, dotProduct]
  congr 1
  funext i
  ring_nf

/-- **Einstein--Cartan dilation law.** Dilating the axial current by `r` scales the eliminated
Hehl--Datta contact density by `r²`, matching the quadratic metric-interval law. -/
@[zil_level physical_theorem]
theorem hehlDattaContactDensity_dilation {ι : Type*}
    [Fintype ι] [DecidableEq ι] (kappa : ℝ) (r : ℝˣ) (J5 : ι → ℝ) :
    hehlDattaContactDensity kappa (dilationGroup ι r J5) =
      (r : ℝ) ^ 2 * hehlDattaContactDensity kappa J5 := by
  unfold hehlDattaContactDensity axialCurrentNormSq
  rw [dilationGroup_apply]
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  ring_nf

/-- The reduced Cartan equation is covariant under the compensated transformation
`κ ↦ κ / r²`, `K ↦ K / r`, and `J₅ ↦ r J₅`. -/
@[zil_level bridge_theorem]
theorem cartanResidual_compensated_dilation
    (kappa K J5 : ℝ) (r : ℝˣ) :
    cartanResidual (kappa / (r : ℝ) ^ 2) (K / (r : ℝ)) ((r : ℝ) * J5) =
      cartanResidual kappa K J5 / (r : ℝ) := by
  unfold cartanResidual
  field_simp [r.ne_zero]

/-- **Compensated Einstein--Cartan dilation.** Giving the coupling inverse-square
Weyl weight exactly compensates the quadratic axial-current dilation, so the
eliminated Hehl--Datta density is invariant. -/
@[zil_level physical_theorem]
theorem hehlDattaContactDensity_compensated_dilation_invariant {ι : Type*}
    [Fintype ι] [DecidableEq ι] (kappa : ℝ) (r : ℝˣ) (J5 : ι → ℝ) :
    hehlDattaContactDensity (kappa / (r : ℝ) ^ 2) (dilationGroup ι r J5) =
      hehlDattaContactDensity kappa J5 := by
  rw [hehlDattaContactDensity_dilation]
  unfold hehlDattaContactDensity
  field_simp [r.ne_zero]

/-!

## C. Dadhich--Pons projective Palatini connection

-/

/-- **Dadhich--Pons under compensated dilation.** The constant-Weyl transformation preserves the
Levi-Civita part and therefore preserves the full Palatini connection after adjoining the same
projective mode `C(U)`. Simultaneously, the compensated metric interval is invariant. -/
@[zil_level bridge_theorem]
theorem dadhichPons_projective_dilationWeyl_invariant {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (U : ι → ℝ) (r : ℝˣ) (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    let lam := (((r : ℝ) ^ 2)⁻¹)
    entropicConnection
        (christoffelFromMetric (lam⁻¹ • gInv) (fun κ => lam • dg κ))
        (projectiveConnection U) =
      entropicConnection (christoffelFromMetric gInv dg) (projectiveConnection U)
      ∧ metricInterval (lam • g) (dilationGroup ι r v) = metricInterval g v := by
  dsimp only
  have h := dilationWeyl_connection_invariant_interval_invariant gInv dg r g v
  exact ⟨congrArg (fun Γ => entropicConnection Γ (projectiveConnection U)) h.1, h.2⟩

/-- Torsion is additive under the repository's connection sum. -/
lemma torsion_entropicConnection {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (Γ C : ι → Matrix ι ι ℝ) (l μ ν : ι) :
    torsion (entropicConnection Γ C) l μ ν = torsion Γ l μ ν + torsion C l μ ν := by
  simp only [torsion_apply, entropicConnection, Matrix.add_apply]
  ring

/-- A projective connection determines its covector uniquely on a nonempty index carrier. -/
@[zil_level bridge_theorem]
theorem projectiveConnection_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (U V : ι → ℝ) (h : projectiveConnection U = projectiveConnection V) : U = V := by
  funext μ
  let l : ι := Classical.choice ‹Nonempty ι›
  have hl := congrFun (congrFun (congrFun h l) μ) l
  simpa [projectiveConnection_apply] using hl

/-- **Dadhich--Pons reconstruction.** In dimension at least two, the projective
covector is recovered
from the normalized torsion trace `U_μ = T^ν_{μν} / (D - 1)`. -/
@[zil_level physical_theorem]
theorem projectiveCovector_recovered_from_torsion_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι] (U : ι → ℝ) (hd : 2 ≤ Fintype.card ι) (μ : ι) :
    U μ = (∑ ν, torsion (projectiveConnection U) ν μ ν) /
      ((Fintype.card ι : ℝ) - 1) := by
  rw [torsion_projectiveConnection_trace]
  have hne : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hlt : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    linarith
  field_simp

/-- Adding a projective mode to a torsion-free base connection leaves exactly the projective torsion
trace `(D - 1) U`. -/
@[zil_level bridge_theorem]
theorem entropicConnection_projective_torsion_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Γ : ι → Matrix ι ι ℝ) (U : ι → ℝ)
    (hΓ : IsTorsionFree Γ) (μ : ι) :
    (∑ ν, torsion (entropicConnection Γ (projectiveConnection U)) ν μ ν) =
      ((Fintype.card ι : ℝ) - 1) * U μ := by
  simp_rw [torsion_entropicConnection]
  have hzero : ∀ ν, torsion Γ ν μ ν = 0 := by
    intro ν
    rw [torsion_apply]
    have hentry := congrFun (congrFun (hΓ ν) μ) ν
    simpa [Matrix.transpose_apply] using sub_eq_zero.mpr hentry.symm
  simp_rw [hzero, zero_add]
  exact torsion_projectiveConnection_trace U μ

/-- Vanishing torsion trace fixes precisely the zero projective covector over a
torsion-free base. -/
@[zil_level bridge_theorem]
theorem entropicConnection_projective_torsionTrace_zero_iff {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Γ : ι → Matrix ι ι ℝ) (U : ι → ℝ)
    (hΓ : IsTorsionFree Γ) (hd : 2 ≤ Fintype.card ι) :
    (∀ μ, (∑ ν, torsion (entropicConnection Γ (projectiveConnection U)) ν μ ν) = 0) ↔
      U = 0 := by
  constructor
  · intro h
    funext μ
    rw [Pi.zero_apply]
    have htrace := entropicConnection_projective_torsion_trace Γ U hΓ μ
    rw [h μ] at htrace
    have hne : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
      have hlt : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
      linarith
    exact (mul_eq_zero.mp htrace.symm).resolve_left hne
  · intro h
    subst U
    intro μ
    simp [entropicConnection_projective_torsion_trace Γ 0 hΓ μ]

/-- **Unique Dadhich--Pons gauge-fixed representative.** On a torsion-free base connection, imposing
zero torsion trace removes the entire projective orbit and returns the base connection itself. -/
@[zil_level physical_theorem]
theorem dadhichPons_traceGauge_unique_representative {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Γ : ι → Matrix ι ι ℝ) (U : ι → ℝ)
    (hΓ : IsTorsionFree Γ) (hd : 2 ≤ Fintype.card ι)
    (htrace : ∀ μ,
      (∑ ν, torsion (entropicConnection Γ (projectiveConnection U)) ν μ ν) = 0) :
    entropicConnection Γ (projectiveConnection U) = Γ := by
  have hU := (entropicConnection_projective_torsionTrace_zero_iff Γ U hΓ hd).mp htrace
  subst U
  funext l
  ext μ ν
  simp [entropicConnection, projectiveConnection_apply]

/-!

## D. Shared trace-reversal covariance

-/

/-- Scaling the inverse metric scales its contraction with a fixed tensor linearly. -/
lemma metricTrace_smul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (gInv T : Matrix ι ι ℝ) :
    metricTrace (a • gInv) T = a * metricTrace gInv T := by
  simp [metricTrace, Matrix.trace_smul, smul_eq_mul]

/-- A general trace-reversal term is invariant under simultaneous constant rescaling of a metric
and inverse metric. The statement does not require the trace denominator to be nonzero. -/
lemma traceReversedWithDenominator_constWeyl {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (den : ℝ) (gInv g T : Matrix ι ι ℝ) :
    T - (metricTrace (lam⁻¹ • gInv) T / den) • (lam • g) =
      T - (metricTrace gInv T / den) • g := by
  rw [metricTrace_smul_left]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  calc
    (lam⁻¹ * metricTrace gInv T / den) * (lam * g i j) =
        (lam⁻¹ * lam) * (metricTrace gInv T / den * g i j) := by ring_nf
    _ = metricTrace gInv T / den * g i j := by simp [hlam]

/-- Simultaneous inverse Weyl weights preserve the inverse-metric identity. -/
lemma constWeyl_inverseMetric_mul_metric {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (gInv g : Matrix ι ι ℝ) (hgInv : gInv * g = 1) :
    (lam⁻¹ • gInv) * (lam • g) = 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hlam, one_smul, hgInv]

/-!

## E. Eddington and Lovelock--Palatini affine tensors

-/

/-- The Eddington trace-reversed matter tensor is invariant under a constant Weyl rescaling. -/
@[zil_level bridge_theorem]
lemma traceReversedMatter_constWeyl {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (gInv g T : Matrix ι ι ℝ) :
    traceReversedMatter (lam⁻¹ • gInv) (lam • g) T =
      traceReversedMatter gInv g T := by
  unfold traceReversedMatter
  exact traceReversedWithDenominator_constWeyl hlam
    ((Fintype.card ι : ℝ) - 2) gInv g T

/-- The Eddington matter-affine tensor is invariant when `Ric` and `T` are held fixed. -/
@[zil_level bridge_theorem]
lemma matterAffineTensor_constWeyl {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (Ric gInv g T : Matrix ι ι ℝ) (kappa : ℝ) :
    matterAffineTensor Ric (lam⁻¹ • gInv) (lam • g) T kappa =
      matterAffineTensor Ric gInv g T kappa := by
  simp [matterAffineTensor, traceReversedMatter_constWeyl hlam]

/-- The Eddington affine tensor is invariant under the Weyl factor induced by a dilation. -/
@[zil_level bridge_theorem]
theorem eddingtonMatterAffine_dilationWeyl_invariant {ι : Type*}
    [Fintype ι] [DecidableEq ι] (r : ℝˣ)
    (Ric gInv g T : Matrix ι ι ℝ) (kappa : ℝ) :
    let lam := (((r : ℝ) ^ 2)⁻¹)
    matterAffineTensor Ric (lam⁻¹ • gInv) (lam • g) T kappa =
      matterAffineTensor Ric gInv g T kappa := by
  dsimp only
  exact matterAffineTensor_constWeyl
    (inv_ne_zero (pow_ne_zero 2 r.ne_zero)) Ric gInv g T kappa

/-- **Eddington first-integral covariance.** If `M = c g`, then after
`g ↦ λg`, `g⁻¹ ↦ λ⁻¹g⁻¹`, the same affine tensor satisfies `M = (c/λ)(λg)`. -/
@[zil_level physical_theorem]
theorem eddingtonFirstIntegral_constWeyl_covariant {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (Ric gInv g T : Matrix ι ι ℝ) (kappa firstConstant : ℝ)
    (hfirst : matterAffineTensor Ric gInv g T kappa = firstConstant • g) :
    matterAffineTensor Ric (lam⁻¹ • gInv) (lam • g) T kappa =
      (firstConstant / lam) • (lam • g) := by
  rw [matterAffineTensor_constWeyl hlam, hfirst]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- The pure-Lovelock trace-reversed matter tensor has the same constant-Weyl invariance. -/
@[zil_level bridge_theorem]
lemma lovelockTraceReversedMatter_constWeyl {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (m : ℕ) (gInv g T : Matrix ι ι ℝ) :
    lovelockTraceReversedMatter m (lam⁻¹ • gInv) (lam • g) T =
      lovelockTraceReversedMatter m gInv g T := by
  unfold lovelockTraceReversedMatter
  exact traceReversedWithDenominator_constWeyl hlam
    ((Fintype.card ι : ℝ) - 2 * (m : ℝ)) gInv g T

/-- The pure-Lovelock matter-affine tensor is constant-Weyl invariant. -/
@[zil_level bridge_theorem]
lemma lovelockAffineTensor_constWeyl {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (m : ℕ) (RicM gInv g T : Matrix ι ι ℝ) (kappa : ℝ) :
    lovelockAffineTensor m RicM (lam⁻¹ • gInv) (lam • g) T kappa =
      lovelockAffineTensor m RicM gInv g T kappa := by
  simp [lovelockAffineTensor, lovelockTraceReversedMatter_constWeyl hlam]

/-- The pure-Lovelock affine tensor is invariant under the Weyl factor induced by a dilation. -/
@[zil_level bridge_theorem]
theorem lovelockMatterAffine_dilationWeyl_invariant {ι : Type*}
    [Fintype ι] [DecidableEq ι] (r : ℝˣ) (m : ℕ)
    (RicM gInv g T : Matrix ι ι ℝ) (kappa : ℝ) :
    let lam := (((r : ℝ) ^ 2)⁻¹)
    lovelockAffineTensor m RicM (lam⁻¹ • gInv) (lam • g) T kappa =
      lovelockAffineTensor m RicM gInv g T kappa := by
  dsimp only
  exact lovelockAffineTensor_constWeyl
    (inv_ne_zero (pow_ne_zero 2 r.ne_zero)) m RicM gInv g T kappa

/-- **Pure-Lovelock first-integral covariance.** If `M_m = c g`, a constant Weyl rescaling
changes only the presentation of the integration constant, from `c` to `c / λ`. -/
@[zil_level physical_theorem]
theorem lovelockFirstIntegral_constWeyl_covariant {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (m : ℕ) (RicM gInv g T : Matrix ι ι ℝ) (kappa firstConstant : ℝ)
    (hfirst : lovelockAffineTensor m RicM gInv g T kappa = firstConstant • g) :
    lovelockAffineTensor m RicM (lam⁻¹ • gInv) (lam • g) T kappa =
      (firstConstant / lam) • (lam • g) := by
  rw [lovelockAffineTensor_constWeyl hlam, hfirst]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- **Weyl-covariant Eddington endpoint.** The rescaled affine first integral
derives the cosmological
Einstein equation for the rescaled metric, with integration constant `c / λ`. -/
@[zil_level physical_theorem]
theorem eddingtonFirstIntegral_constWeyl_derives_einsteinLambda {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (Ric gInv g T : Matrix ι ι ℝ) (kappa firstConstant : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2)
    (hgInv : gInv * g = 1)
    (hfirst : matterAffineTensor Ric gInv g T kappa = firstConstant • g) :
    einsteinFieldEquationCosmological Ric
      (metricTrace (lam⁻¹ • gInv) Ric) (lam • g) T
      (eddingtonLambda (ι := ι) (firstConstant / lam)) kappa := by
  apply firstIntegral_derives_einsteinLambda Ric (lam⁻¹ • gInv) (lam • g) T
    kappa (firstConstant / lam) hdim
    (constWeyl_inverseMetric_mul_metric hlam gInv g hgInv)
  exact eddingtonFirstIntegral_constWeyl_covariant hlam Ric gInv g T kappa firstConstant hfirst

/-- The Ricci/Lovelock trace carries inverse Weyl weight when its tensor argument is fixed. -/
lemma metricTrace_constWeyl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {lam : ℝ} (gInv T : Matrix ι ι ℝ) :
    metricTrace (lam⁻¹ • gInv) T = lam⁻¹ * metricTrace gInv T :=
  metricTrace_smul_left lam⁻¹ gInv T

/-- **Weyl-covariant pure-Lovelock endpoint.** The rescaled affine first integral derives the
pure-Lovelock field equation with `L ↦ L / λ` and first-integral constant `c ↦ c / λ`. -/
@[zil_level physical_theorem]
theorem lovelockFirstIntegral_constWeyl_derives_fieldEquation {ι : Type*}
    [Fintype ι] [DecidableEq ι] {lam : ℝ} (hlam : lam ≠ 0)
    (m : ℕ) (hm : m ≠ 0)
    (RicM gInv g T : Matrix ι ι ℝ) (L kappa firstConstant : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2 * (m : ℝ))
    (hgInv : gInv * g = 1)
    (htraceRic : metricTrace gInv RicM = (m : ℝ) * L)
    (hfirst : lovelockAffineTensor m RicM gInv g T kappa = firstConstant • g) :
    RicM - ((L / lam) / 2) • (lam • g) +
        lovelockEddingtonLambda (ι := ι) m (firstConstant / lam) • (lam • g) =
      kappa • T := by
  apply lovelockFirstIntegral_derives_fieldEquation m hm RicM (lam⁻¹ • gInv) (lam • g) T
    (L / lam) kappa (firstConstant / lam) hdim
    (constWeyl_inverseMetric_mul_metric hlam gInv g hgInv)
  · rw [metricTrace_constWeyl, htraceRic]
    field_simp [hlam]
  · exact lovelockFirstIntegral_constWeyl_covariant hlam m RicM gInv g T kappa
      firstConstant hfirst

end Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricDilationGravityFormulations

zil attach tetradDilationWeyl_properSeparation_invariant where
  supported_by @ "lean:dilationGroup_apply_eq_dilationMatrix_mulVec",
  supported_by @ "lean:metricInterval_compensated_dilation",
  formalizes @ "claim:inverse-coframe-scaling-compensates-coordinate-dilation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.\
    TetradADMGravity.tetradMetric"

zil attach hehlDattaContactDensity_dilation where
  formalizes @ "claim:einstein-cartan-contact-density-scales-quadratically",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.\
    EinsteinCartanAxialTorsion.hehlDattaContactDensity",
  caveat @ "claim:algebraic-current-rescaling-not-derived-spinor-conformal-weight"

zil attach hehlDattaContactDensity_compensated_dilation_invariant where
  supported_by @ "lean:hehlDattaContactDensity_dilation",
  formalizes @ "claim:einstein-cartan-contact-density-is-compensated-dilation-invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.\
    EinsteinCartanAxialTorsion.cartanResidual",
  caveat @ "claim:coupling-and-current-weights-are-explicit-algebraic-transformations"

zil attach dadhichPons_projective_dilationWeyl_invariant where
  formalizes @ "claim:dadhich-pons-projective-connection-survives-constant-weyl-dilation",
  supported_by @ "paper:dadhich-pons-einstein-palatini-equivalence",
  caveat @ "claim:projective-covector-is-held-fixed"

zil attach projectiveCovector_recovered_from_torsion_trace where
  formalizes @ "claim:dadhich-pons-projective-covector-is-reconstructed-from-torsion-trace",
  supported_by @ "paper:dadhich-pons-einstein-palatini-equivalence"

zil attach dadhichPons_traceGauge_unique_representative where
  formalizes @ "claim:zero-torsion-trace-selects-unique-projective-palatini-representative",
  supported_by @ "paper:dadhich-pons-einstein-palatini-equivalence",
  caveat @ "claim:uniqueness-is-within-the-explicit-projective-orbit"

zil attach eddingtonMatterAffine_dilationWeyl_invariant where
  formalizes @ "claim:eddington-affine-tensor-is-constant-weyl-invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.\
    EddingtonAffineFirstIntegral.matterAffineTensor",
  caveat @ "claim:ricci-and-matter-tensors-are-held-fixed"

zil attach eddingtonFirstIntegral_constWeyl_covariant where
  formalizes @ "claim:eddington-first-integral-constant-has-inverse-weyl-weight",
  supported_by @ "paper:eddington-affine-first-integral"

zil attach eddingtonFirstIntegral_constWeyl_derives_einsteinLambda where
  supported_by @ "lean:eddingtonFirstIntegral_constWeyl_covariant",
  formalizes @ "claim:weyl-covariant-eddington-first-integral-derives-einstein-lambda",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.\
    EddingtonAffineFirstIntegral.firstIntegral_derives_einsteinLambda"

zil attach lovelockMatterAffine_dilationWeyl_invariant where
  formalizes @ "claim:pure-lovelock-affine-tensor-is-constant-weyl-invariant",
  supported_by @ "paper:dadhich-pons-lovelock-palatini-characterization",
  caveat @ "claim:ricci-and-matter-tensors-are-held-fixed"

zil attach lovelockFirstIntegral_constWeyl_covariant where
  formalizes @ "claim:pure-lovelock-first-integral-constant-has-inverse-weyl-weight",
  supported_by @ "paper:dadhich-pons-lovelock-palatini-characterization"

zil attach lovelockFirstIntegral_constWeyl_derives_fieldEquation where
  supported_by @ "lean:lovelockFirstIntegral_constWeyl_covariant",
  formalizes @ "claim:weyl-covariant-first-integral-derives-pure-lovelock-field-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.\
    EddingtonAffineFirstIntegral.lovelockFirstIntegral_derives_fieldEquation"

zil_file_contract physlib.metricDilationGravityFormulations where
  promises "Constant-Weyl transport and projective uniqueness across tetrad,\
    Cartan, Palatini, and affine gravity."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.\
      MetricIntervalIsometryInvariance.dilationGroup",
    "lean:Physlib.QuantumMechanics.ComplexAction.EinsteinPalatiniProjectiveGauge.\
      projectiveConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.\
      lovelockAffineTensor"
  ]
  forbids_substitutes [
    "using a position-dependent Weyl factor",
    "deriving a spinor conformal weight from axial-current rescaling",
    "transforming Ricci or matter without an explicit conformal-weight theorem",
    "claiming a new field equation or global evolution result"
  ]
  witnessed_by [
    tetradDilationWeyl_properSeparation_invariant,
    hehlDattaContactDensity_dilation,
    hehlDattaContactDensity_compensated_dilation_invariant,
    dadhichPons_projective_dilationWeyl_invariant,
    projectiveCovector_recovered_from_torsion_trace,
    dadhichPons_traceGauge_unique_representative,
    eddingtonMatterAffine_dilationWeyl_invariant,
    eddingtonFirstIntegral_constWeyl_covariant,
    eddingtonFirstIntegral_constWeyl_derives_einsteinLambda,
    lovelockMatterAffine_dilationWeyl_invariant,
    lovelockFirstIntegral_constWeyl_covariant,
    lovelockFirstIntegral_constWeyl_derives_fieldEquation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.metricDilationGravityFormulations
