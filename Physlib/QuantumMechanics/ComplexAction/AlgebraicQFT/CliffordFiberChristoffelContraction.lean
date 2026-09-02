/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
meta import Zil

/-!
# Clifford-fiber contraction and the flat Nagao–Nielsen action geometry

`CliffordFiberLeviCivita` builds the *first-kind* Christoffel symbol
`christoffelFirstKind dg k i j = ½(∂ᵢg_{jk}+∂ⱼg_{ik}−∂ₖg_{ij})` (fully lowered, no metric
inverse) that transports the `Cl(TM) ≅ ℍ ⊕ ℍ` spinor fiber and underlies the Bell
three-faces / Nagao–Nielsen no-signaling contour.  `LeviCivitaUniqueness` builds the
*second-kind* connection `christoffelFromMetric` (raised, `Γ^σ_{μν}`) and its uniqueness.

This module links the two.  Contracting the second-kind connection against the metric
(`loweredSymbol`) reproduces the Clifford fiber's first-kind Christoffel exactly:

`∑_σ Γ^σ_{lμ} g_{σν} = christoffelFirstKind dg ν l μ`
(`loweredChristoffel_eq_firstKind`),

which is just the `christoffel_contraction` Koszul value read in the fiber module's index
convention (using metric-derivative symmetry `∂_κ g_{ab}=∂_κ g_{ba}`).  Combined with the
second-kind uniqueness, *any* torsion-free metric-compatible connection lowers to that same
fiber Christoffel (`lowered_torsionFree_metricCompatible_eq_firstKind`) — so the unique
metric connection is the one whose Clifford-fiber transport carries the Bell contour.

The same uniqueness theorem closes the Nagao–Nielsen complex-action geometry.  Its quadratic
form `nnLorentzForm q = q.re² - q.im² = (q²).re` is the flat `(1,1)` Minkowski interval on the
real/imaginary action plane.  The existing hyperbolic `lorentzBoost` therefore acts as an exact
metric isometry (`nnActionBoost_preserves_interval`), preserving both `Re(q²)` and the convergence
cone.  Since this metric is constant, its derivative is zero and the earlier Christoffel
uniqueness gives an actual existence-and-uniqueness result: the only torsion-free compatible
connection is the zero connection (`nnFlatLeviCivita_existsUnique`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction

open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open scoped Matrix

/-- **The second-kind Levi-Civita connection contracts to the Clifford-fiber first-kind
Christoffel.**  Lowering `christoffelFromMetric` with the metric reproduces the
`christoffelFirstKind` of `CliffordFiberLeviCivita` (in its `Γ_{k,ij}` index convention),
via the `christoffel_contraction` Koszul value and metric-derivative symmetry. -/
@[zil_level bridge_theorem]
theorem loweredChristoffel_eq_firstKind {n : ℕ}
    (g gInv : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Fin n → Fin n → ℝ)
    (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    (hsym : ∀ κ a b, dg κ a b = dg κ b a) (l μ ν : Fin n) :
    loweredSymbol (christoffelFromMetric gInv (fun k => Matrix.of (dg k))) g l μ ν
      = christoffelFirstKind dg ν l μ := by
  unfold loweredSymbol
  rw [christoffel_contraction (fun k => Matrix.of (dg k)) hgi hinv l μ ν]
  unfold christoffelFirstKind
  simp only [Matrix.of_apply]
  rw [hsym l ν μ, hsym μ ν l]
  ring

/-- **Any torsion-free metric-compatible connection lowers to the Clifford-fiber Christoffel.**
By second-kind uniqueness such a connection *is* `christoffelFromMetric`, so its metric
contraction is the fiber's `christoffelFirstKind`: the unique metric connection is exactly the
one whose `Cl(TM) ≅ ℍ ⊕ ℍ` spinor transport carries the Bell no-signaling contour. -/
@[zil_level bridge_theorem]
theorem lowered_torsionFree_metricCompatible_eq_firstKind {n : ℕ}
    {g gInv : Matrix (Fin n) (Fin n) ℝ} {Γ : Fin n → Matrix (Fin n) (Fin n) ℝ}
    (dg : Fin n → Fin n → Fin n → ℝ)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    (hsym : ∀ κ a b, dg κ a b = dg κ b a)
    (htf : IsTorsionFree Γ) (hmc : IsMetricCompatible Γ (fun k => Matrix.of (dg k)) g)
    (l μ ν : Fin n) :
    loweredSymbol Γ g l μ ν = christoffelFirstKind dg ν l μ := by
  have hdg : ∀ κ, (Matrix.of (dg κ))ᵀ = Matrix.of (dg κ) := fun κ => by
    ext a b; simp only [Matrix.transpose_apply, Matrix.of_apply]; exact hsym κ b a
  rw [christoffel_unique_of_torsionFree_metricCompatible (fun k => Matrix.of (dg k))
      hg hgi hinv hdg htf hmc]
  exact loweredChristoffel_eq_firstKind g gInv dg hgi hinv hsym l μ ν

/-! ## The flat Nagao–Nielsen real/imaginary-action geometry -/

/-- The `(1,1)` metric on the real/imaginary-action plane. -/
def nnMinkowskiMetric : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The real and imaginary components of a complex action as a two-vector. -/
def nnActionVector (q : ℂ) : Fin 2 → ℝ := ![q.re, q.im]

/-- The matrix of the hyperbolic action boost. -/
def nnActionBoostMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh η, Real.sinh η; Real.sinh η, Real.cosh η]

/-- **The hyperbolic rotation of real and imaginary action.**  It applies the repository's
`(1,1)` rapidity boost to `(q.re, q.im)` and returns the transformed complex action. -/
noncomputable def nnActionBoost (η : ℝ) (q : ℂ) : ℂ :=
  ⟨(lorentzBoost η q.re q.im).1, (lorentzBoost η q.re q.im).2⟩

/-- **The Nagao–Nielsen form is the general metric interval** specialized to the `(1,1)`
metric and the real/imaginary-action vector. -/
@[zil_level bridge_theorem]
theorem nnLorentzForm_eq_metricInterval (q : ℂ) :
    nnLorentzForm q = metricInterval nnMinkowskiMetric (nnActionVector q) := by
  simp [nnLorentzForm, metricInterval, nnMinkowskiMetric, nnActionVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The complex action boost is exactly multiplication by its `SO(1,1)` matrix on the
real/imaginary component vector. -/
@[zil_level bridge_theorem]
theorem nnActionVector_boost (η : ℝ) (q : ℂ) :
    nnActionVector (nnActionBoost η q) = nnActionBoostMatrix η *ᵥ nnActionVector q := by
  funext i
  fin_cases i <;>
    simp [nnActionVector, nnActionBoost, nnActionBoostMatrix, lorentzBoost,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The action-boost matrix is an isometry of the `(1,1)` metric:** `Lᵀ g L = g`. -/
@[zil_level bridge_theorem]
theorem nnActionBoostMatrix_isometry (η : ℝ) :
    (nnActionBoostMatrix η)ᵀ * nnMinkowskiMetric * nnActionBoostMatrix η = nnMinkowskiMetric := by
  have h := Real.cosh_sq_sub_sinh_sq η
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nnActionBoostMatrix, nnMinkowskiMetric, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    nlinarith [h]

/-- **The real/imaginary-action boost is a metric isometry.**  The invariant interval is
exactly the Nagao–Nielsen form `q.re² - q.im²`; the pre-existing hyperbolic Lorentz boost
preserves it for every rapidity and every complex action. -/
@[zil_level bridge_theorem]
theorem nnActionBoost_preserves_interval (η : ℝ) (q : ℂ) :
    nnLorentzForm (nnActionBoost η q) = nnLorentzForm q := by
  rw [nnLorentzForm_eq_metricInterval, nnLorentzForm_eq_metricInterval,
    nnActionVector_boost]
  exact metricInterval_isometry_invariant nnMinkowskiMetric (nnActionBoostMatrix η)
    (nnActionBoostMatrix_isometry η) (nnActionVector q)

/-- **Equivalently, the boost preserves the real part of the squared complex action.**
This uses `nnLorentzForm q = (q²).re`, so the invariant is intrinsic to the complex number and
not merely a separately declared coordinate expression. -/
@[zil_level bridge_theorem]
theorem nnActionBoost_preserves_real_square (η : ℝ) (q : ℂ) :
    ((nnActionBoost η q) ^ 2).re = (q ^ 2).re := by
  rw [← nnLorentzForm_eq_re_sq, nnActionBoost_preserves_interval,
    nnLorentzForm_eq_re_sq]

/-- **The opposite-rapidity boost is the inverse action.**  Applying rapidity `η` and then
`-η` recovers both real and imaginary action components exactly. -/
@[zil_level bridge_theorem]
theorem nnActionBoost_neg_comp (η : ℝ) (q : ℂ) :
    nnActionBoost (-η) (nnActionBoost η q) = q := by
  apply Complex.ext
  · simp [nnActionBoost, lorentzBoost, Real.cosh_neg, Real.sinh_neg]
    linear_combination q.re * Real.cosh_sq_sub_sinh_sq η
  · simp [nnActionBoost, lorentzBoost, Real.cosh_neg, Real.sinh_neg]
    linear_combination q.im * Real.cosh_sq_sub_sinh_sq η

/-- Every action boost is injective because the opposite rapidity is an explicit left inverse. -/
@[zil_level bridge_theorem]
theorem nnActionBoost_injective (η : ℝ) : Function.Injective (nnActionBoost η) := by
  intro q r h
  have hi := congrArg (nnActionBoost (-η)) h
  simpa only [nnActionBoost_neg_comp] using hi

/-- The action boost fixes the zero complex residual. -/
theorem nnActionBoost_zero (η : ℝ) : nnActionBoost η 0 = 0 := by
  apply Complex.ext <;> simp [nnActionBoost, lorentzBoost]

/-- **A boosted complex residual vanishes exactly when the original residual vanishes.** -/
@[zil_level bridge_theorem]
theorem nnActionBoost_eq_zero_iff (η : ℝ) (q : ℂ) :
    nnActionBoost η q = 0 ↔ q = 0 := by
  constructor
  · intro h
    apply nnActionBoost_injective η
    exact h.trans (nnActionBoost_zero η).symm
  · rintro rfl
    exact nnActionBoost_zero η

/-- **The Nagao–Nielsen convergence cone is boost-invariant.**  Hyperbolic mixing of real and
imaginary action cannot move a contour into or out of the timelike region
`0 < nnLorentzForm`. -/
@[zil_level bridge_theorem]
theorem nnActionBoost_converges_iff (η : ℝ) (q : ℂ) :
    nnConverges (nnActionBoost η q) ↔ nnConverges q := by
  unfold nnConverges
  rw [nnActionBoost_preserves_interval]

/-! ### Uniqueness of the boost-invariant symmetric form -/

/-- A general real symmetric quadratic form on the real/imaginary-action plane.  The three
coefficients are respectively its real diagonal, mixed, and imaginary diagonal entries. -/
def nnSymmetricForm (a b c : ℝ) (q : ℂ) : ℝ :=
  a * q.re ^ 2 + 2 * b * q.re * q.im + c * q.im ^ 2

/-- The coefficient family with zero mixed term and opposite diagonal entries is precisely a
scalar multiple of the Nagao–Nielsen Lorentz form. -/
theorem nnSymmetricForm_minkowski (a : ℝ) (q : ℂ) :
    nnSymmetricForm a 0 (-a) q = a * nnLorentzForm q := by
  simp [nnSymmetricForm, nnLorentzForm]
  ring

/-- **Boost invariance determines the symmetric form up to scale.**  If a real symmetric
quadratic form on `(Re q, Im q)` is invariant under every Nagao–Nielsen action boost, then its
mixed coefficient vanishes and its imaginary diagonal coefficient is the negative of its real
coefficient.  Thus it is a scalar multiple of `nnLorentzForm`; this is a classification theorem,
not merely another preservation identity. -/
@[zil_level bridge_theorem]
theorem nnSymmetricForm_invariant_unique {a b c : ℝ}
    (hinv : ∀ η q,
      nnSymmetricForm a b c (nnActionBoost η q) = nnSymmetricForm a b c q) :
    b = 0 ∧ c = -a := by
  have hp := hinv 1 (1 : ℂ)
  have hm := hinv (-1) (1 : ℂ)
  norm_num [nnSymmetricForm, nnActionBoost, lorentzBoost] at hp hm
  have hcosh : Real.cosh (1 : ℝ) ≠ 0 := ne_of_gt (Real.cosh_pos 1)
  have hsinh : Real.sinh (1 : ℝ) ≠ 0 := Real.sinh_ne_zero.mpr (by norm_num)
  have hb : b = 0 := by
    apply mul_left_cancel₀ hcosh
    apply mul_right_cancel₀ hsinh
    nlinarith [hp, hm]
  refine ⟨hb, ?_⟩
  rw [hb] at hp
  norm_num at hp
  have hhyper := Real.cosh_sq_sub_sinh_sq (1 : ℝ)
  have hsum : (a + c) * Real.sinh 1 ^ 2 = 0 := by
    linear_combination hp - a * hhyper
  have hac : a + c = 0 :=
    (mul_eq_zero.mp hsum).resolve_right (pow_ne_zero 2 hsinh)
  linarith

/-- **Exact classification of invariant symmetric forms.**  Invariance under the full
real/imaginary rapidity family holds exactly when the form is `a · nnLorentzForm`. -/
@[zil_level bridge_theorem]
theorem nnSymmetricForm_invariant_iff {a b c : ℝ} :
    (∀ η q,
      nnSymmetricForm a b c (nnActionBoost η q) = nnSymmetricForm a b c q) ↔
      b = 0 ∧ c = -a := by
  constructor
  · exact nnSymmetricForm_invariant_unique
  · rintro ⟨rfl, rfl⟩ η q
    rw [nnSymmetricForm_minkowski, nnSymmetricForm_minkowski,
      nnActionBoost_preserves_interval]

/-- **Unit normalization removes the last conformal scale.**  A boost-invariant symmetric form
whose unit real-action vector has interval one is pointwise equal to `nnLorentzForm`. -/
@[zil_level bridge_theorem]
theorem nnLorentzForm_unique_normalized {a b c : ℝ}
    (hinv : ∀ η q,
      nnSymmetricForm a b c (nnActionBoost η q) = nnSymmetricForm a b c q)
    (hnorm : nnSymmetricForm a b c 1 = 1) :
    ∀ q, nnSymmetricForm a b c q = nnLorentzForm q := by
  obtain ⟨hb, hc⟩ := nnSymmetricForm_invariant_unique hinv
  have ha : a = 1 := by
    simpa [nnSymmetricForm] using hnorm
  subst a
  rw [hb, hc]
  intro q
  simpa using nnSymmetricForm_minkowski 1 q

/-- The derivative data of the constant Nagao–Nielsen `(1,1)` action metric. -/
def nnFlatMetricDerivative : Fin 2 → Fin 2 → Fin 2 → ℝ := fun _ _ _ => 0

/-- **Uniqueness of the flat action-plane Levi–Civita connection.**  Any first-kind
connection that is torsion-free and compatible with the constant `(1,1)` metric derivative
is identically zero.  This specializes the proved Koszul uniqueness theorem and its flat
Christoffel corollary; it is not an additional connection postulate. -/
@[zil_level bridge_theorem]
theorem nnFlatLeviCivita_unique {Γ : Fin 2 → Fin 2 → Fin 2 → ℝ}
    (htf : ∀ k i j, Γ k i j = Γ k j i)
    (hcompat : ∀ i j k,
      nnFlatMetricDerivative i j k = Γ k i j + Γ j i k) :
    Γ = 0 := by
  funext k i j
  rw [leviCivita_unique htf hcompat k i j]
  exact christoffelFirstKind_flat (fun _ _ _ => rfl) k i j

/-- **Existence and uniqueness of the flat Nagao–Nielsen Levi–Civita connection.**  The zero
connection exists, is torsion-free and metric-compatible, and the preceding uniqueness theorem
shows that no other connection has both properties. -/
@[zil_level bridge_theorem]
theorem nnFlatLeviCivita_existsUnique :
    ∃! Γ : Fin 2 → Fin 2 → Fin 2 → ℝ,
      (∀ k i j, Γ k i j = Γ k j i) ∧
      (∀ i j k, nnFlatMetricDerivative i j k = Γ k i j + Γ j i k) := by
  refine ⟨0, ?_, ?_⟩
  · constructor
    · intro k i j
      rfl
    · intro i j k
      simp [nnFlatMetricDerivative]
  · intro Γ hΓ
    exact nnFlatLeviCivita_unique hΓ.1 hΓ.2

/-- **Uniqueness of the normalized invariant geometry.**  Boost symmetry and one timelike
calibration determine the metric interval exactly, while torsion freedom and compatibility
determine its connection exactly.  The two uniqueness statements share the same flat
Nagao–Nielsen action plane. -/
@[zil_level bridge_theorem]
theorem nnInvariantGeometry_unique {a b c : ℝ}
    (hinv : ∀ η q,
      nnSymmetricForm a b c (nnActionBoost η q) = nnSymmetricForm a b c q)
    (hnorm : nnSymmetricForm a b c 1 = 1) :
    (∀ q, nnSymmetricForm a b c q = nnLorentzForm q) ∧
    ∃! Γ : Fin 2 → Fin 2 → Fin 2 → ℝ,
      (∀ k i j, Γ k i j = Γ k j i) ∧
      (∀ i j k, nnFlatMetricDerivative i j k = Γ k i j + Γ j i k) :=
  ⟨nnLorentzForm_unique_normalized hinv hnorm, nnFlatLeviCivita_existsUnique⟩

/-- **Nagao–Nielsen invariant-geometry closure.**  The complex action carries the exact
Minkowski interval `Re(q²)`, its hyperbolic real/imaginary rotation preserves that interval and
the convergence cone, and the associated constant metric has one and only one torsion-free
compatible connection: the flat zero Levi–Civita connection. -/
@[zil_level bridge_theorem]
theorem nnComplexAction_interval_flatLeviCivita (η : ℝ) (q : ℂ) :
    nnLorentzForm q = (q ^ 2).re ∧
    nnLorentzForm (nnActionBoost η q) = nnLorentzForm q ∧
    (nnConverges (nnActionBoost η q) ↔ nnConverges q) ∧
    ∃! Γ : Fin 2 → Fin 2 → Fin 2 → ℝ,
      (∀ k i j, Γ k i j = Γ k j i) ∧
      (∀ i j k, nnFlatMetricDerivative i j k = Γ k i j + Γ j i k) :=
  ⟨nnLorentzForm_eq_re_sq q, nnActionBoost_preserves_interval η q,
    nnActionBoost_converges_iff η q, nnFlatLeviCivita_existsUnique⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction

zil attach loweredChristoffel_eq_firstKind where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffel_contraction",
  formalizes @ "claim:contracting-the-second-kind-levi-civita-connection-against-the-metric-reproduces-the-clifford-fiber-first-kind-christoffel-symbol-linking-the-raised-connection-to-the-fully-lowered-koszul-connection-that-transports-the-cl-tm-quaternion-pair-spinor-fiber"

zil attach lowered_torsionFree_metricCompatible_eq_firstKind where
  formalizes @ "claim:any-torsion-free-metric-compatible-connection-lowers-to-the-clifford-fiber-first-kind-christoffel-so-the-unique-metric-connection-is-the-one-whose-clifford-spinor-transport-carries-the-bell-no-signaling-contour",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.christoffel_unique_of_torsionFree_metricCompatible"

zil attach nnActionBoost_preserves_interval where
  formalizes @ "claim:the-hyperbolic-boost-mixing-the-real-and-imaginary-parts-of-the-nagao-nielsen-complex-action-is-an-exact-isometry-of-the-one-one-minkowski-interval-q-real-squared-minus-q-imaginary-squared",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.metricInterval_isometry_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoostMatrix_isometry",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra.lorentzBoost_preserves_form",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm"

zil attach nnLorentzForm_eq_metricInterval where
  formalizes @ "claim:the-nagao-nielsen-real-squared-minus-imaginary-squared-form-is-exactly-the-general-metric-interval-specialized-to-the-diagonal-one-minus-one-action-plane-metric",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.metricInterval"

zil attach nnActionVector_boost where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:the-hyperbolic-complex-action-boost-is-exactly-matrix-multiplication-by-its-so-one-one-matrix-on-the-real-imaginary-action-vector"

zil attach nnActionBoostMatrix_isometry where
  formalizes @ "claim:the-nagao-nielsen-action-boost-matrix-satisfies-l-transpose-g-l-equals-g-for-the-diagonal-one-minus-one-metric",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.metricInterval_isometry_invariant"

zil attach nnActionBoost_preserves_real_square where
  formalizes @ "claim:the-real-imaginary-action-boost-preserves-the-real-part-of-q-squared-because-this-is-exactly-the-nagao-nielsen-minkowski-interval",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm_eq_re_sq"

zil attach nnActionBoost_neg_comp where
  formalizes @ "claim:the-opposite-rapidity-nagao-nielsen-action-boost-is-an-exact-inverse-on-the-real-and-imaginary-action-components",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra.lorentzBoost_preserves_form"

zil attach nnActionBoost_injective where
  formalizes @ "claim:each-hyperbolic-real-imaginary-action-boost-is-injective-because-the-opposite-rapidity-is-its-explicit-left-inverse",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoost_neg_comp"

zil attach nnActionBoost_eq_zero_iff where
  formalizes @ "claim:a-boosted-complex-action-residual-vanishes-if-and-only-if-the-original-residual-vanishes",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoost_injective"

zil attach nnActionBoost_converges_iff where
  formalizes @ "claim:the-nagao-nielsen-timelike-convergence-cone-is-invariant-under-hyperbolic-real-imaginary-action-boosts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoost_preserves_interval"

zil attach nnSymmetricForm_invariant_unique where
  formalizes @ "claim:invariance-under-the-full-real-imaginary-action-boost-family-forces-every-real-symmetric-quadratic-form-to-have-zero-mixed-term-and-opposite-diagonal-coefficients-so-it-is-a-scalar-multiple-of-the-nagao-nielsen-lorentz-form",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnActionBoost_preserves_interval"

zil attach nnSymmetricForm_invariant_iff where
  formalizes @ "claim:a-real-symmetric-quadratic-form-on-the-action-plane-is-invariant-under-every-hyperbolic-action-boost-if-and-only-if-it-is-a-scalar-multiple-of-the-nagao-nielsen-lorentz-form",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnSymmetricForm_invariant_unique"

zil attach nnLorentzForm_unique_normalized where
  formalizes @ "claim:boost-invariance-together-with-unit-timelike-normalization-uniquely-determines-the-nagao-nielsen-lorentz-form-pointwise-removing-the-remaining-conformal-scale",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnSymmetricForm_invariant_unique"

zil attach nnFlatLeviCivita_unique where
  formalizes @ "claim:any-torsion-free-connection-compatible-with-the-constant-one-one-nagao-nielsen-action-metric-is-the-zero-flat-connection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita.leviCivita_unique",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita.christoffelFirstKind_flat"

zil attach nnFlatLeviCivita_existsUnique where
  formalizes @ "claim:the-constant-nagao-nielsen-one-one-action-metric-has-exactly-one-torsion-free-metric-compatible-first-kind-connection-the-zero-levi-civita-connection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnFlatLeviCivita_unique"

zil attach nnInvariantGeometry_unique where
  formalizes @ "claim:the-full-action-boost-symmetry-and-one-timelike-calibration-uniquely-determine-the-nagao-nielsen-metric-interval-while-torsion-freedom-and-metric-compatibility-uniquely-determine-its-flat-zero-levi-civita-connection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnLorentzForm_unique_normalized",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnFlatLeviCivita_existsUnique",
  caveat @ "claim:the-classification-is-for-real-symmetric-quadratic-forms-on-the-flat-two-dimensional-action-component-plane-and-does-not-classify-arbitrary-curved-or-nonlinear-action-geometries"

zil attach nnComplexAction_interval_flatLeviCivita where
  formalizes @ "claim:the-nagao-nielsen-complex-action-carries-the-invariant-minkowski-interval-real-of-q-squared-its-hyperbolic-real-imaginary-boost-preserves-the-interval-and-convergence-cone-and-its-constant-metric-has-the-unique-zero-levi-civita-connection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm_eq_re_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberChristoffelContraction.nnFlatLeviCivita_existsUnique",
  caveat @ "claim:this-is-the-flat-one-plus-one-real-imaginary-action-plane-and-does-not-identify-action-components-with-a-full-curved-spacetime-or-prove-an-interacting-curved-complex-action-connection"

zil_file_contract physlib.cliffordFiberChristoffelContraction where
  promises "Linking the second-kind Levi-Civita connection and its uniqueness to the recently updated Clifford fiber module and to the flat Nagao-Nielsen complex-action plane. Contracting the raised connection christoffelFromMetric against the metric reproduces the fully lowered first-kind Christoffel symbol christoffelFirstKind of the Clifford fiber module, in that module's index convention, via the Koszul contraction value and metric-derivative symmetry. By second-kind uniqueness any torsion-free metric-compatible connection is christoffelFromMetric, so it lowers to that same fiber Christoffel. On the real and imaginary parts of the complex action, nnLorentzForm is the one-one Minkowski interval and the existing hyperbolic boost is its metric isometry, preserving real of q squared and the Nagao-Nielsen convergence cone. Conversely, invariance under the full boost family classifies every real symmetric quadratic form on that plane as a scalar multiple of nnLorentzForm, and unit timelike normalization fixes the scale uniquely. The action metric is constant, so its metric derivative vanishes and the Koszul theorem proves that the zero connection exists and is the unique torsion-free compatible Levi-Civita connection."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.loweredSymbol",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.CliffordFiberLeviCivita.christoffelFirstKind",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra.lorentzBoost",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance.metricInterval_isometry_invariant"
  ]
  forbids_substitutes [
    "dropping the metric-derivative symmetry needed to match the two index conventions",
    "reading the contraction identity as identifying the raised and lowered connections without the metric",
    "promoting the flat one-plus-one action-plane isometry to a full curved-spacetime complex-action theorem",
    "claiming that Lorentz invariance alone physically identifies the real and imaginary action coordinates with spacetime coordinates",
    "extending the symmetric-quadratic-form uniqueness theorem to nonlinear or curved action metrics without additional hypotheses"
  ]
  witnessed_by [
    loweredChristoffel_eq_firstKind,
    lowered_torsionFree_metricCompatible_eq_firstKind,
    nnLorentzForm_eq_metricInterval,
    nnActionVector_boost,
    nnActionBoostMatrix_isometry,
    nnActionBoost_preserves_interval,
    nnActionBoost_preserves_real_square,
    nnActionBoost_neg_comp,
    nnActionBoost_injective,
    nnActionBoost_eq_zero_iff,
    nnActionBoost_converges_iff,
    nnSymmetricForm_invariant_unique,
    nnSymmetricForm_invariant_iff,
    nnLorentzForm_unique_normalized,
    nnFlatLeviCivita_unique,
    nnFlatLeviCivita_existsUnique,
    nnInvariantGeometry_unique,
    nnComplexAction_interval_flatLeviCivita
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.cliffordFiberChristoffelContraction
