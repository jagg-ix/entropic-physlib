/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.DysonSchwinger
public import Physlib.QuantumMechanics.OpenSystems.LiouvilleSecondQuantization
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
public import Physlib.QuantumMechanics.DDimensions.Operators.Multiplication

/-!
# Continuum scalar fields, pointwise operators, and contact distributions

This module reuses the continuum infrastructure already present in Physlib for
Rivers' scalar Green-function chapter:

* `SpaceDHilbertSpace d = L²(Space d, ℂ)` for scalar wave profiles;
* maximal-domain pointwise multiplication operators `mulOperator`;
* `L²(X × X, μ × μ)` continuum kernels from
  `LiouvilleSecondQuantization.ContinuumKernelSpace`;
* left and right pointwise kernel actions;
* Dirac delta distributions for the contact terms in the continuum
  Dyson--Schwinger hierarchy.

The contact term is distribution-valued. For external points
`[x₁, ..., xₙ]`, it is

`Σ_j G(x₁,...,x̂_j,...,xₙ) δ_(x_j)`.

This avoids treating `δ(x-x_j)` or coincident continuum fields as ordinary
pointwise functions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open MeasureTheory
open _root_.QuantumMechanics
open _root_.QuantumMechanics.LiouvilleSecondQuantization

/-- A continuum complex scalar field representative on `Space d`. -/
abbrev ContinuumScalarField (d : ℕ) := Space d → ℂ

/-- The repository's existing scalar `L²` Hilbert carrier. -/
abbrev ContinuumScalarHilbertSpace (d : ℕ) :=
  SpaceDHilbertSpace d

/-- A continuum two-point kernel in the existing product-measure `L²` space. -/
abbrev ContinuumScalarKernelSpace (d : ℕ) :=
  ContinuumKernelSpace (Space d) (volume : Measure (Space d))

/-- Existing `MemLp` membership predicate for a scalar two-point kernel. -/
def MemContinuumScalarKernel {d : ℕ}
    (K : Space d × Space d → ℂ) : Prop :=
  MemContinuumKernel (volume : Measure (Space d)) K

/-- Construct a continuum scalar kernel using the existing `Lp` constructor. -/
def mkContinuumScalarKernel {d : ℕ} {K : Space d × Space d → ℂ}
    (hK : MemContinuumScalarKernel K) : ContinuumScalarKernelSpace d :=
  mkContinuumKernel hK

/-- The constructed scalar kernel agrees almost everywhere with its
representative. -/
lemma coe_mkContinuumScalarKernel_ae {d : ℕ}
    {K : Space d × Space d → ℂ} (hK : MemContinuumScalarKernel K) :
    (mkContinuumScalarKernel hK : Space d × Space d → ℂ) =ᵐ[
      (volume : Measure (Space d)).prod volume] K :=
  coe_mkContinuumKernel_ae hK

/-- Pointwise multiplication by a continuum source or background field, with
the maximal domain already supplied by Physlib. -/
def continuumScalarMulOperator {d : ℕ} (f : ContinuumScalarField d) :
    ContinuumScalarHilbertSpace d →ₗ.[ℂ] ContinuumScalarHilbertSpace d :=
  SpaceDHilbertSpace.mulOperator MeasureTheory.volume f

/-- Almost-everywhere strongly measurable pointwise multipliers have dense
domain. -/
lemma continuumScalarMulOperator_hasDenseDomain {d : ℕ}
    {f : ContinuumScalarField d} (hf : AEStronglyMeasurable f) :
    (continuumScalarMulOperator f).HasDenseDomain := by
  simpa [continuumScalarMulOperator] using
    (SpaceDHilbertSpace.mulOperator_hasDenseDomain hf)

/-- The continuum multiplication operator acts pointwise almost everywhere. -/
lemma continuumScalarMulOperator_apply_ae {d : ℕ}
    {f : ContinuumScalarField d}
    (ψ : (continuumScalarMulOperator f).domain) :
    continuumScalarMulOperator f ψ =ᵐ[volume] f • ψ := by
  simpa [continuumScalarMulOperator] using
    (SpaceDHilbertSpace.mulOperator_apply_ae (f := f) ψ)

/-- Left pointwise multiplication of a two-point kernel by a source field. -/
def leftContinuumScalarKernelAction {d : ℕ}
    (f : ContinuumScalarField d) (K : Space d × Space d → ℂ) :
    Space d × Space d → ℂ :=
  leftPointwiseKernelAction f K

/-- Right pointwise multiplication of a two-point kernel by a source field. -/
def rightContinuumScalarKernelAction {d : ℕ}
    (f : ContinuumScalarField d) (K : Space d × Space d → ℂ) :
    Space d × Space d → ℂ :=
  rightPointwiseKernelAction f K

/-- Left and right continuum source multipliers commute. -/
lemma left_right_continuumScalarKernelAction_commute {d : ℕ}
    (f g : ContinuumScalarField d) (K : Space d × Space d → ℂ) :
    leftContinuumScalarKernelAction f
        (rightContinuumScalarKernelAction g K) =
      rightContinuumScalarKernelAction g
        (leftContinuumScalarKernelAction f K) :=
  leftPointwise_rightPointwise_commute f g K

/-- Scalar distributions on continuum configuration space. -/
abbrev ScalarContactDistribution (d : ℕ) :=
  Physlib.Distribution ℂ (Space d) ℂ

/-- The continuum contact distribution centered at `x`. -/
def scalarContactDistribution {d : ℕ} (x : Space d) :
    ScalarContactDistribution d :=
  Physlib.Distribution.diracDelta ℂ x

/-- A contact distribution evaluates a Schwartz test function at its center. -/
@[simp] lemma scalarContactDistribution_apply {d : ℕ}
    (x : Space d) (η : SchwartzMap (Space d) ℂ) :
    scalarContactDistribution x η = η x :=
  rfl

/-- Distributional contact term in the continuum scalar Dyson--Schwinger
hierarchy. Each recursive step removes exactly one external insertion. -/
def continuumContactTerm {d : ℕ}
    (G : List (Space d) → ℂ) : List (Space d) → ScalarContactDistribution d
  | [] => 0
  | y :: ys =>
      G ys • scalarContactDistribution y +
        continuumContactTerm (fun zs => G (y :: zs)) ys

@[simp] lemma continuumContactTerm_nil {d : ℕ}
    (G : List (Space d) → ℂ) :
    continuumContactTerm G [] = 0 :=
  rfl

/-- The one-external-point contact term is `G₀ δ_y`. -/
@[simp] lemma continuumContactTerm_singleton_apply {d : ℕ}
    (G : List (Space d) → ℂ) (y : Space d)
    (η : SchwartzMap (Space d) ℂ) :
    continuumContactTerm G [y] η = G [] * η y := by
  simp [continuumContactTerm, scalarContactDistribution]

/-- The two-external-point contact term is
`G₁(z) δ_y + G₁(y) δ_z`. -/
@[simp] lemma continuumContactTerm_pair_apply {d : ℕ}
    (G : List (Space d) → ℂ) (y z : Space d)
    (η : SchwartzMap (Space d) ℂ) :
    continuumContactTerm G [y, z] η =
      G [z] * η y + G [y] * η z := by
  simp [continuumContactTerm, scalarContactDistribution]

/-- Convolution of two continuum kernels with a pointwise background insertion
on their contracted variable. This is the analytic expression occurring in
Rivers' external-field equations, including
`∂_g Δ_g = Δ_g B Δ_g`. -/
def pointwiseKernelComposition {d : ℕ}
    (A C : Space d × Space d → ℂ) (B : ContinuumScalarField d)
    (x y : Space d) : ℂ :=
  ∫ z, A (x, z) * B z * C (z, y)

/-- The zero pointwise background gives a zero composed kernel. -/
@[simp] lemma pointwiseKernelComposition_zero {d : ℕ}
    (A C : Space d × Space d → ℂ) (x y : Space d) :
    pointwiseKernelComposition A C (fun _ => 0) x y = 0 := by
  simp [pointwiseKernelComposition]

end Physlib.QFT.ScalarGreenFunctions

end
