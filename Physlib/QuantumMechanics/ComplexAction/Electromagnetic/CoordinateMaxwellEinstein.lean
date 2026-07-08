/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
public import Physlib.QFT.PathIntegral.CurvedMeasurePathIntegral
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

/-!
# Coordinate Maxwell fields and the complex Einstein bridge

This module provides the coordinate-calculus Maxwell kernel and connects it to
the existing momentum-space Maxwell-Faraday structure
`PTSymmetricQFT.MaxwellFaraday.faraday`.  The bridge keeps the derivative operator
and connection coefficients explicit:

* `coordinateFaradayTensor` is `F = dA` in coordinates.
* `homogeneousMaxwell_of_potential` proves the coordinate `d(dA) = 0` statement
  from mixed-partial symmetry.
* `curvedMaxwell_flatConnection_implies_wave_of_lorenzGauge` proves that the
  inhomogeneous Maxwell equation for a flat connection, Lorenz gauge, and
  commuting mixed partials gives the potential wave equation.
* `maxwellWave_and_complexEinstein_split` attaches that Maxwell wave equation
  to the repository's matrix-based complex Einstein field equation.
* `currentConnectedFunctional_eq_log_sourcePartition` attaches a coordinate
  current to the curved measure path-integral source functional.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
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
theorem coordinateFaradayTensor_antisymm
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) (x : CoordinateVector ι) (μ ν : ι) :
    coordinateFaradayTensor coordDeriv A x μ ν =
      -coordinateFaradayTensor coordDeriv A x ν μ := by
  unfold coordinateFaradayTensor
  ring

/-! ## Link to the existing momentum-space Maxwell-Faraday structure -/

/-- Coordinate derivative specialization `partial_mu f = k_mu * f`, the
momentum-space convention used by `PTSymmetricQFT.MaxwellFaraday`. -/
def momentumCoordinatePartial (k : Fin 4 → ℝ) : CoordinatePartial (Fin 4) :=
  fun f μ x => k μ * f x

/-- Constant coordinate one-form corresponding to a momentum-space potential. -/
def constantCoordinatePotential (A : Fin 4 → ℝ) : CoordinateOneForm (Fin 4) :=
  fun _ μ => A μ

/-- The coordinate Maxwell-Faraday tensor reduces exactly to the existing momentum-space structure when `partial_mu` is specialized to multiplication by
`k_mu` and the potential is coordinate-constant. -/
theorem coordinateFaradayTensor_momentum_eq_faraday
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
theorem homogeneousCyclic_faraday_eq_mixedPartialCommutatorSum
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
theorem homogeneousMaxwell_of_potential
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

/-- With the coordinate convention `partial_mu F^{mu nu}`, the
momentum-specialized coordinate divergence is the negative of the existing
Greaves-Thomas Maxwell operator `F^{nu mu} k_mu`. This theorem records the
index-order sign convention instead of redefining the momentum-space operator. -/
theorem partialDiv_momentumCoordinateFaraday_eq_neg_maxwellOp
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

/-- The same momentum-specialized coordinate divergence is the existing Heras/Maxwell four-current structure `J^nu = partial_mu F^{mu nu}`. -/
theorem partialDiv_momentumCoordinateFaraday_eq_fourCurrent
    (k A : Fin 4 → ℝ) (ν : Fin 4) (x : CoordinateVector (Fin 4)) :
    partialDivTwoContravariant (momentumCoordinatePartial k)
      (coordinateFaradayTensor (momentumCoordinatePartial k) (constantCoordinatePotential A)) ν x =
      fourCurrent k A ν := by
  simp [partialDivTwoContravariant, coordinateFaradayTensor, momentumCoordinatePartial,
    constantCoordinatePotential, fourCurrent, faraday, Matrix.of_apply]

/-- The coordinate divergence current obtained from the momentum-specialized
Faraday tensor is conserved because it is definitionally the existing
`Electromagnetic.MaxwellContinuityCovariant.fourCurrent`. -/
theorem partialDiv_momentumCoordinateFaraday_conserved
    (k A : Fin 4 → ℝ) (x : CoordinateVector (Fin 4)) :
    (∑ ν : Fin 4,
      k ν * partialDivTwoContravariant (momentumCoordinatePartial k)
        (coordinateFaradayTensor (momentumCoordinatePartial k) (constantCoordinatePotential A)) ν x) = 0 := by
  have h := fourCurrent_conserved k A
  rw [show (∑ ν : Fin 4,
      k ν * partialDivTwoContravariant (momentumCoordinatePartial k)
        (coordinateFaradayTensor (momentumCoordinatePartial k) (constantCoordinatePotential A)) ν x)
      = ∑ ν : Fin 4, k ν * fourCurrent k A ν by
        refine Finset.sum_congr rfl ?_
        intro ν _
        rw [partialDiv_momentumCoordinateFaraday_eq_fourCurrent]]
  exact h

/-- A connection vanishes in the chosen coordinates. -/
def ConnectionVanishes (Γ : CoordinateConnection ι) : Prop :=
  ∀ (x : CoordinateVector ι) (i j k : ι), Γ x i j k = 0

/-- If the connection coefficients vanish, the covariant derivative reduces to a partial derivative. -/
theorem covariantDerivTwoContravariant_eq_partial_of_connectionVanishes [Fintype ι]
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
theorem covariantDivTwoContravariant_eq_partial_of_connectionVanishes [Fintype ι]
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
theorem partialDiv_faraday_eq_wave_sub_gradDiv_sub_commutator [Fintype ι]
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
def DivergenceMixedPartialSymmetric (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι) : Prop :=
  ∀ (μ ν : ι) (x : CoordinateVector ι),
    coordDeriv (fun y => coordDeriv (fun z => A z μ) ν y) μ x =
      coordDeriv (fun y => coordDeriv (fun z => A z μ) μ y) ν x

/-- Strong mixed-partial symmetry implies the divergence-level condition. -/
theorem divergenceMixedPartialSymmetric_of_mixedPartialSymmetric
    (coordDeriv : CoordinatePartial ι) (A : CoordinateOneForm ι)
    (h : MixedPartialSymmetric coordDeriv A) :
    DivergenceMixedPartialSymmetric coordDeriv A := by
  intro μ ν x
  have hμ := h μ ν μ x
  unfold mixedPartialCommutator at hμ
  exact sub_eq_zero.mp hμ

/-- The divergence commutator vanishes under divergence-level mixed-partial symmetry. -/
theorem divergenceCommutator_eq_zero_of_symmetry [Fintype ι]
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
theorem partialDiv_faraday_eq_wave_sub_gradDiv_of_symmetry
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
theorem partialDiv_faraday_eq_wave_of_lorenzGauge
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
    (coordDeriv : CoordinatePartial ι) (F : CoordinateTwoTensor ι) (J : CoordinateCurrent ι) : Prop :=
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

/-- With vanishing connection coefficients, curved inhomogeneous Maxwell is flat Maxwell. -/
theorem maxwellInhomogeneousCurved_of_connectionVanishes_iff_flat
    [Fintype ι]
    (coordDeriv : CoordinatePartial ι) (Γ : CoordinateConnection ι)
    (F : CoordinateTwoTensor ι) (J : CoordinateCurrent ι) (hΓ : ConnectionVanishes Γ) :
    MaxwellInhomogeneousCurved coordDeriv Γ F J ↔ MaxwellInhomogeneousFlatTensor coordDeriv F J := by
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
theorem flatMaxwellPotential_implies_wave_of_lorenzGauge
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
theorem curvedMaxwell_flatConnection_implies_wave_of_lorenzGauge
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
      (coordDeriv := coordDeriv) (Γ := Γ) (F := coordinateFaradayTensor coordDeriv A) (J := J) hΓ).1 hCurved
  exact flatMaxwellPotential_implies_wave_of_lorenzGauge
    (coordDeriv := coordDeriv) (A := A) (J := J) hSub hFlat hGauge hSymm

/-- Coordinate Maxwell plus the repository's complex Einstein equation give both the wave equation and
the real/imaginary Einstein split. -/
theorem maxwellWave_and_complexEinstein_split
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

/-- A coordinate current sampled along a field configuration as a complex path-integral source. -/
def currentSource {α : Type*} (chart : α → CoordinateVector ι)
    (J : CoordinateCurrent ι) (ν : ι) : α → ℂ :=
  fun x => (J (chart x) ν : ℂ)

/-- The connected functional for a coordinate current is the log of the current-coupled partition. -/
theorem currentConnectedFunctional_eq_log_sourcePartition
    {α : Type*} [MeasurableSpace α] (c : CurvedMeasurePathIntegralModel α)
    (chart : α → CoordinateVector ι) (J : CoordinateCurrent ι) (ν : ι) :
    c.connectedGeneratingFunctional (currentSource chart J ν) =
      Complex.log (c.sourceCoupledPartition (currentSource chart J ν)) := by
  rfl

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein

end
