/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.MeasureExpectation
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Tactic.Linarith

/-!
# Finite Wilson gauge models as path-integral models

This file ports the proved finite Wilson-action material from the helper
tree into the shared `Physlib.QFT.PathIntegral` layer, using standard
terminology only.

A finite Wilson model has finitely many plaquette contributions, an
inverse coupling, a Euclidean Wilson action, and a Boltzmann damping
factor.  It is converted into `MeasurePathIntegralModel` over a finite
counting space, so the general source-coupled partition and expectation
API from `MeasureExpectation` applies directly.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators
open Filter MeasureTheory

namespace Physlib.QFT.PathIntegral

/-- Finite Wilson-action gauge data over a finite plaquette set. -/
structure FiniteWilsonGaugeModel where
  /-- Number of plaquette contributions. -/
  nPlaquettes : ℕ
  /-- The plaquette set is nonempty. -/
  nPlaquettes_pos : 0 < nPlaquettes
  /-- Inverse coupling, usually denoted `β`. -/
  inverseCoupling : ℝ
  /-- Nonnegative Euclidean inverse coupling. -/
  inverseCoupling_nonneg : 0 ≤ inverseCoupling
  /-- Plaquette action contribution. -/
  plaquetteAction : Fin nPlaquettes → ℝ

namespace FiniteWilsonGaugeModel

variable (L : FiniteWilsonGaugeModel)

/-- Finite Wilson action as the sum of plaquette contributions. -/
def wilsonAction : ℝ :=
  ∑ i : Fin L.nPlaquettes, L.plaquetteAction i

/-- Euclidean Wilson Boltzmann factor `exp(-β S_W)`. -/
def boltzmannFactor : ℝ :=
  Real.exp (-L.inverseCoupling * L.wilsonAction)

/-- The finite Wilson Boltzmann factor is strictly positive. -/
lemma boltzmannFactor_pos : 0 < L.boltzmannFactor := by
  unfold boltzmannFactor
  exact Real.exp_pos _

/-- If the Wilson action is nonnegative, the Boltzmann damping is at most one. -/
lemma boltzmannFactor_le_one (h_nonneg : 0 ≤ L.wilsonAction) :
    L.boltzmannFactor ≤ 1 := by
  unfold boltzmannFactor
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  nlinarith [L.inverseCoupling_nonneg, h_nonneg]

/-- Per-plaquette imaginary action contribution `β S_p`. -/
def imaginaryAction (i : Fin L.nPlaquettes) : ℝ :=
  L.inverseCoupling * L.plaquetteAction i

/-- Nonnegative plaquette actions give a nonnegative imaginary action. -/
lemma imaginaryAction_nonneg
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i) :
    ∀ i : Fin L.nPlaquettes, 0 ≤ L.imaginaryAction i := by
  intro i
  unfold imaginaryAction
  exact mul_nonneg L.inverseCoupling_nonneg (hPlaquette_nonneg i)

/-- A finite Wilson model as a measurable complex path-integral model over a counting space. -/
def toMeasurePathIntegralModel (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i) :
    MeasurePathIntegralModel (Fin L.nPlaquettes) where
  μ := Measure.count
  hbar := hbar
  hbar_pos := hbar_pos
  actionRe := fun _ => 0
  actionIm := L.imaginaryAction
  measurable_actionRe := measurable_const
  measurable_actionIm := measurable_of_finite _
  actionIm_nonneg := L.imaginaryAction_nonneg hPlaquette_nonneg

/-- The finite Wilson partition is exactly the finite counting sum of weights. -/
lemma partition_eq_finset_sum (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i) :
    (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).partition =
      ∑ i : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).weight i := by
  simp [MeasurePathIntegralModel.partition, toMeasurePathIntegralModel]

/-- Source-coupled finite Wilson partitions are finite counting sums. -/
lemma sourceCoupledPartition_eq_finset_sum (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (J : Fin L.nPlaquettes → ℂ) :
    (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledPartition J =
      ∑ i : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledWeight J i := by
  simp [MeasurePathIntegralModel.sourceCoupledPartition, toMeasurePathIntegralModel]

/-- Source-coupled unnormalised expectations are finite counting sums. -/
lemma sourceCoupledUnnormalizedExpectation_eq_finset_sum
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (J O : Fin L.nPlaquettes → ℂ) :
    MeasurePathIntegralModel.sourceCoupledUnnormalizedExpectation
      (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) J O =
      ∑ i : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledWeight J i * O i := by
  simp [MeasurePathIntegralModel.sourceCoupledUnnormalizedExpectation,
    MeasurePathIntegralModel.sourceCoupledWeight, toMeasurePathIntegralModel]

/-- Source-coupled normalised expectations are ratios of finite Wilson sums. -/
lemma sourceCoupledExpectation_eq_finset_ratio
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (J O : Fin L.nPlaquettes → ℂ) :
    MeasurePathIntegralModel.sourceCoupledExpectation
      (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) J O =
      (∑ i : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledWeight J i * O i) /
      (∑ i : Fin L.nPlaquettes,
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledWeight J i) := by
  unfold MeasurePathIntegralModel.sourceCoupledExpectation
  rw [L.sourceCoupledUnnormalizedExpectation_eq_finset_sum hbar hbar_pos hPlaquette_nonneg J O]
  rw [L.sourceCoupledPartition_eq_finset_sum hbar hbar_pos hPlaquette_nonneg J]

/-- The first source derivative of a finite Wilson partition inserts the
observable coupled to the source:
`d Z[tO] / dt |₀ = ⟪O⟫`. -/
lemma sourceCoupledPartition_linearSource_hasDerivAt_zero
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (O : Fin L.nPlaquettes → ℂ) :
    HasDerivAt
      (fun t : ℂ =>
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).sourceCoupledPartition
          (fun i => t * O i))
      ((L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).unnormalizedExpectation O) 0 := by
  let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  have hterm : ∀ i : Fin L.nPlaquettes,
      HasDerivAt (fun t : ℂ => M.sourceCoupledWeight (fun j => t * O j) i)
        (M.weight i * O i) 0 := by
    intro i
    unfold MeasurePathIntegralModel.sourceCoupledWeight
    have hlin : HasDerivAt (fun t : ℂ => t * O i) (O i) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const (O i)
    have hexp : HasDerivAt (fun t : ℂ => Complex.exp (t * O i)) (O i) 0 := by
      simpa using hlin.cexp
    simpa [mul_assoc] using hexp.const_mul (M.weight i)
  have hsum : HasDerivAt
      (fun t : ℂ => ∑ i : Fin L.nPlaquettes, M.sourceCoupledWeight (fun j => t * O j) i)
      (∑ i : Fin L.nPlaquettes, M.weight i * O i) 0 := by
    exact HasDerivAt.fun_sum fun i _hi => hterm i
  change HasDerivAt
    (fun t : ℂ => ∫ i, M.sourceCoupledWeight (fun j => t * O j) i ∂M.μ)
    (∫ i, M.weight i * O i ∂M.μ) 0
  simpa [M, MeasurePathIntegralModel.sourceCoupledPartition,
    MeasurePathIntegralModel.unnormalizedExpectation, FiniteWilsonGaugeModel.toMeasurePathIntegralModel]
    using hsum

/-- The first source derivative of a finite source-coupled unnormalised
expectation inserts one more observable:
`d ⟪A⟫_{tO} / dt |₀ = ⟪O A⟫`. -/
lemma sourceCoupledUnnormalizedExpectation_linearSource_hasDerivAt_zero
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (O A : Fin L.nPlaquettes → ℂ) :
    HasDerivAt
      (fun t : ℂ =>
        MeasurePathIntegralModel.sourceCoupledUnnormalizedExpectation
          (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) (fun i => t * O i) A)
      (MeasurePathIntegralModel.unnormalizedExpectation
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) (fun i => O i * A i)) 0 := by
  let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  have hterm : ∀ i : Fin L.nPlaquettes,
      HasDerivAt
        (fun t : ℂ => M.sourceCoupledWeight (fun j => t * O j) i * A i)
        (M.weight i * (O i * A i)) 0 := by
    intro i
    have hweight : HasDerivAt (fun t : ℂ => M.sourceCoupledWeight (fun j => t * O j) i)
        (M.weight i * O i) 0 := by
      unfold MeasurePathIntegralModel.sourceCoupledWeight
      have hlin : HasDerivAt (fun t : ℂ => t * O i) (O i) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).mul_const (O i)
      have hexp : HasDerivAt (fun t : ℂ => Complex.exp (t * O i)) (O i) 0 := by
        simpa using hlin.cexp
      simpa [mul_assoc] using hexp.const_mul (M.weight i)
    simpa [mul_assoc] using hweight.mul_const (A i)
  have hsum : HasDerivAt
      (fun t : ℂ => ∑ i : Fin L.nPlaquettes,
        M.sourceCoupledWeight (fun j => t * O j) i * A i)
      (∑ i : Fin L.nPlaquettes, M.weight i * (O i * A i)) 0 := by
    exact HasDerivAt.fun_sum fun i _hi => hterm i
  change HasDerivAt
    (fun t : ℂ => ∫ i, M.sourceCoupledWeight (fun j => t * O j) i * A i ∂M.μ)
    (∫ i, M.weight i * (O i * A i) ∂M.μ) 0
  simpa [M, MeasurePathIntegralModel.sourceCoupledUnnormalizedExpectation,
    MeasurePathIntegralModel.unnormalizedExpectation, FiniteWilsonGaugeModel.toMeasurePathIntegralModel]
    using hsum

/-- The finite Wilson partition is a finite sum of positive real damping factors. -/
lemma partition_eq_real_wilson_damping_sum
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i) :
    (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).partition =
      ((∑ i : Fin L.nPlaquettes, Real.exp (-(L.imaginaryAction i / hbar))) : ℂ) := by
  rw [L.partition_eq_finset_sum hbar hbar_pos hPlaquette_nonneg]
  simp [MeasurePathIntegralModel.weight, MeasurePathIntegralModel.actionReScaled,
    MeasurePathIntegralModel.actionImScaled, toMeasurePathIntegralModel, imaginaryAction,
    Complex.ofReal_exp]

/-- The zero-source finite Wilson partition lies in the complex slit plane. -/
lemma partition_mem_slitPlane
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i) :
    (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).partition ∈
      Complex.slitPlane := by
  rw [L.partition_eq_real_wilson_damping_sum hbar hbar_pos hPlaquette_nonneg]
  rw [← Complex.ofReal_sum]
  exact Complex.ofReal_mem_slitPlane.2
    (Finset.sum_pos
      (s := Finset.univ)
      (f := fun i : Fin L.nPlaquettes => Real.exp (-(L.imaginaryAction i / hbar)))
      (fun _ _ => Real.exp_pos _)
      ⟨⟨0, L.nPlaquettes_pos⟩, by simp⟩)

/-- The first source derivative of the finite connected generating functional is
the normalised insertion:
`d log Z[tO] / dt |₀ = ⟨O⟩`. -/
lemma connectedGeneratingFunctional_linearSource_hasDerivAt_zero
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (O : Fin L.nPlaquettes → ℂ) :
    HasDerivAt
      (fun t : ℂ =>
        (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).connectedGeneratingFunctional
          (fun i => t * O i))
      ((L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).normalizedExpectation O) 0 := by
  let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  have hsource :
      HasDerivAt
        (fun t : ℂ => M.sourceCoupledPartition (fun i => t * O i))
        (M.unnormalizedExpectation O) 0 := by
    simpa [M] using
      L.sourceCoupledPartition_linearSource_hasDerivAt_zero hbar hbar_pos hPlaquette_nonneg O
  have hslit : M.sourceCoupledPartition (fun i => (0 : ℂ) * O i) ∈ Complex.slitPlane := by
    simpa [M.sourceCoupledPartition_zero, M] using
      L.partition_mem_slitPlane hbar hbar_pos hPlaquette_nonneg
  have hlog :
      HasDerivAt
        (fun t : ℂ => Complex.log (M.sourceCoupledPartition (fun i => t * O i)))
        (M.unnormalizedExpectation O / M.sourceCoupledPartition (fun i => (0 : ℂ) * O i)) 0 :=
    hsource.clog hslit
  simpa [M, MeasurePathIntegralModel.connectedGeneratingFunctional,
    MeasurePathIntegralModel.normalizedExpectation, M.sourceCoupledPartition_zero]
    using hlog

/-- The first source derivative of a finite normalised expectation has the
standard quotient-rule form. After rewriting the zero-source terms, this is the
finite connected two-point insertion
`d ⟨A⟩_{tO} / dt |₀ = ⟨OA⟩ - ⟨O⟩⟨A⟩`. -/
lemma sourceCoupledExpectation_linearSource_hasDerivAt_zero_quotient
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (O A : Fin L.nPlaquettes → ℂ) :
    HasDerivAt
      (fun t : ℂ =>
        MeasurePathIntegralModel.sourceCoupledExpectation
          (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) (fun i => t * O i) A)
      (let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
       ((M.unnormalizedExpectation (fun i => O i * A i) *
              M.sourceCoupledPartition (fun i => (0 : ℂ) * O i)
            - M.sourceCoupledUnnormalizedExpectation (fun i => (0 : ℂ) * O i) A *
              M.unnormalizedExpectation O) /
            (M.sourceCoupledPartition (fun i => (0 : ℂ) * O i)) ^ 2)) 0 := by
  let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  have hnum :
      HasDerivAt
        (fun t : ℂ => M.sourceCoupledUnnormalizedExpectation (fun i => t * O i) A)
        (M.unnormalizedExpectation (fun i => O i * A i)) 0 := by
    simpa [M] using
      L.sourceCoupledUnnormalizedExpectation_linearSource_hasDerivAt_zero
        hbar hbar_pos hPlaquette_nonneg O A
  have hden :
      HasDerivAt
        (fun t : ℂ => M.sourceCoupledPartition (fun i => t * O i))
        (M.unnormalizedExpectation O) 0 := by
    simpa [M] using
      L.sourceCoupledPartition_linearSource_hasDerivAt_zero hbar hbar_pos hPlaquette_nonneg O
  have hden_nonzero : M.sourceCoupledPartition (fun i => (0 : ℂ) * O i) ≠ 0 := by
    exact Complex.slitPlane_ne_zero <| by
      simpa [M.sourceCoupledPartition_zero, M] using
        L.partition_mem_slitPlane hbar hbar_pos hPlaquette_nonneg
  have hquot :
      HasDerivAt
        (fun t : ℂ =>
          M.sourceCoupledUnnormalizedExpectation (fun i => t * O i) A /
            M.sourceCoupledPartition (fun i => t * O i))
        ((M.unnormalizedExpectation (fun i => O i * A i) *
              M.sourceCoupledPartition (fun i => (0 : ℂ) * O i)
            - M.sourceCoupledUnnormalizedExpectation (fun i => (0 : ℂ) * O i) A *
              M.unnormalizedExpectation O) /
            (M.sourceCoupledPartition (fun i => (0 : ℂ) * O i)) ^ 2) 0 :=
    hnum.div hden hden_nonzero
  simpa [M, MeasurePathIntegralModel.sourceCoupledExpectation]
    using hquot

/-- The quotient-rule derivative for a finite normalised source expectation is
the connected two-point insertion:
`⟪OA⟫/Z - (⟪O⟫/Z)(⟪A⟫/Z)`. -/
lemma sourceCoupledExpectation_linearSource_derivative_eq_connected
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (O A : Fin L.nPlaquettes → ℂ) :
    (let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg;
       ((M.unnormalizedExpectation (fun i => O i * A i) *
              M.sourceCoupledPartition (fun i => (0 : ℂ) * O i)
            - M.sourceCoupledUnnormalizedExpectation (fun i => (0 : ℂ) * O i) A *
              M.unnormalizedExpectation O) /
            (M.sourceCoupledPartition (fun i => (0 : ℂ) * O i)) ^ 2)) =
      MeasurePathIntegralModel.normalizedExpectation
          (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) (fun i => O i * A i)
        - MeasurePathIntegralModel.normalizedExpectation
            (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) O *
          MeasurePathIntegralModel.normalizedExpectation
            (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) A := by
  let M := L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg
  have hZ : M.partition ≠ 0 := by
    exact Complex.slitPlane_ne_zero <| by
      simpa [M] using L.partition_mem_slitPlane hbar hbar_pos hPlaquette_nonneg
  simp [MeasurePathIntegralModel.normalizedExpectation,
    MeasurePathIntegralModel.sourceCoupledPartition_zero,
    MeasurePathIntegralModel.sourceCoupledUnnormalizedExpectation,
    MeasurePathIntegralModel.unnormalizedExpectation,
    MeasurePathIntegralModel.sourceCoupledWeight]
  field_simp [hZ]

/-- The first source derivative of a finite normalised expectation is the
connected two-point insertion:
`d ⟨A⟩_{tO} / dt |₀ = ⟨OA⟩ - ⟨O⟩⟨A⟩`. -/
lemma sourceCoupledExpectation_linearSource_hasDerivAt_zero
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (O A : Fin L.nPlaquettes → ℂ) :
    HasDerivAt
      (fun t : ℂ =>
        MeasurePathIntegralModel.sourceCoupledExpectation
          (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) (fun i => t * O i) A)
      (MeasurePathIntegralModel.normalizedExpectation
          (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) (fun i => O i * A i)
        - MeasurePathIntegralModel.normalizedExpectation
            (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) O *
          MeasurePathIntegralModel.normalizedExpectation
            (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg) A) 0 := by
  have hq :=
    L.sourceCoupledExpectation_linearSource_hasDerivAt_zero_quotient
      hbar hbar_pos hPlaquette_nonneg O A
  rw [L.sourceCoupledExpectation_linearSource_derivative_eq_connected
      hbar hbar_pos hPlaquette_nonneg O A] at hq
  simpa using hq

/-- Explicit Euclidean form: the finite Wilson model has zero real action. -/
lemma weight_eq_wilson_damping (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ i : Fin L.nPlaquettes, 0 ≤ L.plaquetteAction i)
    (i : Fin L.nPlaquettes) :
    (L.toMeasurePathIntegralModel hbar hbar_pos hPlaquette_nonneg).weight i =
      Complex.exp ((-(L.imaginaryAction i / hbar) : ℂ)) := by
  simp [MeasurePathIntegralModel.weight, MeasurePathIntegralModel.actionReScaled,
    MeasurePathIntegralModel.actionImScaled, toMeasurePathIntegralModel, imaginaryAction]

end FiniteWilsonGaugeModel

/-! ## Continuum-limit contracts for finite Wilson sequences -/

/-- Continuum admissibility data for a finite Wilson sequence. -/
structure FiniteWilsonContinuumAdmissible where
  /-- Lattice spacing along the approximating sequence. -/
  latticeSpacing : ℕ → ℝ
  /-- Inverse coupling along the approximating sequence. -/
  inverseCoupling : ℕ → ℝ
  /-- The lattice spacing tends to zero. -/
  spacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0)
  /-- The inverse coupling tends to the ultraviolet limit. -/
  inverseCoupling_tendsto_atTop : Tendsto inverseCoupling atTop atTop

/-- Source-coupled partition sequence from finite Wilson data. -/
def finiteWilsonSourceCoupledPartitionSeq
    (Ls : ℕ → FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i)
    (J : ∀ n, Fin (Ls n).nPlaquettes → ℂ) :
    ℕ → ℂ :=
  fun n => MeasurePathIntegralModel.sourceCoupledPartition
    ((Ls n).toMeasurePathIntegralModel hbar hbar_pos (hPlaquette_nonneg n)) (J n)

/-- Source-coupled unnormalised expectation sequence from finite Wilson data. -/
def finiteWilsonSourceCoupledUnnormalizedExpectationSeq
    (Ls : ℕ → FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i)
    (J O : ∀ n, Fin (Ls n).nPlaquettes → ℂ) :
    ℕ → ℂ :=
  fun n => MeasurePathIntegralModel.sourceCoupledUnnormalizedExpectation
    ((Ls n).toMeasurePathIntegralModel hbar hbar_pos (hPlaquette_nonneg n)) (J n) (O n)

/-- Source-coupled normalised expectation sequence from finite Wilson data. -/
def finiteWilsonSourceCoupledExpectationSeq
    (Ls : ℕ → FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i)
    (J O : ∀ n, Fin (Ls n).nPlaquettes → ℂ) :
    ℕ → ℂ :=
  fun n => MeasurePathIntegralModel.sourceCoupledExpectation
    ((Ls n).toMeasurePathIntegralModel hbar hbar_pos (hPlaquette_nonneg n)) (J n) (O n)

/-- Connected generating functional sequence `W_n[J] = log Z_n[J]`. -/
def finiteWilsonConnectedGeneratingFunctionalSeq
    (Ls : ℕ → FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i)
    (J : ∀ n, Fin (Ls n).nPlaquettes → ℂ) :
    ℕ → ℂ :=
  fun n =>
    Complex.log
      (MeasurePathIntegralModel.sourceCoupledPartition
        ((Ls n).toMeasurePathIntegralModel hbar hbar_pos (hPlaquette_nonneg n)) (J n))

/-- Quotient transfer for source-coupled finite Wilson expectations. -/
lemma finiteWilsonSourceCoupledExpectationSeq_tendsto_of_tendsto
    (Ls : ℕ → FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i)
    (J O : ∀ n, Fin (Ls n).nPlaquettes → ℂ)
    (unnormLimit partitionLimit : ℂ)
    (hUnnorm :
      Tendsto
        (finiteWilsonSourceCoupledUnnormalizedExpectationSeq
          Ls hbar hbar_pos hPlaquette_nonneg J O)
        atTop (nhds unnormLimit))
    (hPartition :
      Tendsto
        (finiteWilsonSourceCoupledPartitionSeq Ls hbar hbar_pos hPlaquette_nonneg J)
        atTop (nhds partitionLimit))
    (hPartition_ne : partitionLimit ≠ 0) :
    Tendsto
      (finiteWilsonSourceCoupledExpectationSeq Ls hbar hbar_pos hPlaquette_nonneg J O)
      atTop (nhds (unnormLimit / partitionLimit)) := by
  have hdiv := hUnnorm.div hPartition hPartition_ne
  change Tendsto
    (finiteWilsonSourceCoupledUnnormalizedExpectationSeq Ls hbar hbar_pos hPlaquette_nonneg J O /
      finiteWilsonSourceCoupledPartitionSeq Ls hbar hbar_pos hPlaquette_nonneg J)
    atTop (nhds (unnormLimit / partitionLimit))
  simpa using hdiv

/-- Log-continuity transfer for finite Wilson connected generating functionals. -/
lemma finiteWilsonConnectedGeneratingFunctionalSeq_tendsto_of_partition_tendsto
    (Ls : ℕ → FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i)
    (J : ∀ n, Fin (Ls n).nPlaquettes → ℂ)
    (partitionLimit : ℂ)
    (hPartition :
      Tendsto
        (finiteWilsonSourceCoupledPartitionSeq Ls hbar hbar_pos hPlaquette_nonneg J)
        atTop (nhds partitionLimit))
    (hPartition_slit : partitionLimit ∈ Complex.slitPlane) :
    Tendsto
      (finiteWilsonConnectedGeneratingFunctionalSeq Ls hbar hbar_pos hPlaquette_nonneg J)
      atTop (nhds (Complex.log partitionLimit)) := by
  exact hPartition.clog hPartition_slit

/-- Unified continuum contract for source-coupled finite Wilson observables. -/
structure FiniteWilsonContinuumContract
    (Ls : ℕ → FiniteWilsonGaugeModel)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i)
    (J O : ∀ n, Fin (Ls n).nPlaquettes → ℂ) where
  /-- Continuum partition limit. -/
  partitionLimit : ℂ
  /-- Continuum unnormalised expectation limit. -/
  unnormLimit : ℂ
  /-- Partition convergence. -/
  partition_tendsto :
    Tendsto (finiteWilsonSourceCoupledPartitionSeq Ls hbar hbar_pos hPlaquette_nonneg J)
      atTop (nhds partitionLimit)
  /-- Unnormalised expectation convergence. -/
  unnorm_tendsto :
    Tendsto (finiteWilsonSourceCoupledUnnormalizedExpectationSeq
      Ls hbar hbar_pos hPlaquette_nonneg J O) atTop (nhds unnormLimit)
  /-- Nonzero limiting partition. -/
  partition_ne_zero : partitionLimit ≠ 0
  /-- Slit-plane condition for the principal logarithm. -/
  partition_mem_slitPlane : partitionLimit ∈ Complex.slitPlane

namespace FiniteWilsonContinuumContract

variable {Ls : ℕ → FiniteWilsonGaugeModel}
variable {hbar : ℝ} {hbar_pos : 0 < hbar}
variable {hPlaquette_nonneg : ∀ n, ∀ i : Fin (Ls n).nPlaquettes, 0 ≤ (Ls n).plaquetteAction i}
variable {J O : ∀ n, Fin (Ls n).nPlaquettes → ℂ}

/-- Contract consequence: normalised source-coupled expectations converge. -/
lemma expectation_tendsto
    (C : FiniteWilsonContinuumContract Ls hbar hbar_pos hPlaquette_nonneg J O) :
    Tendsto (finiteWilsonSourceCoupledExpectationSeq Ls hbar hbar_pos hPlaquette_nonneg J O)
      atTop (nhds (C.unnormLimit / C.partitionLimit)) :=
  finiteWilsonSourceCoupledExpectationSeq_tendsto_of_tendsto
    Ls hbar hbar_pos hPlaquette_nonneg J O C.unnormLimit C.partitionLimit
    C.unnorm_tendsto C.partition_tendsto C.partition_ne_zero

/-- Contract consequence: connected generating functionals converge. -/
lemma connectedGeneratingFunctional_tendsto
    (C : FiniteWilsonContinuumContract Ls hbar hbar_pos hPlaquette_nonneg J O) :
    Tendsto (finiteWilsonConnectedGeneratingFunctionalSeq Ls hbar hbar_pos hPlaquette_nonneg J)
      atTop (nhds (Complex.log C.partitionLimit)) :=
  finiteWilsonConnectedGeneratingFunctionalSeq_tendsto_of_partition_tendsto
    Ls hbar hbar_pos hPlaquette_nonneg J C.partitionLimit
    C.partition_tendsto C.partition_mem_slitPlane

/-- Contract consequence: expectation and connected functional converge together. -/
lemma expectation_and_connectedGeneratingFunctional_tendsto
    (C : FiniteWilsonContinuumContract Ls hbar hbar_pos hPlaquette_nonneg J O) :
    Tendsto (finiteWilsonSourceCoupledExpectationSeq Ls hbar hbar_pos hPlaquette_nonneg J O)
      atTop (nhds (C.unnormLimit / C.partitionLimit)) ∧
    Tendsto (finiteWilsonConnectedGeneratingFunctionalSeq Ls hbar hbar_pos hPlaquette_nonneg J)
      atTop (nhds (Complex.log C.partitionLimit)) :=
  ⟨C.expectation_tendsto, C.connectedGeneratingFunctional_tendsto⟩

end FiniteWilsonContinuumContract

end Physlib.QFT.PathIntegral

end
