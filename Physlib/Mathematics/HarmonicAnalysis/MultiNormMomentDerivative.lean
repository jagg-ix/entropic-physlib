/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Data.Fintype.Pi
public import Physlib.Mathematics.Distribution.SchwartzNuclear.HermiteTensorProduct

/-!
# Multi-index cancellation and derivative decompositions

This module supplies the finite multi-index and bundled-Schwartz API needed to
state the Hadamard-lemma mechanism in Lemma 4.1 of Hejna--Nagel--Ricci.  It
reuses Mathlib's iterated directional derivative on Schwartz space, including
its support theorem, rather than introducing a second derivative operation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormMomentDerivative

/-- The repository's existing coordinate multi-index on `ℝ^d`. -/
abbrev CoordinateMultiIndex (d : ℕ) := GaussianField.MultiIndex d

/-- Total order `|α|` of a coordinate multi-index. -/
def totalOrder {d : ℕ} (α : CoordinateMultiIndex d) : ℕ :=
  GaussianField.MultiIndex.abs α

/-- The finite set of coordinate multi-indices of total order exactly `m`. -/
def exactMultiIndices (d m : ℕ) : Finset (CoordinateMultiIndex d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range (m + 1)).filter
    (fun α => totalOrder α = m)

@[simp]
lemma mem_exactMultiIndices_iff {d m : ℕ} {α : CoordinateMultiIndex d} :
    α ∈ exactMultiIndices d m ↔ totalOrder α = m := by
  simp only [exactMultiIndices, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, and_iff_right_iff_imp]
  intro h i
  exact Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i) |>.trans h.le)

/-- Coordinate directions, with the `i`-th basis vector repeated `α i`
times.  Feeding this list to Mathlib's line derivative realizes `∂^α`. -/
def multiIndexDirections {d : ℕ} (α : CoordinateMultiIndex d) :
    List (EuclideanSpace ℝ (Fin d)) :=
  (Finset.univ.toList).flatMap fun i =>
    List.replicate (α i) (EuclideanSpace.single i 1)

lemma length_multiIndexDirections {d : ℕ} (α : CoordinateMultiIndex d) :
    (multiIndexDirections α).length = totalOrder α := by
  simp [multiIndexDirections, totalOrder, GaussianField.MultiIndex.abs]

/-- The coordinate derivative `∂^α`, implemented by Mathlib's iterated line
derivative on the bundled Schwartz space. -/
def coordinateDerivative {d : ℕ} (α : CoordinateMultiIndex d)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  LineDeriv.iteratedLineDerivOp (multiIndexDirections α |>.get) f

/-- Coordinate differentiation does not enlarge closed support. -/
lemma tsupport_coordinateDerivative_subset {d : ℕ}
    (α : CoordinateMultiIndex d) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    tsupport (coordinateDerivative α f) ⊆ tsupport f := by
  exact SchwartzMap.tsupport_iteratedLineDerivOp_subset
    (multiIndexDirections α |>.get) f

/-- The polynomial moment `∫ x^α ψ(x) dx` used in the paper's definition of
cancellation. -/
def schwartzMoment {d : ℕ} (α : CoordinateMultiIndex d)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : ℂ :=
  ∫ x, (∏ i, (x i : ℂ) ^ α i) * ψ x

/-- Vanishing of every moment of total degree strictly below `m`. -/
def HasCancellationOrder {d : ℕ}
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (m : ℕ) : Prop :=
  ∀ α : CoordinateMultiIndex d, totalOrder α < m → schwartzMoment α ψ = 0

/-- The finite component family is normalized relative to `ψ` in the paper's
Schwartz-seminorm sense. -/
def ComponentsNormalizedRelative {d : ℕ}
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (m : ℕ)
    (component : CoordinateMultiIndex d →
      𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : Prop :=
  ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ k' n' : ℕ,
    ∀ α ∈ exactMultiIndices d m,
      SchwartzMap.seminorm ℂ k n (component α) ≤
        C * SchwartzMap.seminorm ℂ k' n' ψ

/-- A paper-faithful derivative-decomposition certificate for Lemma 4.1.
`component α` is relevant only when `|α| = m`; keeping it total makes finite
sums and downstream tensor constructions straightforward. -/
structure DerivativeDecomposition {d : ℕ}
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (m : ℕ) where
  component : CoordinateMultiIndex d → 𝓢(EuclideanSpace ℝ (Fin d), ℂ)
  reconstruct :
    ψ = ∑ α ∈ exactMultiIndices d m, coordinateDerivative α (component α)
  normalized : ComponentsNormalizedRelative ψ m component
  support_control :
    ∀ α ∈ exactMultiIndices d m, tsupport (coordinateDerivative α (component α)) ⊆
      tsupport (component α)

/-- Every certified component in an order-`m` decomposition is differentiated
exactly `m` times. -/
lemma derivativeDecomposition_exact_order {d m : ℕ}
    {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
    (_D : DerivativeDecomposition ψ m) {α : CoordinateMultiIndex d}
    (hα : α ∈ exactMultiIndices d m) :
    (multiIndexDirections α).length = m := by
  rw [length_multiIndexDirections, (mem_exactMultiIndices_iff.mp hα)]

/-- The support field of a decomposition is supplied canonically by Mathlib's
support theorem; callers constructing the Hadamard components never need a
second support proof. -/
def DerivativeDecomposition.mkCanonical {d m : ℕ}
    {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
    (component : CoordinateMultiIndex d → 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (reconstruct :
      ψ = ∑ α ∈ exactMultiIndices d m, coordinateDerivative α (component α))
    (normalized : ComponentsNormalizedRelative ψ m component) :
    DerivativeDecomposition ψ m where
  component := component
  reconstruct := reconstruct
  normalized := normalized
  support_control := fun α _ => tsupport_coordinateDerivative_subset α (component α)

/-- Lemma 4.1 interface: an analytic Hadamard construction is precisely a map
from order-`m` moment cancellation to the finite, support-controlled
multi-index derivative decomposition consumed by the rest of Section 4. -/
def HadamardDecompositionMechanism (d m : ℕ) :=
  ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ),
    HasCancellationOrder ψ m → DerivativeDecomposition ψ m

/-- First capstone: applying a Hadamard mechanism produces the exact arbitrary
multi-index decomposition, with every summand an `m`-fold bundled Schwartz
derivative and with support controlled by the existing Mathlib theorem. -/
lemma arbitraryMultiIndex_moment_derivative_decomposition
    {d m : ℕ} (H : HadamardDecompositionMechanism d m)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hψ : HasCancellationOrder ψ m) :
    ∃ components : CoordinateMultiIndex d → 𝓢(EuclideanSpace ℝ (Fin d), ℂ),
      ψ = ∑ α ∈ exactMultiIndices d m,
        coordinateDerivative α (components α) ∧
      ComponentsNormalizedRelative ψ m components ∧
      (∀ α ∈ exactMultiIndices d m,
        (multiIndexDirections α).length = m ∧
        tsupport (coordinateDerivative α (components α)) ⊆ tsupport (components α)) := by
  let D := H ψ hψ
  refine ⟨D.component, D.reconstruct, D.normalized, ?_⟩
  intro α hα
  exact ⟨derivativeDecomposition_exact_order D hα, D.support_control α hα⟩

end MultiNormMomentDerivative

end Physlib.Mathematics.HarmonicAnalysis
