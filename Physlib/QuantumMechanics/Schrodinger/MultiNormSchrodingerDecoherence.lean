/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization
public import Physlib.QuantumMechanics.ComplexAction.DowkerHalliwellDecoherenceFunctional

/-!
# Decoherence functionals of multi-norm Schrödinger branches

The square-analysis pieces of the global multi-norm partition are treated as
complex history amplitudes.  Their existing Sorkin--Johnston/Dowker--Halliwell
rank-one decoherence functional has an exact Born diagonal whose locally finite
sum is the original pointwise Born weight.  Free Schrödinger phase evolution
leaves the entire decoherence kernel invariant, not merely its diagonal.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

namespace MultiNormSchrodingerDecoherence

open Physlib.Mathematics.HarmonicAnalysis
open MultiNormGlobalFrequencyCover MultiNormGlobalReproducingFormula
  MultiNormGlobalComplexReproducingFormula
open MultiNormSchrodingerLocalization EuclideanL2FreeEvolution
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism
open Physlib.QuantumMechanics.ComplexAction.DowkerHalliwellDecoherenceFunctional

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

/-! ## A. The localized decoherence kernel -/

/-- The rank-one decoherence functional of the global multi-norm
square-analysis branch amplitudes at a fixed frequency. -/
def multiNormDecoherenceFunctional
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) : FullTubeIndex E → FullTubeIndex E → ℂ :=
  decoherenceFunctional
    (fun A => globalNormalizedComplexAnalysisPiece A f ξ)

lemma multiNormDecoherenceFunctional_apply
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) (A B : FullTubeIndex E) :
    multiNormDecoherenceFunctional E f ξ A B =
      globalNormalizedComplexAnalysisPiece A f ξ *
        starRingEnd ℂ (globalNormalizedComplexAnalysisPiece B f ξ) := by
  exact decoherenceFunctional_apply _ A B

/-- The multi-norm decoherence kernel is exactly the existing
Dowker--Halliwell Gram kernel of the conjugated branch amplitudes. -/
lemma multiNormDecoherenceFunctional_eq_gram
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    multiNormDecoherenceFunctional E f ξ =
      gramDecoherence
        (fun A => starRingEnd ℂ
          (globalNormalizedComplexAnalysisPiece A f ξ)) := by
  exact decoherenceFunctional_eq_gramDecoherence _

/-! ## B. Exact Born resolution -/

/-- The quantal measure of one localized branch is its normalized symbol times
the original pointwise Born weight. -/
lemma multiNormDecoherenceFunctional_quantalMeasure
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) (A : FullTubeIndex E) :
    quantalMeasure (multiNormDecoherenceFunctional E f ξ) A =
      MultiNormGlobalNormalizedPartition.globalNormalizedSmoothSymbol A ξ *
        Complex.normSq (f ξ) := by
  rw [multiNormDecoherenceFunctional,
    decoherenceFunctional_quantalMeasure,
    normSq_globalNormalizedComplexAnalysisPiece (V := V)]

/-- The locally finite Born diagonals sum exactly to the Born weight of the
unlocalized complex amplitude. -/
lemma finsum_multiNormDecoherenceFunctional_quantalMeasure_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    ∑ᶠ A : FullTubeIndex E,
      quantalMeasure (multiNormDecoherenceFunctional E f ξ) A =
        Complex.normSq (f ξ) := by
  simpa [multiNormDecoherenceFunctional,
    decoherenceFunctional_quantalMeasure] using
      finsum_normSq_globalNormalizedComplexAnalysisPiece_eq
        (V := V) E f ξ

/-- The canonical finite carrier already contains the full Born diagonal. -/
lemma sum_globalSymbolFinsupport_multiNormQuantalMeasure_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    ∑ A ∈ globalSymbolFinsupport E ξ,
      quantalMeasure (multiNormDecoherenceFunctional E f ξ) A =
        Complex.normSq (f ξ) := by
  simpa [multiNormDecoherenceFunctional,
    decoherenceFunctional_quantalMeasure] using
      sum_globalSymbolFinsupport_complexAnalysis_normSq_eq
        (V := V) E f ξ

/-- The rank-one interference bound is saturated by every pair of multi-norm
branches. -/
lemma multiNormDecoherenceFunctional_offdiag_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) (A B : FullTubeIndex E) :
    ‖multiNormDecoherenceFunctional E f ξ A B‖ ^ 2 =
      quantalMeasure (multiNormDecoherenceFunctional E f ξ) A *
        quantalMeasure (multiNormDecoherenceFunctional E f ξ) B := by
  simpa [multiNormDecoherenceFunctional, quantalMeasure] using
    decoherenceFunctional_offdiag_eq
      (fun C : FullTubeIndex E =>
        globalNormalizedComplexAnalysisPiece C f ξ) A B

/-! ## C. Schrödinger phase invariance -/

/-- Multiplication of the total amplitude by a unit-modulus phase leaves the
entire localized decoherence kernel invariant. -/
lemma multiNormDecoherenceFunctional_phase_invariant
    (E : StandardMultiNormMatrix ι) (f q : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) (hq : Complex.normSq (q ξ) = 1)
    (A B : FullTubeIndex E) :
    multiNormDecoherenceFunctional E (fun η => q η * f η) ξ A B =
      multiNormDecoherenceFunctional E f ξ A B := by
  have hunit : q ξ * starRingEnd ℂ (q ξ) = 1 := by
    rw [Complex.mul_conj, hq, Complex.ofReal_one]
  rw [multiNormDecoherenceFunctional_apply,
    multiNormDecoherenceFunctional_apply]
  simp only [globalNormalizedComplexAnalysisPiece, map_mul]
  calc
    _ = (q ξ * starRingEnd ℂ (q ξ)) *
        ((Real.sqrt
              (MultiNormGlobalNormalizedPartition.globalNormalizedSmoothSymbol A ξ) : ℂ) *
          f ξ *
          starRingEnd ℂ
            (Real.sqrt
              (MultiNormGlobalNormalizedPartition.globalNormalizedSmoothSymbol B ξ) : ℂ) *
          starRingEnd ℂ (f ξ)) := by ring
    _ = _ := by rw [hunit, one_mul]; ring

/-- The repository's free Schrödinger phase leaves the multi-norm decoherence
kernel invariant in the Euclidean one-block specialization. -/
lemma euclideanMultiNormDecoherence_freeSchrodingerPhase_invariant {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (A B : FullTubeIndex E) :
    multiNormDecoherenceFunctional
        (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
        (fun η => freeSchrodingerPhase t (η ()) * f (η ()))
        (fun _ => ξ) A B =
      multiNormDecoherenceFunctional
        (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
        (fun η => f (η ())) (fun _ => ξ) A B := by
  apply multiNormDecoherenceFunctional_phase_invariant
  rw [Complex.normSq_eq_norm_sq, norm_freeSchrodingerPhase]
  norm_num

/-- Capstone: multi-norm branches form the existing Gram decoherence kernel,
their Born diagonal resolves the original amplitude exactly, their pure-state
off-diagonal bound is saturated, and free Schrödinger evolution preserves the
kernel. -/
lemma multiNorm_schrodingerDecoherence_bridge {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (A B : FullTubeIndex E) :
    (∑ᶠ C : FullTubeIndex E,
      quantalMeasure
        (multiNormDecoherenceFunctional
          (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
          (fun η => f (η ())) (fun _ => ξ)) C) =
        Complex.normSq (f ξ) ∧
    ‖multiNormDecoherenceFunctional
        (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
        (fun η => f (η ())) (fun _ => ξ) A B‖ ^ 2 =
      quantalMeasure
          (multiNormDecoherenceFunctional
            (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
            (fun η => f (η ())) (fun _ => ξ)) A *
        quantalMeasure
          (multiNormDecoherenceFunctional
            (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
            (fun η => f (η ())) (fun _ => ξ)) B ∧
    multiNormDecoherenceFunctional
        (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
        (fun η => freeSchrodingerPhase t (η ()) * f (η ()))
        (fun _ => ξ) A B =
      multiNormDecoherenceFunctional
        (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
        (fun η => f (η ())) (fun _ => ξ) A B := by
  exact ⟨finsum_multiNormDecoherenceFunctional_quantalMeasure_eq
      (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
      (fun η => f (η ())) (fun _ => ξ),
    multiNormDecoherenceFunctional_offdiag_eq
      (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E
      (fun η => f (η ())) (fun _ => ξ) A B,
    euclideanMultiNormDecoherence_freeSchrodingerPhase_invariant
      E f ξ t A B⟩

end MultiNormSchrodingerDecoherence

end Physlib.QuantumMechanics.Schrodinger
