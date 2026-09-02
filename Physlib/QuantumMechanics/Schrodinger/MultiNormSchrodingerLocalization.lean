/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula
public import Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger

/-!
# Multi-norm localization of complex Schrödinger amplitudes

This module connects the smooth multi-norm analysis branches to two existing
Schrödinger layers.  First, every complex-linear functional Schrödinger
generator commutes pointwise with localization.  Second, the one-block
Euclidean specialization defines genuine `L²` frequency localizations that
are contractions and commute with the repository's free Schrödinger evolution.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Physlib.QuantumMechanics.Schrodinger

namespace MultiNormSchrodingerLocalization

open Physlib.Mathematics.HarmonicAnalysis
open MultiNormGlobalFrequencyCover MultiNormGlobalNormalizedPartition
  MultiNormGlobalComplexReproducingFormula
open EuclideanL2FreeEvolution
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger

/-! ## A. Functional Schrödinger covariance -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

/-- A complex-linear operator commutes with every global square-analysis
branch.  This is the abstract fixed-background Schrödinger covariance. -/
lemma globalComplexAnalysisPiece_commutes_linearMap
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E)
    (H : ℂ →ₗ[ℂ] ℂ) (f : (∀ i, V i) → ℂ) (ξ : ∀ i, V i) :
    H (globalNormalizedComplexAnalysisPiece A f ξ) =
      globalNormalizedComplexAnalysisPiece A (fun η => H (f η)) ξ := by
  change H ((Real.sqrt (globalNormalizedSmoothSymbol A ξ) : ℂ) • f ξ) =
    (Real.sqrt (globalNormalizedSmoothSymbol A ξ) : ℂ) • H (f ξ)
  exact H.map_smul _ _

/-- The existing Ipek--Caticha smeared functional Schrödinger generator
commutes with every global multi-norm analysis branch. -/
lemma globalComplexAnalysisPiece_commutes_smearedSchrodinger
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E)
    (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ)
    (f : (∀ i, V i) → ℂ) (ξ : ∀ i, V i) :
    smearedSchrodingerGenerator N Ni Hperp Hi
        (globalNormalizedComplexAnalysisPiece A f ξ) =
      globalNormalizedComplexAnalysisPiece A
        (fun η => smearedSchrodingerGenerator N Ni Hperp Hi (f η)) ξ :=
  globalComplexAnalysisPiece_commutes_linearMap (V := V) A
    (smearedSchrodingerGenerator N Ni Hperp Hi) f ξ

/-! ## B. Euclidean `L²` analysis branches -/

/-- The Euclidean specialization evaluates the global symbol on the unique
coordinate block whose value is the whole Euclidean frequency vector. -/
def euclideanMultiNormAnalysisSymbol {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (globalNormalizedSmoothSymbol
    (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) A (fun _ => ξ))

lemma continuous_euclideanMultiNormAnalysisSymbol {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E) :
    Continuous (euclideanMultiNormAnalysisSymbol (n := n) E A) := by
  apply Real.continuous_sqrt.comp
  exact (contDiff_globalNormalizedSmoothSymbol
    (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E A).continuous.comp
      (continuous_pi fun _ => continuous_id)

lemma euclideanMultiNormAnalysisSymbol_nonneg {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    0 ≤ euclideanMultiNormAnalysisSymbol E A ξ :=
  Real.sqrt_nonneg _

lemma euclideanMultiNormAnalysisSymbol_le_one {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    euclideanMultiNormAnalysisSymbol E A ξ ≤ 1 := by
  rw [euclideanMultiNormAnalysisSymbol, Real.sqrt_le_one]
  exact (globalSmoothPartitionOfUnity
    (V := fun _ : Unit => EuclideanSpace ℝ (Fin n)) E).le_one A (fun _ => ξ)

lemma aestronglyMeasurable_euclideanMultiNormAnalysisSymbol_mul {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (g : EuclideanL2 n) :
    AEStronglyMeasurable
      (fun ξ => (euclideanMultiNormAnalysisSymbol E A ξ : ℂ) * g ξ) := by
  exact ((Complex.continuous_ofReal.comp
    (continuous_euclideanMultiNormAnalysisSymbol E A)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable g)

lemma memLp_euclideanMultiNormAnalysisSymbol_mul {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (g : EuclideanL2 n) :
    MemLp (fun ξ => (euclideanMultiNormAnalysisSymbol E A ξ : ℂ) * g ξ) 2 := by
  apply (Lp.memLp g).mono
    (aestronglyMeasurable_euclideanMultiNormAnalysisSymbol_mul E A g)
  exact Filter.Eventually.of_forall fun ξ => by
    calc
      ‖(euclideanMultiNormAnalysisSymbol E A ξ : ℂ) * g ξ‖ =
          euclideanMultiNormAnalysisSymbol E A ξ * ‖g ξ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (euclideanMultiNormAnalysisSymbol_nonneg E A ξ)]
      _ ≤ 1 * ‖g ξ‖ := mul_le_mul_of_nonneg_right
        (euclideanMultiNormAnalysisSymbol_le_one E A ξ) (norm_nonneg _)
      _ = ‖g ξ‖ := one_mul _

/-- The smooth multi-norm square-analysis cutoff on Euclidean frequency-space
`L²`. -/
def euclideanMultiNormAnalysisCutoff {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (g : EuclideanL2 n) : EuclideanL2 n :=
  (memLp_euclideanMultiNormAnalysisSymbol_mul E A g).toLp
    (fun ξ => (euclideanMultiNormAnalysisSymbol E A ξ : ℂ) * g ξ)

lemma euclideanMultiNormAnalysisCutoff_coeFn {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (g : EuclideanL2 n) :
    euclideanMultiNormAnalysisCutoff E A g =ᵐ[volume]
      fun ξ => (euclideanMultiNormAnalysisSymbol E A ξ : ℂ) * g ξ :=
  MemLp.coeFn_toLp _

/-- Each smooth multi-norm analysis cutoff is an `L²` contraction. -/
lemma norm_euclideanMultiNormAnalysisCutoff_le {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (g : EuclideanL2 n) :
    ‖euclideanMultiNormAnalysisCutoff E A g‖ ≤ ‖g‖ := by
  rw [euclideanMultiNormAnalysisCutoff, Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono
  · finiteness
  apply eLpNorm_mono_ae
  exact Filter.Eventually.of_forall fun ξ => by
    calc
      ‖(euclideanMultiNormAnalysisSymbol E A ξ : ℂ) * g ξ‖ =
          euclideanMultiNormAnalysisSymbol E A ξ * ‖g ξ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (euclideanMultiNormAnalysisSymbol_nonneg E A ξ)]
      _ ≤ 1 * ‖g ξ‖ := mul_le_mul_of_nonneg_right
        (euclideanMultiNormAnalysisSymbol_le_one E A ξ) (norm_nonneg _)
      _ = ‖g ξ‖ := one_mul _

/-! ## C. Covariance under free Schrödinger evolution -/

/-- The smooth multi-norm cutoff commutes with the existing free Schrödinger
frequency multiplier. -/
lemma euclideanMultiNormAnalysisCutoff_commutes_multiplier {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (t : ℝ) (g : EuclideanL2 n) :
    euclideanMultiNormAnalysisCutoff E A
        (freeSchrodingerMultiplier t g) =
      freeSchrodingerMultiplier t
        (euclideanMultiNormAnalysisCutoff E A g) := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    euclideanMultiNormAnalysisCutoff_coeFn E A
      (freeSchrodingerMultiplier t g),
    freeSchrodingerMultiplier_coeFn t g,
    freeSchrodingerMultiplier_coeFn t
      (euclideanMultiNormAnalysisCutoff E A g),
    euclideanMultiNormAnalysisCutoff_coeFn E A g
  ] with ξ hleft hmult hright hcut
  rw [hleft, hmult, hright, hcut]
  ring

/-- The physical-space smooth multi-norm frequency localization. -/
def euclideanMultiNormFrequencyLocalization {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (f : EuclideanL2 n) : EuclideanL2 n :=
  𝓕⁻ (euclideanMultiNormAnalysisCutoff E A (𝓕 f))

/-- The physical-space smooth multi-norm localization commutes with the existing
free Schrödinger evolution. -/
lemma euclideanMultiNormFrequencyLocalization_commutes_evolution {n : ℕ}
    (E : StandardMultiNormMatrix Unit) (A : FullTubeIndex E)
    (t : ℝ) (f : EuclideanL2 n) :
    euclideanMultiNormFrequencyLocalization E A
        (freeSchrodingerEvolution t f) =
      freeSchrodingerEvolution t
        (euclideanMultiNormFrequencyLocalization E A f) := by
  simp [euclideanMultiNormFrequencyLocalization, freeSchrodingerEvolution,
    euclideanMultiNormAnalysisCutoff_commutes_multiplier]

/-- Capstone: the same global multi-norm branch commutes with the Ipek--Caticha
functional generator, and its Euclidean `L²` realization is contractive and
covariant under the unitary free Schrödinger flow. -/
lemma multiNorm_schrodingerLocalization_bridge
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E)
    (N Ni : ℝ) (Hperp Hi : ℂ →ₗ[ℂ] ℂ)
    (f : (∀ i, V i) → ℂ) (ξ : ∀ i, V i)
    {n : ℕ} (Eeucl : StandardMultiNormMatrix Unit)
    (Aeucl : FullTubeIndex Eeucl) (t : ℝ) (g : EuclideanL2 n) :
    smearedSchrodingerGenerator N Ni Hperp Hi
        (globalNormalizedComplexAnalysisPiece A f ξ) =
      globalNormalizedComplexAnalysisPiece A
        (fun η => smearedSchrodingerGenerator N Ni Hperp Hi (f η)) ξ ∧
    ‖euclideanMultiNormAnalysisCutoff Eeucl Aeucl g‖ ≤ ‖g‖ ∧
    euclideanMultiNormFrequencyLocalization Eeucl Aeucl
        (freeSchrodingerEvolution t g) =
      freeSchrodingerEvolution t
        (euclideanMultiNormFrequencyLocalization Eeucl Aeucl g) := by
  exact ⟨globalComplexAnalysisPiece_commutes_smearedSchrodinger
      (V := V) A N Ni Hperp Hi f ξ,
    norm_euclideanMultiNormAnalysisCutoff_le Eeucl Aeucl g,
    euclideanMultiNormFrequencyLocalization_commutes_evolution
      Eeucl Aeucl t g⟩

end MultiNormSchrodingerLocalization

end Physlib.QuantumMechanics.Schrodinger
