/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
meta import Zil

/-!
# Euclidean Sobolev regularity and rough frequency localization

This module supplies the next Fourier-analytic layer for the Euclidean free
Schrödinger evolution.  It implements the Bessel-potential definition of
`H^s(ℝⁿ)` and the rough annular Fourier cutoff used in the Littlewood--Paley
reduction in Jonathan Hickman's exposition of the Du--Zhang theorem.

The proved content is deliberately below the Littlewood--Paley
characterization: the cutoff is an idempotent `L²` contraction, it commutes
with free Schrödinger evolution, preserves Sobolev membership, and contracts
the corresponding weighted norm.  No dyadic square-function equivalence,
maximal estimate, or almost-everywhere convergence theorem is asserted.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory Set
open scoped FourierTransform ENNReal NNReal SchwartzMap InnerProductSpace

namespace Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization

open EuclideanL2FreeEvolution

/-! # A. The Fourier definition of `H^s(ℝⁿ)` -/

/-- The inhomogeneous Bessel-potential weight
`(1 + ‖ξ‖²)^(s/2)` used to define `H^s(ℝⁿ)`. -/
def besselPotentialWeight {n : ℕ}
    (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

lemma continuous_besselPotentialWeight {n : ℕ} (s : ℝ) :
    Continuous (besselPotentialWeight (n := n) s) := by
  unfold besselPotentialWeight
  apply Continuous.rpow_const
  · fun_prop
  · intro ξ
    left
    positivity

lemma besselPotentialWeight_pos {n : ℕ}
    (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    0 < besselPotentialWeight s ξ := by
  unfold besselPotentialWeight
  positivity

lemma besselPotentialWeight_mono {n : ℕ}
    {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    besselPotentialWeight s₁ ξ ≤ besselPotentialWeight s₂ ξ := by
  unfold besselPotentialWeight
  apply Real.rpow_le_rpow_of_exponent_le
  · nlinarith [sq_nonneg ‖ξ‖]
  · linarith

@[simp] lemma besselPotentialWeight_zero {n : ℕ}
    (ξ : EuclideanSpace ℝ (Fin n)) :
    besselPotentialWeight 0 ξ = 1 := by
  simp [besselPotentialWeight]

/-- The weighted Fourier representative entering the `H^s` norm. -/
def weightedFourier {n : ℕ}
    (s : ℝ) (f : EuclideanL2 n) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun ξ => (besselPotentialWeight s ξ : ℂ) * (𝓕 f) ξ

lemma aestronglyMeasurable_weightedFourier {n : ℕ}
    (s : ℝ) (f : EuclideanL2 n) :
    AEStronglyMeasurable (weightedFourier s f) := by
  exact
    ((Complex.continuous_ofReal.comp
      (continuous_besselPotentialWeight s)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable (𝓕 f))

/-- Membership in the inhomogeneous Bessel-potential Sobolev space
`H^s(ℝⁿ)`: the weighted Fourier representative lies in `L²`. -/
def HasSobolevRegularity {n : ℕ}
    (s : ℝ) (f : EuclideanL2 n) : Prop :=
  MemLp (weightedFourier s f) 2

/-- The native Lean carrier for `H^s(ℝⁿ)`, as a subtype of Euclidean `L²`
equipped with the Bessel-potential membership certificate. -/
def EuclideanHs (n : ℕ) (s : ℝ) :=
  {f : EuclideanL2 n // HasSobolevRegularity s f}

/-- The `L²` representative of `(1 - Δ)^(s/2) f` in frequency space. -/
def sobolevDerivativeFrequency {n : ℕ} {s : ℝ}
    {f : EuclideanL2 n} (hf : HasSobolevRegularity s f) :
    EuclideanL2 n :=
  hf.toLp (weightedFourier s f)

/-- The inhomogeneous `H^s` norm defined by the Bessel-potential Fourier
multiplier. -/
def sobolevNorm {n : ℕ}
    (s : ℝ) (f : EuclideanL2 n) (hf : HasSobolevRegularity s f) : ℝ :=
  ‖sobolevDerivativeFrequency hf‖

lemma hasSobolevRegularity_zero {n : ℕ}
    (f : EuclideanL2 n) :
    HasSobolevRegularity 0 f := by
  have hFourier : MemLp (fun ξ => (𝓕 f) ξ) 2 := Lp.memLp (𝓕 f)
  exact hFourier.ae_eq (Filter.Eventually.of_forall fun ξ => by
    simp [weightedFourier]
  )

lemma sobolevNorm_zero_eq_l2Norm {n : ℕ}
    (f : EuclideanL2 n) :
    sobolevNorm 0 f (hasSobolevRegularity_zero f) = ‖f‖ := by
  have hderiv :
      sobolevDerivativeFrequency (hasSobolevRegularity_zero f) = 𝓕 f := by
    apply Lp.ext (μ := volume)
    filter_upwards [
      MemLp.coeFn_toLp (hasSobolevRegularity_zero f)
    ] with ξ hξ
    change
      (hasSobolevRegularity_zero f).toLp (weightedFourier 0 f) ξ =
        (𝓕 f) ξ
    rw [hξ]
    simp [weightedFourier]
  rw [sobolevNorm, hderiv, MeasureTheory.Lp.norm_fourier_eq]

lemma norm_weightedFourier_mono {n : ℕ}
    {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    (f : EuclideanL2 n) (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖weightedFourier s₁ f ξ‖ ≤ ‖weightedFourier s₂ f ξ‖ := by
  rw [weightedFourier, weightedFourier, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (besselPotentialWeight_pos s₁ ξ),
    abs_of_pos (besselPotentialWeight_pos s₂ ξ)]
  gcongr
  exact besselPotentialWeight_mono hs ξ

/-- The paper's Sobolev hierarchy:
`H^{s₂}(ℝⁿ) ⊆ H^{s₁}(ℝⁿ)` whenever `s₁ ≤ s₂`. -/
lemma HasSobolevRegularity.mono {n : ℕ}
    {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s₂ f) :
    HasSobolevRegularity s₁ f := by
  exact hf.of_le
    (aestronglyMeasurable_weightedFourier s₁ f)
    (Filter.Eventually.of_forall fun ξ =>
      norm_weightedFourier_mono hs f ξ)

set_option backward.isDefEq.respectTransparency false in
/-- The `H^{s₁}` norm is bounded by the `H^{s₂}` norm when `s₁ ≤ s₂`. -/
lemma sobolevNorm_mono {n : ℕ}
    {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s₂ f) :
    sobolevNorm s₁ f (hf.mono hs) ≤ sobolevNorm s₂ f hf := by
  unfold sobolevNorm sobolevDerivativeFrequency
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono
  · finiteness
  exact eLpNorm_mono_ae
    (Filter.Eventually.of_forall fun ξ =>
      norm_weightedFourier_mono hs f ξ)

/-! ## A.1. Complete `H¹(ℝ³)` energy-coordinate carrier -/

/-- Divide a continuum `L²` energy coordinate by the positive
`H¹` Bessel weight. This is the frequency representative whose inverse
Fourier transform realizes the corresponding `H¹(ℝ³)` function. -/
def inverseBesselOneWeighted
    (u : EuclideanL2 3) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun ξ => ((besselPotentialWeight 1 ξ)⁻¹ : ℂ) * u ξ

/-- The first-order Bessel weight is at least one. -/
lemma one_le_besselPotentialWeight_one
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    1 ≤ besselPotentialWeight 1 ξ := by
  simpa using besselPotentialWeight_mono (n := 3) (s₁ := 0) (s₂ := 1)
    zero_le_one ξ

lemma aestronglyMeasurable_inverseBesselOneWeighted
    (u : EuclideanL2 3) :
    AEStronglyMeasurable (inverseBesselOneWeighted u) := by
  exact
    ((Complex.continuous_ofReal.comp
      (continuous_besselPotentialWeight 1)).inv₀
        (fun ξ => Complex.ofReal_ne_zero.mpr
          (besselPotentialWeight_pos 1 ξ).ne')).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u)

/-- Division by the `H¹` Bessel weight is an `L²` contraction. -/
lemma memLp_inverseBesselOneWeighted
    (u : EuclideanL2 3) :
    MemLp (inverseBesselOneWeighted u) 2 := by
  refine (Lp.memLp u).of_le
    (aestronglyMeasurable_inverseBesselOneWeighted u)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [inverseBesselOneWeighted, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (besselPotentialWeight_pos 1 ξ)]
  simpa using mul_le_mul_of_nonneg_right
    (inv_le_one_of_one_le₀ (one_le_besselPotentialWeight_one ξ))
    (norm_nonneg (u ξ))

/-- The inverse-Bessel multiplier bundled as an element of continuum
frequency-space `L²(ℝ³)`. -/
def inverseBesselOneMultiplier
    (u : EuclideanL2 3) : EuclideanL2 3 :=
  (memLp_inverseBesselOneWeighted u).toLp
    (inverseBesselOneWeighted u)

lemma inverseBesselOneMultiplier_coeFn
    (u : EuclideanL2 3) :
    inverseBesselOneMultiplier u =ᵐ[volume]
      inverseBesselOneWeighted u :=
  MemLp.coeFn_toLp _

/-- Reconstruct an `H¹(ℝ³)` representative from its complete `L²`
Bessel-energy coordinate. -/
def hOneRepresentative
    (u : EuclideanL2 3) : EuclideanL2 3 :=
  𝓕⁻ (inverseBesselOneMultiplier u)

lemma fourier_hOneRepresentative
    (u : EuclideanL2 3) :
    𝓕 (hOneRepresentative u) = inverseBesselOneMultiplier u := by
  simp [hOneRepresentative]

/-- Applying the first-order Bessel multiplier to the reconstructed
representative recovers the original energy coordinate almost everywhere. -/
lemma weightedFourier_hOneRepresentative_ae
    (u : EuclideanL2 3) :
    weightedFourier 1 (hOneRepresentative u) =ᵐ[volume] u := by
  filter_upwards [inverseBesselOneMultiplier_coeFn u] with ξ hξ
  rw [weightedFourier, fourier_hOneRepresentative, hξ,
    inverseBesselOneWeighted]
  field_simp [(besselPotentialWeight_pos 1 ξ).ne']

/-- Every continuum `L²` energy coordinate reconstructs an actual
inhomogeneous `H¹(ℝ³)` representative. -/
lemma hOneRepresentative_hasSobolevRegularity
    (u : EuclideanL2 3) :
    HasSobolevRegularity 1 (hOneRepresentative u) := by
  exact (Lp.memLp u).ae_eq
    (weightedFourier_hOneRepresentative_ae u).symm

/-- The reconstructed representative has exactly the supplied energy
coordinate, not merely an equivalent norm. -/
lemma sobolevDerivativeFrequency_hOneRepresentative
    (u : EuclideanL2 3) :
    sobolevDerivativeFrequency
      (hOneRepresentative_hasSobolevRegularity u) = u := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    MemLp.coeFn_toLp (hOneRepresentative_hasSobolevRegularity u),
    weightedFourier_hOneRepresentative_ae u
  ] with ξ hto hweighted
  simpa [sobolevDerivativeFrequency] using hto.trans hweighted

lemma inverseBesselOneMultiplier_sobolevDerivativeFrequency
    (f : EuclideanL2 3) (hf : HasSobolevRegularity 1 f) :
    inverseBesselOneMultiplier (sobolevDerivativeFrequency hf) = 𝓕 f := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    inverseBesselOneMultiplier_coeFn (sobolevDerivativeFrequency hf),
    MemLp.coeFn_toLp hf
  ] with ξ hinv hderiv
  rw [hinv, inverseBesselOneWeighted]
  change ((besselPotentialWeight 1 ξ)⁻¹ : ℂ) *
      (hf.toLp (weightedFourier 1 f)) ξ = (𝓕 f) ξ
  rw [hderiv, weightedFourier]
  field_simp [(besselPotentialWeight_pos 1 ξ).ne']

/-- Conversely, reconstructing from an existing `H¹` energy coordinate
returns the original `L²` representative. -/
lemma hOneRepresentative_sobolevDerivativeFrequency
    (f : EuclideanL2 3) (hf : HasSobolevRegularity 1 f) :
    hOneRepresentative (sobolevDerivativeFrequency hf) = f := by
  rw [hOneRepresentative,
    inverseBesselOneMultiplier_sobolevDerivativeFrequency f hf]
  exact FourierTransform.fourierInv_fourier_eq f

/-- The complete Hilbert carrier for `H¹(ℝ³)`, represented by the full
continuum Bessel-energy coordinate. It inherits completeness and the inner
product from `L²(ℝ³)`; this is not a finite-mode approximation. -/
abbrev EuclideanHOneThree : Type := EuclideanL2 3

/-- Extract the complete energy coordinate of an `H¹` representative. -/
def hOneEnergyCoordinate
    (f : EuclideanHs 3 1) : EuclideanHOneThree :=
  sobolevDerivativeFrequency f.2

/-- Bundle a complete energy coordinate as an `H¹` representative. -/
def hOneFromEnergyCoordinate
    (u : EuclideanHOneThree) : EuclideanHs 3 1 :=
  ⟨hOneRepresentative u, hOneRepresentative_hasSobolevRegularity u⟩

@[simp, zil_level structural] lemma hOneEnergyCoordinate_fromEnergyCoordinate
    (u : EuclideanHOneThree) :
    hOneEnergyCoordinate (hOneFromEnergyCoordinate u) = u :=
  sobolevDerivativeFrequency_hOneRepresentative u

@[simp] lemma hOneFromEnergyCoordinate_energyCoordinate
    (f : EuclideanHs 3 1) :
    hOneFromEnergyCoordinate (hOneEnergyCoordinate f) = f := by
  apply Subtype.ext
  exact hOneRepresentative_sobolevDerivativeFrequency f.1 f.2

/-- Exact equivalence between the predicate-defined `H¹(ℝ³)` subtype and
its complete Hilbert Bessel-energy carrier. -/
def hOneEnergyEquiv : EuclideanHs 3 1 ≃ EuclideanHOneThree where
  toFun := hOneEnergyCoordinate
  invFun := hOneFromEnergyCoordinate
  left_inv := hOneFromEnergyCoordinate_energyCoordinate
  right_inv := hOneEnergyCoordinate_fromEnergyCoordinate

@[simp] lemma norm_hOneEnergyCoordinate
    (f : EuclideanHs 3 1) :
    ‖hOneEnergyCoordinate f‖ = sobolevNorm 1 f.1 f.2 :=
  rfl

/-! ## A.2. Weak sequential compactness of bounded `H¹(ℝ³)` families -/

/-- The complete `H¹(ℝ³)` energy carrier is second countable. The explicit
`p = 2` facts expose Mathlib's separable-`Lᵖ` instance for the Euclidean
Lebesgue measure. -/
noncomputable instance instSecondCountableTopologyEuclideanHOneThree :
    SecondCountableTopology EuclideanHOneThree := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- **Weak sequential compactness with retention of the energy bound.**
Every sequence in continuum `H¹(ℝ³)` bounded by `C` has a weakly convergent
subsequence whose limit is itself in the same closed ball.

The final norm bound is not an added certificate: it is the closed-ball
membership returned by sequential Banach--Alaoglu, transported back through
the Fréchet--Riesz linear isometry. -/
@[zil_level structural]
theorem bounded_hOne_has_weaklyConvergent_subsequence_with_norm_bound
    (u : ℕ → EuclideanHOneThree) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : EuclideanHOneThree, ‖v‖ ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w)) := by
  let F : ℕ → WeakDual ℂ EuclideanHOneThree :=
    fun n => StrongDual.toWeakDual
      (InnerProductSpace.toDual ℂ EuclideanHOneThree (u n))
  have hF : ∀ n,
      F n ∈ WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℂ EuclideanHOneThree) C := by
    intro n
    change dist (WeakDual.toStrongDual (F n)) 0 ≤ C
    rw [dist_zero_right]
    simpa [F] using hu n
  obtain ⟨Flim, hFlim, φ, hφ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall
      (𝕜 := ℂ) (E := EuclideanHOneThree)
      (0 : StrongDual ℂ EuclideanHOneThree) C hF
  let v : EuclideanHOneThree :=
    (InnerProductSpace.toDual ℂ EuclideanHOneThree).symm
      (WeakDual.toStrongDual Flim)
  have hv : ‖v‖ ≤ C := by
    simpa [v, Metric.mem_closedBall, dist_zero] using hFlim
  refine ⟨v, hv, φ, hφ, ?_⟩
  intro w
  have heval :=
    ((WeakDual.eval_continuous (𝕜 := ℂ) w).tendsto Flim).comp hlim
  simpa [F, v, Function.comp_def,
    InnerProductSpace.toDual_symm_apply] using heval

/-- **Weak sequential compactness in continuum `H¹(ℝ³)`.** Every sequence
bounded in the complete Bessel-energy norm admits a subsequence converging
against every `H¹` test vector.

The proof applies the Fréchet--Riesz equivalence to place the sequence in the
weak dual and then uses sequential Banach--Alaoglu. It is an
infinite-dimensional Hilbert-space theorem, not a finite-mode compactness
surrogate. -/
theorem bounded_hOne_has_weaklyConvergent_subsequence
    (u : ℕ → EuclideanHOneThree) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : EuclideanHOneThree, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ w : EuclideanHOneThree,
        Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
          (𝓝 (inner ℂ v w)) := by
  obtain ⟨v, _hv, φ, hφ, hweak⟩ :=
    bounded_hOne_has_weaklyConvergent_subsequence_with_norm_bound u C hu
  exact ⟨v, φ, hφ, hweak⟩

/-- **Hilbert-space compactness closure.** Weak `H¹(ℝ³)` convergence together
with convergence of the complete Bessel-energy norm upgrades to strong
`H¹(ℝ³)` convergence.

This is the infinite-dimensional Radon--Riesz argument:
`‖uₙ-v‖² = ‖uₙ‖² - 2 re⟪uₙ,v⟫ + ‖v‖²`.  It is the exact bridge needed after
concentration compactness supplies preservation of the norm; no finite-mode
surrogate is involved. -/
@[zil_level structural]
theorem hOne_tendsto_of_weak_of_norm
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (hweak : ∀ w : EuclideanHOneThree,
      Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖v‖)) :
    Tendsto u atTop (𝓝 v) := by
  have hinner :
      Tendsto (fun n => (inner ℂ (u n) v).re) atTop
        (𝓝 ((inner ℂ v v).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp (hweak v)
  have hsquare :
      Tendsto (fun n => ‖u n - v‖ ^ 2) atTop (𝓝 0) := by
    convert ((hnorm.pow 2).sub (hinner.const_mul 2)).add_const (‖v‖ ^ 2) using 1
    · funext n
      rw [@norm_sub_sq ℂ EuclideanHOneThree, RCLike.re_eq_complex_re]
    · rw [← RCLike.re_eq_complex_re,
        inner_self_eq_norm_sq (𝕜 := ℂ)]
      ring_nf
  have hsqrt :=
    (Real.continuous_sqrt.tendsto 0).comp hsquare
  have hdist : Tendsto (fun n => dist (u n) v) atTop (𝓝 0) := by
    convert hsqrt using 1
    · funext n
      simp only [Function.comp_apply, dist_eq_norm]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    · simp
  exact tendsto_iff_dist_tendsto_zero.mpr hdist

/-! ## A.3. Tight continuum densities and Prokhorov compactness -/

/-- **Tight probability sequences have convergent subsequences.** For
probability measures on genuine Euclidean three-space, a uniform
concentration/tightness estimate invokes Mathlib's Prokhorov theorem and
produces a subsequence converging in distribution to another probability
measure.

In Schrödinger--Newton applications the measures are the recentered Born
densities.  This theorem proves the compactness consequence of the tightness
estimate; deriving that estimate from the Hartree binding energy is a
separate analytic step. -/
@[zil_level structural]
theorem tight_probabilitySequence_has_convergent_subsequence
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) |
        ν ∈ Set.range μ}) :
    ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have hcompact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨ν, _hν, φ, hφ, hlim⟩ :=
    hcompact.isSeqCompact (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨ν, φ, hφ, by simpa [Function.comp_def] using hlim⟩

/-- **A quantitative moment bound produces continuum tightness.**
If the first radial moments of a sequence of probability measures on
`ℝ³` are bounded by one finite extended real constant, then the whole
sequence is tight.

The proof is the genuine continuum argument: Markov's inequality bounds the
mass outside every ball by `C / R`, and this bound tends uniformly to zero as
the radius grows. Thus applications may discharge Prokhorov tightness by an
explicit localization estimate rather than inserting it as a certificate. -/
@[zil_level structural]
theorem uniform_firstMoment_implies_tight
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ n,
      ∫⁻ x, ENNReal.ofReal ‖x‖
        ∂((μ n : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) ≤ C) :
    IsTightMeasureSet
      {((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) |
        ν ∈ Set.range μ} := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hεtop : ε = ∞
  · subst ε
    exact ⟨0, fun _ _ => le_top⟩
  let C₀ : ℝ≥0 := C.toNNReal
  have hCcoe : (C₀ : ℝ≥0∞) = C := ENNReal.coe_toNNReal hC
  let ε₀ : ℝ≥0 := ε.toNNReal
  have hεcoe : (ε₀ : ℝ≥0∞) = ε := ENNReal.coe_toNNReal hεtop
  have hε0 : ε₀ ≠ 0 := by
    exact ENNReal.coe_ne_zero.mp (hεcoe.trans_ne hε.ne')
  let R : ℝ≥0 := C₀ / ε₀ + 1
  have hR0 : R ≠ 0 := by
    positivity
  have hRtop : (R : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hCR : (C₀ : ℝ≥0∞) / (R : ℝ≥0∞) ≤ ε := by
    rw [ENNReal.div_le_iff_le_mul
      (Or.inl (ENNReal.coe_ne_zero.mpr hR0)) (Or.inl hRtop)]
    rw [← hεcoe]
    exact_mod_cast (show C₀ ≤ ε₀ * R by
      rw [show C₀ = ε₀ * (C₀ / ε₀) by
        exact (mul_div_cancel₀ C₀ hε0).symm]
      simp only [R, mul_add, mul_one]
      exact le_add_of_nonneg_right zero_le)
  refine ⟨(R : ℝ), fun r hr => ?_⟩
  refine iSup₂_le fun ν hν => ?_
  obtain ⟨_ν, ⟨n, rfl⟩, rfl⟩ := hν
  have hmono :
      ((μ n : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) {x | r < ‖x‖} ≤
        ((μ n : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3)))
          {x | (R : ℝ≥0∞) ≤ ENNReal.ofReal ‖x‖} := by
    apply measure_mono
    intro x hx
    simp only [Set.mem_setOf_eq]
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal
      (le_trans (by exact_mod_cast hr) hx.le)
  refine hmono.trans <| (meas_ge_le_lintegral_div ?_
    (ENNReal.coe_ne_zero.mpr hR0) hRtop).trans ?_
  · exact
      (ENNReal.measurable_ofReal.comp continuous_norm.measurable).aemeasurable
  · exact (ENNReal.div_le_div_right
      ((hmoment n).trans_eq hCcoe.symm) (R : ℝ≥0∞)).trans hCR

/-- **Joint continuum concentration compactness.** A sequence uniformly
bounded in the complete `H¹(ℝ³)` energy norm and carrying a tight sequence of
three-dimensional probability measures has one common subsequence on which

* the fields converge weakly in `H¹`, with the limit retaining the energy
  bound, and
* the probability measures converge in distribution.

The proof first applies sequential Banach--Alaoglu, restricts tightness to the
resulting subsequence, applies Prokhorov, and composes the two strictly
monotone selectors.  Thus the field and density limits are not obtained along
unrelated subsequences.  Strong `H¹` convergence still requires the separate
norm-closure premise discharged by `hOne_tendsto_of_weak_of_norm`. -/
@[zil_level structural]
theorem bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence
    (u : ℕ → EuclideanHOneThree) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) |
        ν ∈ Set.range μ}) :
    ∃ v : EuclideanHOneThree, ‖v‖ ≤ C ∧
      ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)),
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          (∀ w : EuclideanHOneThree,
            Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
              (𝓝 (inner ℂ v w))) ∧
          Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨v, hv, φ, hφ, hweak⟩ :=
    bounded_hOne_has_weaklyConvergent_subsequence_with_norm_bound u C hu
  have htightSub : IsTightMeasureSet
      {((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) |
        ν ∈ Set.range (μ ∘ φ)} := by
    apply htight.subset
    rintro _ ⟨ν, ⟨n, rfl⟩, rfl⟩
    exact ⟨μ (φ n), ⟨φ n, rfl⟩, rfl⟩
  obtain ⟨ν, ψ, hψ, hμ⟩ :=
    tight_probabilitySequence_has_convergent_subsequence
      (μ ∘ φ) htightSub
  refine ⟨v, hv, ν, φ ∘ ψ, hφ.comp hψ, ?_, ?_⟩
  · intro w
    simpa [Function.comp_def] using (hweak w).comp hψ.tendsto_atTop
  · simpa [Function.comp_def] using hμ

/-- **Moment-controlled joint continuum concentration compactness.**
A finite uniform first radial moment now discharges the tightness premise of
the joint Banach--Alaoglu/Prokhorov theorem. One common subsequence carries
both weak `H¹(ℝ³)` convergence and probability-measure convergence.

The limiting density is bundled as a `ProbabilityMeasure`, so its total mass
is definitionally retained as one. Identifying it with the Born density of
the weak field limit remains the separate local-compactness step. -/
@[zil_level structural]
theorem bounded_hOne_and_firstMoment_has_joint_subsequence
    (u : ℕ → EuclideanHOneThree) (B : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ B)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ n,
      ∫⁻ x, ENNReal.ofReal ‖x‖
        ∂((μ n : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) ≤ C) :
    ∃ v : EuclideanHOneThree, ‖v‖ ≤ B ∧
      ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)),
        (((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3))) Set.univ = 1) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          (∀ w : EuclideanHOneThree,
            Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
              (𝓝 (inner ℂ v w))) ∧
          Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨v, hv, ν, φ, hφ, hweak, hμ⟩ :=
    bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence
      u B hu μ (uniform_firstMoment_implies_tight μ C hC hmoment)
  exact ⟨v, hv, ν, by simp, φ, hφ, hweak, hμ⟩

/-- **A quantitative concentration-compactness criterion in continuum
`H¹(ℝ³)`.** A closed family is strongly compact when

1. its `H¹` norm is uniformly bounded;
2. an associated continuum probability density has a uniform finite first
   radial moment; and
3. joint weak-field/probability subsequences preserve the `H¹` norm.

The first two hypotheses are converted into a common weak
Banach--Alaoglu/Prokhorov subsequence by
`bounded_hOne_and_firstMoment_has_joint_subsequence`. The third is precisely
the no-loss-of-energy closure step, and the Hilbert Radon--Riesz theorem then
upgrades the selected fields to strong `H¹` convergence. Closedness retains
the limit in the family.

For a translation-invariant variational problem the moment bound is meant to
be applied after recentering. The theorem does not hide that recentering or
the model-specific norm-closure estimate. -/
@[zil_level structural]
theorem isCompact_of_closed_bounded_firstMoment_and_normClosure
    (K : Set EuclideanHOneThree)
    (bornMeasure :
      EuclideanHOneThree →
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (hclosed : IsClosed K)
    (B : ℝ) (hbounded : ∀ u ∈ K, ‖u‖ ≤ B)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ u ∈ K,
      ∫⁻ x, ENNReal.ofReal ‖x‖
        ∂((bornMeasure u :
            ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
          Measure (EuclideanSpace ℝ (Fin 3))) ≤ C)
    (hnormClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n, u n ∈ K) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖)) :
    IsCompact K := by
  rw [isCompact_iff_isSeqCompact]
  intro u hu
  obtain ⟨v, _hv, _ν, _hνmass, φ, hφ, hweak, _hmeasure⟩ :=
    bounded_hOne_and_firstMoment_has_joint_subsequence
      u B (fun n => hbounded (u n) (hu n))
      (bornMeasure ∘ u) C hC (fun n => by
        simpa [Function.comp_def] using hmoment (u n) (hu n))
  have hstrong : Tendsto (u ∘ φ) atTop (𝓝 v) := by
    apply hOne_tendsto_of_weak_of_norm
    · simpa [Function.comp_def] using hweak
    · simpa [Function.comp_def] using
        hnormClosure u v φ hu hφ hweak
  have hvK : v ∈ K :=
    hclosed.mem_of_tendsto hstrong
      (Filter.Eventually.of_forall fun n => hu (φ n))
  exact ⟨v, hvK, φ, hφ, hstrong⟩

/-! ### A.3.1. The actual normalized `H¹` Born law

The compactness statements above accept an associated probability measure
because they are useful beyond quantum-mechanical applications.  This
section now constructs the canonical measure in the application of interest:
the squared modulus of the physical-space `L²` representative reconstructed
from the complete Bessel-energy `H¹` coordinate.

The main closure theorem is quantitative.  Strong convergence in the
complete `H¹` carrier contracts to strong physical-space `L²` convergence,
and

`∫ | |ψₙ|² - |ψ|² | ≤ ‖ψₙ - ψ‖₂ (‖ψₙ‖₂ + ‖ψ‖₂)`.

Consequently normalized Born laws converge weakly.  Combined with the
no-loss-of-energy premise already used above, this identifies the
Prokhorov limit with the Born law of the limiting field; it is no longer an
unrelated probability-measure adapter.
-/

/-- The inverse Bessel multiplier is linear with respect to subtraction. -/
lemma inverseBesselOneMultiplier_sub
    (u v : EuclideanHOneThree) :
    inverseBesselOneMultiplier (u - v) =
      inverseBesselOneMultiplier u - inverseBesselOneMultiplier v := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    inverseBesselOneMultiplier_coeFn (u - v),
    inverseBesselOneMultiplier_coeFn u,
    inverseBesselOneMultiplier_coeFn v,
    Lp.coeFn_sub u v,
    Lp.coeFn_sub (inverseBesselOneMultiplier u)
      (inverseBesselOneMultiplier v)
  ] with x huv hu hv hsub hsubOut
  rw [huv, hsubOut, Pi.sub_apply, hu, hv, inverseBesselOneWeighted,
    inverseBesselOneWeighted, inverseBesselOneWeighted, hsub, Pi.sub_apply]
  ring

/-- Division by the Bessel weight contracts the native `L²` norm. -/
lemma norm_inverseBesselOneMultiplier_le
    (u : EuclideanHOneThree) :
    ‖inverseBesselOneMultiplier u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
  apply eLpNorm_mono_ae
  filter_upwards [inverseBesselOneMultiplier_coeFn u] with x hx
  rw [hx, inverseBesselOneWeighted, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (besselPotentialWeight_pos 1 x)]
  exact mul_le_of_le_one_left (norm_nonneg (u x))
    (inv_le_one_of_one_le₀ (one_le_besselPotentialWeight_one x))

/-- Physical-space `H¹` reconstruction is linear under subtraction. -/
lemma hOneRepresentative_sub
    (u v : EuclideanHOneThree) :
    hOneRepresentative (u - v) =
      hOneRepresentative u - hOneRepresentative v := by
  rw [hOneRepresentative, inverseBesselOneMultiplier_sub]
  exact map_sub (FourierTransform.fourierInvCLM ℂ (EuclideanL2 3)) _ _

/-- Physical-space reconstruction is an `L²` contraction of the complete
`H¹` Bessel-energy coordinate. -/
lemma norm_hOneRepresentative_le
    (u : EuclideanHOneThree) :
    ‖hOneRepresentative u‖ ≤ ‖u‖ := by
  change
    ‖(Lp.fourierTransformₗᵢ
      (EuclideanSpace ℝ (Fin 3)) ℂ).symm
        (inverseBesselOneMultiplier u)‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  exact norm_inverseBesselOneMultiplier_le u

/-- The reconstruction map is one-Lipschitz. -/
lemma dist_hOneRepresentative_le
    (u v : EuclideanHOneThree) :
    dist (hOneRepresentative u) (hOneRepresentative v) ≤ dist u v := by
  simp only [dist_eq_norm, ← hOneRepresentative_sub]
  exact norm_hOneRepresentative_le (u - v)

private lemma integral_norm_sq_euclideanL2
    (f : EuclideanL2 3) :
    ∫ x, ‖f x‖ ^ 2 ∂volume = ‖f‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [inner_self_eq_norm_sq]

private lemma integrable_norm_sq_euclideanL2
    (f : EuclideanL2 3) :
    Integrable (fun x => ‖f x‖ ^ 2) volume :=
  (Lp.memLp f).integrable_norm_pow two_ne_zero

private lemma abs_norm_sq_sub_norm_sq_le
    (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤
      ‖a - b‖ * ‖a‖ + ‖a - b‖ * ‖b‖ := by
  calc
    |‖a‖ ^ 2 - ‖b‖ ^ 2| =
        |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) := by
      rw [sq_sub_sq, abs_mul,
        abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
      ring
    _ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b) (by positivity)
    _ = ‖a - b‖ * ‖a‖ + ‖a - b‖ * ‖b‖ := by ring

private lemma memLp_pointwise_sub
    (f g : EuclideanL2 3) :
    MemLp (fun x => f x - g x) 2 volume :=
  (Lp.memLp (f - g)).ae_eq (Lp.coeFn_sub f g)

private lemma integrable_density_sub
    (f g : EuclideanL2 3) :
    Integrable (fun x => ‖f x‖ ^ 2 - ‖g x‖ ^ 2) volume :=
  (integrable_norm_sq_euclideanL2 f).sub
    (integrable_norm_sq_euclideanL2 g)

private lemma integrable_norm_sub_mul_norm_left
    (f g : EuclideanL2 3) :
    Integrable (fun x => ‖f x - g x‖ * ‖f x‖) volume :=
  (memLp_pointwise_sub f g).norm.integrable_mul (Lp.memLp f).norm

private lemma integrable_norm_sub_mul_norm_right
    (f g : EuclideanL2 3) :
    Integrable (fun x => ‖f x - g x‖ * ‖g x‖) volume :=
  (memLp_pointwise_sub f g).norm.integrable_mul (Lp.memLp g).norm

private lemma integral_norm_pointwise_sub_sq_eq
    (f g : EuclideanL2 3) :
    ∫ x, ‖f x - g x‖ ^ 2 ∂volume = ‖f - g‖ ^ 2 := by
  rw [← integral_norm_sq_euclideanL2 (f - g)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  have hx' : (f - g) x = f x - g x := by
    simpa [Pi.sub_apply] using hx
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hx'.symm

private lemma integral_norm_sub_mul_norm_le
    (f g h : EuclideanL2 3) :
    ∫ x, ‖f x - g x‖ * ‖h x‖ ∂volume ≤
      ‖f - g‖ * ‖h‖ := by
  have hsub :
      MemLp (fun x => f x - g x) (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using memLp_pointwise_sub f g
  have hh : MemLp (fun x => h x) (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using Lp.memLp h
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume) (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hsub hh
  have hdiffSq :
      ∫ x, ‖f x - g x‖ ^ (2 : ℝ) ∂volume = ‖f - g‖ ^ 2 := by
    simpa only [Real.rpow_two] using
      integral_norm_pointwise_sub_sq_eq f g
  have hhSq :
      ∫ x, ‖h x‖ ^ (2 : ℝ) ∂volume = ‖h‖ ^ 2 := by
    simpa only [Real.rpow_two] using integral_norm_sq_euclideanL2 h
  rw [hdiffSq, hhSq] at hholder
  have hrootDiff :
      (‖f - g‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) = ‖f - g‖ := by
    convert Real.pow_rpow_inv_natCast (norm_nonneg (f - g))
      (by norm_num : (2 : ℕ) ≠ 0) using 1
    all_goals norm_num
  have hrootH :
      (‖h‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) = ‖h‖ := by
    convert Real.pow_rpow_inv_natCast (norm_nonneg h)
      (by norm_num : (2 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rwa [hrootDiff, hrootH] at hholder

private lemma integral_abs_density_sub_le
    (f g : EuclideanL2 3) :
    ∫ x, |‖f x‖ ^ 2 - ‖g x‖ ^ 2| ∂volume ≤
      ‖f - g‖ * (‖f‖ + ‖g‖) := by
  calc
    ∫ x, |‖f x‖ ^ 2 - ‖g x‖ ^ 2| ∂volume ≤
        ∫ x, (‖f x - g x‖ * ‖f x‖ +
          ‖f x - g x‖ * ‖g x‖) ∂volume := by
      apply integral_mono
      · exact (integrable_density_sub f g).abs
      · exact (integrable_norm_sub_mul_norm_left f g).add
          (integrable_norm_sub_mul_norm_right f g)
      · intro x
        exact abs_norm_sq_sub_norm_sq_le (f x) (g x)
    _ = (∫ x, ‖f x - g x‖ * ‖f x‖ ∂volume) +
        (∫ x, ‖f x - g x‖ * ‖g x‖ ∂volume) := by
      rw [integral_add
        (integrable_norm_sub_mul_norm_left f g)
        (integrable_norm_sub_mul_norm_right f g)]
    _ ≤ ‖f - g‖ * ‖f‖ + ‖f - g‖ * ‖g‖ :=
      add_le_add
        (integral_norm_sub_mul_norm_le f g f)
        (integral_norm_sub_mul_norm_le f g g)
    _ = ‖f - g‖ * (‖f‖ + ‖g‖) := by ring

/-- The actual extended-real Born density of a complete `H¹(ℝ³)` energy
coordinate, evaluated on its reconstructed physical-space field. -/
noncomputable def hOneBornDensity
    (u : EuclideanHOneThree)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖hOneRepresentative u x‖ ^ 2)

lemma hOneBornDensity_aemeasurable
    (u : EuclideanHOneThree) :
    AEMeasurable (hOneBornDensity u) volume := by
  exact
    (((Lp.aestronglyMeasurable (hOneRepresentative u)).norm.aemeasurable
      |>.pow_const 2).ennreal_ofReal)

lemma hOneBornDensity_eq_enorm_sq
    (u : EuclideanHOneThree)
    (x : EuclideanSpace ℝ (Fin 3)) :
    hOneBornDensity u x =
      ‖hOneRepresentative u x‖ₑ ^ (2 : ℝ) := by
  simp [hOneBornDensity, ENNReal.ofReal_pow]

/-- The total Born mass is exactly the square of the physical-space
`L²` extended norm. -/
@[zil_level structural]
lemma hOneBornDensity_lintegral_eq_enorm_sq
    (u : EuclideanHOneThree) :
    ∫⁻ x, hOneBornDensity u x ∂volume =
      ‖hOneRepresentative u‖ₑ ^ (2 : ℝ) := by
  rw [Lp.enorm_def]
  change
    (∫⁻ x, hOneBornDensity u x ∂volume) =
      eLpNorm (fun x => hOneRepresentative u x)
        ((2 : ℝ≥0) : ℝ≥0∞) volume ^ ((2 : ℝ≥0) : ℝ)
  have hpow := eLpNorm_nnreal_pow_eq_lintegral
    (μ := volume) (f := fun x => hOneRepresentative u x)
    (p := (2 : ℝ≥0)) (show (2 : ℝ≥0) ≠ 0 by norm_num)
  rw [hpow]
  apply lintegral_congr
  intro x
  simpa using hOneBornDensity_eq_enorm_sq u x

/-- Unit physical-space `L²` mass of a complete Bessel-energy `H¹`
coordinate. -/
def HOneLTwoNormalized (u : EuclideanHOneThree) : Prop :=
  ∫⁻ x, hOneBornDensity u x ∂volume = 1

lemma hOneLTwoNormalized_iff_norm_representative_eq_one
    (u : EuclideanHOneThree) :
    HOneLTwoNormalized u ↔ ‖hOneRepresentative u‖ = 1 := by
  rw [HOneLTwoNormalized, hOneBornDensity_lintegral_eq_enorm_sq]
  constructor
  · intro h
    have henorm : ‖hOneRepresentative u‖ₑ = 1 := by
      apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
      simpa using h
    rw [Lp.norm_def, ← Lp.enorm_def, henorm]
    simp
  · intro h
    have henorm : ‖hOneRepresentative u‖ₑ = 1 := by
      apply (ENNReal.toReal_eq_one_iff _).mp
      simpa [Lp.norm_def, Lp.enorm_def] using h
    rw [henorm]
    simp

/-- Unit physical-space `L²` mass is a closed condition on the complete
`H¹` energy carrier. -/
lemma isClosed_hOneLTwoNormalized :
    IsClosed {u : EuclideanHOneThree | HOneLTwoNormalized u} := by
  have hlip : LipschitzWith (1 : ℝ≥0) hOneRepresentative :=
    LipschitzWith.of_dist_le_mul (K := (1 : ℝ≥0)) fun u v => by
      simpa using dist_hOneRepresentative_le u v
  have hset :
      {u : EuclideanHOneThree | HOneLTwoNormalized u} =
        {u : EuclideanHOneThree | ‖hOneRepresentative u‖ = 1} := by
    ext u
    exact hOneLTwoNormalized_iff_norm_representative_eq_one u
  rw [hset]
  exact isClosed_eq
    (continuous_norm.comp hlip.continuous) continuous_const

/-- Strong `H¹` limits of physically normalized fields remain normalized. -/
lemma hOneLTwoNormalized_of_tendsto
    {u : ℕ → EuclideanHOneThree} {v : EuclideanHOneThree}
    (hu : ∀ n, HOneLTwoNormalized (u n))
    (hlim : Tendsto u atTop (𝓝 v)) :
    HOneLTwoNormalized v :=
  isClosed_hOneLTwoNormalized.mem_of_tendsto hlim
    (Filter.Eventually.of_forall hu)

/-- Real-valued version of the `H¹` Born density, used for Bochner `L¹`
estimates and bounded-observable integrals. -/
noncomputable def hOneBornDensityReal
    (u : EuclideanHOneThree)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖hOneRepresentative u x‖ ^ 2

lemma hOneBornDensity_toReal
    (u : EuclideanHOneThree)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (hOneBornDensity u x).toReal = hOneBornDensityReal u x := by
  simp [hOneBornDensity, hOneBornDensityReal]

lemma integrable_hOneBornDensityReal
    (u : EuclideanHOneThree) :
    Integrable (hOneBornDensityReal u) volume :=
  integrable_norm_sq_euclideanL2 (hOneRepresentative u)

/-- Quantitative `L¹` stability of the actual Born density. -/
lemma integral_abs_hOneBornDensityReal_sub_le
    (u v : EuclideanHOneThree) :
    ∫ x, |hOneBornDensityReal u x -
        hOneBornDensityReal v x| ∂volume ≤
      ‖hOneRepresentative u - hOneRepresentative v‖ *
        (‖hOneRepresentative u‖ + ‖hOneRepresentative v‖) :=
  integral_abs_density_sub_le
    (hOneRepresentative u) (hOneRepresentative v)

/-- Strong convergence in the complete continuum `H¹` carrier implies
`L¹` convergence of the corresponding squared-amplitude densities. -/
theorem hOneBornDensityReal_tendsto_L1
    {u : ℕ → EuclideanHOneThree} {v : EuclideanHOneThree}
    (hlim : Tendsto u atTop (𝓝 v)) :
    Tendsto
      (fun n =>
        ∫ x, |hOneBornDensityReal (u n) x -
          hOneBornDensityReal v x| ∂volume)
      atTop (𝓝 0) := by
  have hlip : LipschitzWith (1 : ℝ≥0) hOneRepresentative :=
    LipschitzWith.of_dist_le_mul (K := (1 : ℝ≥0)) fun a b => by
      simpa using dist_hOneRepresentative_le a b
  have hrep :
      Tendsto (fun n => hOneRepresentative (u n)) atTop
        (𝓝 (hOneRepresentative v)) := by
    simpa [Function.comp_def] using
      (hlip.continuous.tendsto v).comp hlim
  have hdiff :
      Tendsto
        (fun n => ‖hOneRepresentative (u n) - hOneRepresentative v‖)
        atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hrep
  have hsum :
      Tendsto
        (fun n => ‖hOneRepresentative (u n)‖ + ‖hOneRepresentative v‖)
        atTop
        (𝓝 (‖hOneRepresentative v‖ + ‖hOneRepresentative v‖)) :=
    hrep.norm.add_const _
  have hupper :
      Tendsto
        (fun n =>
          ‖hOneRepresentative (u n) - hOneRepresentative v‖ *
            (‖hOneRepresentative (u n)‖ + ‖hOneRepresentative v‖))
        atTop (𝓝 0) := by
    simpa only [zero_mul] using hdiff.mul hsum
  exact squeeze_zero
    (fun n => integral_nonneg fun x =>
      abs_nonneg (hOneBornDensityReal (u n) x -
        hOneBornDensityReal v x))
    (fun n => integral_abs_hOneBornDensityReal_sub_le (u n) v)
    hupper

/-- The measure with Radon--Nikodym density `|ψ|²` relative to Lebesgue
volume. -/
noncomputable def hOneBornMeasure
    (u : EuclideanHOneThree) :
    Measure (EuclideanSpace ℝ (Fin 3)) :=
  volume.withDensity (hOneBornDensity u)

/-- The genuine probability law of a normalized continuum `H¹` field. -/
noncomputable def hOneBornProbability
    (u : EuclideanHOneThree) (hu : HOneLTwoNormalized u) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
  ⟨hOneBornMeasure u, ⟨by
    rw [hOneBornMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact hu⟩⟩

@[simp] lemma hOneBornProbability_toMeasure
    (u : EuclideanHOneThree) (hu : HOneLTwoNormalized u) :
    ((hOneBornProbability u hu :
      ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
        Measure (EuclideanSpace ℝ (Fin 3))) = hOneBornMeasure u :=
  rfl

/-- A bounded continuous Born observable is its usual density-weighted
Lebesgue integral. -/
lemma integral_hOneBornProbability_eq
    (u : EuclideanHOneThree) (hu : HOneLTwoNormalized u)
    (F : BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin 3)) ℝ) :
    ∫ x, F x
        ∂((hOneBornProbability u hu :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3))) =
      ∫ x, hOneBornDensityReal u x * F x ∂volume := by
  rw [hOneBornProbability_toMeasure, hOneBornMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      (hOneBornDensity_aemeasurable u)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [hOneBornDensity_toReal, smul_eq_mul]

private lemma integrable_hOneBornDensityReal_mul_bounded
    (u : EuclideanHOneThree)
    (F : BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin 3)) ℝ) :
    Integrable (fun x => hOneBornDensityReal u x * F x) volume :=
  (integrable_hOneBornDensityReal u).mul_bdd
    F.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => F.norm_coe_le_norm x)

/-- Quantitative control of every bounded continuous observable by the
`L¹` distance between two Born densities. -/
lemma abs_hOneBornObservable_sub_le
    (u v : EuclideanHOneThree)
    (hu : HOneLTwoNormalized u) (hv : HOneLTwoNormalized v)
    (F : BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin 3)) ℝ) :
    |(∫ x, F x
        ∂((hOneBornProbability u hu :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3)))) -
      (∫ x, F x
        ∂((hOneBornProbability v hv :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3))))| ≤
      ‖F‖ * ∫ x,
        |hOneBornDensityReal u x -
          hOneBornDensityReal v x| ∂volume := by
  rw [integral_hOneBornProbability_eq,
    integral_hOneBornProbability_eq]
  have hdiff :
      Integrable
        (fun x => hOneBornDensityReal u x -
          hOneBornDensityReal v x) volume :=
    (integrable_hOneBornDensityReal u).sub
      (integrable_hOneBornDensityReal v)
  have hmul :
      Integrable
        (fun x => (hOneBornDensityReal u x -
          hOneBornDensityReal v x) * F x) volume :=
    hdiff.mul_bdd F.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => F.norm_coe_le_norm x)
  rw [← integral_sub
    (integrable_hOneBornDensityReal_mul_bounded u F)
    (integrable_hOneBornDensityReal_mul_bounded v F)]
  have heq :
      (fun x => hOneBornDensityReal u x * F x -
        hOneBornDensityReal v x * F x) =
      (fun x => (hOneBornDensityReal u x -
        hOneBornDensityReal v x) * F x) := by
    funext x
    ring
  rw [heq]
  calc
    |∫ x, (hOneBornDensityReal u x -
        hOneBornDensityReal v x) * F x ∂volume| ≤
        ∫ x, |(hOneBornDensityReal u x -
          hOneBornDensityReal v x) * F x| ∂volume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖F‖ *
        |hOneBornDensityReal u x -
          hOneBornDensityReal v x| ∂volume := by
      apply integral_mono
      · exact hmul.abs
      · exact hdiff.abs.const_mul ‖F‖
      · intro x
        change
          |(hOneBornDensityReal u x -
            hOneBornDensityReal v x) * F x| ≤
            ‖F‖ * |hOneBornDensityReal u x -
              hOneBornDensityReal v x|
        rw [abs_mul]
        simpa only [mul_comm, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left
            (F.norm_coe_le_norm x)
            (abs_nonneg
              (hOneBornDensityReal u x - hOneBornDensityReal v x))
    _ = ‖F‖ * ∫ x,
        |hOneBornDensityReal u x -
          hOneBornDensityReal v x| ∂volume := by
      rw [integral_const_mul]

/-- Strong convergence of normalized `H¹` states implies weak convergence
of their actual continuum Born probability measures. -/
@[zil_level structural]
theorem hOneBornProbability_tendsto_of_strong
    {u : ℕ → EuclideanHOneThree} {v : EuclideanHOneThree}
    (hu : ∀ n, HOneLTwoNormalized (u n))
    (hv : HOneLTwoNormalized v)
    (hlim : Tendsto u atTop (𝓝 v)) :
    Tendsto
      (fun n => hOneBornProbability (u n) (hu n))
      atTop (𝓝 (hOneBornProbability v hv)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hL1 := hOneBornDensityReal_tendsto_L1 hlim
  have hupper :
      Tendsto
        (fun n => ‖F‖ *
          ∫ x, |hOneBornDensityReal (u n) x -
            hOneBornDensityReal v x| ∂volume)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hL1
  exact squeeze_zero
    (fun n => norm_nonneg
      ((∫ x, F x
        ∂((hOneBornProbability (u n) (hu n) :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3)))) -
       (∫ x, F x
        ∂((hOneBornProbability v hv :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3))))))
    (fun n => by
      simpa only [Real.norm_eq_abs] using
        abs_hOneBornObservable_sub_le (u n) v (hu n) hv F)
    hupper

/-- The first radial moment of the Born probability is the Lebesgue
integral of `|x| |ψ(x)|²`. -/
lemma hOneBornProbability_firstMoment
    (u : EuclideanHOneThree) (hu : HOneLTwoNormalized u) :
    ∫⁻ x, ENNReal.ofReal ‖x‖
        ∂((hOneBornProbability u hu :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3))) =
      ∫⁻ x, hOneBornDensity u x * ENNReal.ofReal ‖x‖ ∂volume := by
  rw [hOneBornProbability_toMeasure, hOneBornMeasure]
  simpa [Function.comp_def] using
    (lintegral_withDensity_eq_lintegral_mul₀
      (hOneBornDensity_aemeasurable u)
      (ENNReal.measurable_ofReal.comp continuous_norm.measurable).aemeasurable)

/-- `H¹` boundedness, physical normalization, and a finite first moment
produce one subsequence carrying weak field convergence and weak convergence
of the corresponding actual Born laws. -/
theorem bounded_normalized_hOne_firstMoment_has_joint_subsequence
    (u : ℕ → EuclideanHOneThree) (B : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ B)
    (hnormalized : ∀ n, HOneLTwoNormalized (u n))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ n,
      ∫⁻ x, hOneBornDensity (u n) x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C) :
    ∃ v : EuclideanHOneThree, ‖v‖ ≤ B ∧
      ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)),
        (((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) :
            Measure (EuclideanSpace ℝ (Fin 3))) Set.univ = 1) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          (∀ w : EuclideanHOneThree,
            Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
              (𝓝 (inner ℂ v w))) ∧
          Tendsto
            (fun n => hOneBornProbability (u (φ n))
              (hnormalized (φ n)))
            atTop (𝓝 ν) := by
  let μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
    fun n => hOneBornProbability (u n) (hnormalized n)
  obtain ⟨v, hv, ν, hνmass, φ, hφ, hweak, hμ⟩ :=
    bounded_hOne_and_firstMoment_has_joint_subsequence
      u B hu μ C hC (fun n => by
        rw [hOneBornProbability_firstMoment]
        exact hmoment n)
  refine ⟨v, hv, ν, hνmass, φ, hφ, hweak, ?_⟩
  change Tendsto (μ ∘ φ) atTop (𝓝 ν)
  exact hμ

/-- **Actual Born-limit concentration compactness.**  Under the explicit
no-loss-of-`H¹`-norm premise, the joint weak-field/Prokhorov subsequence is
strong in `H¹`; normalization closes, and the probability limit is exactly
the Born law of the limiting physical-space field.

The finite first moment is still an explicit, model-specific localization
premise (normally after recentering), and the norm-closure premise is not
claimed to follow from boundedness alone. -/
@[zil_level structural]
theorem bounded_normalized_hOne_firstMoment_has_bornLimit
    (u : ℕ → EuclideanHOneThree) (B : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ B)
    (hnormalized : ∀ n, HOneLTwoNormalized (u n))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ n,
      ∫⁻ x, hOneBornDensity (u n) x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (hnormClosure :
      ∀ (v : EuclideanHOneThree) (φ : ℕ → ℕ),
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖)) :
    ∃ v : EuclideanHOneThree, ‖v‖ ≤ B ∧
      ∃ hvNormalized : HOneLTwoNormalized v,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (u ∘ φ) atTop (𝓝 v) ∧
          Tendsto
            (fun n => hOneBornProbability (u (φ n))
              (hnormalized (φ n)))
            atTop (𝓝 (hOneBornProbability v hvNormalized)) := by
  obtain ⟨v, hv, _ν, _hνmass, φ, hφ, hweak, _hμ⟩ :=
    bounded_normalized_hOne_firstMoment_has_joint_subsequence
      u B hu hnormalized C hC hmoment
  have hstrong : Tendsto (u ∘ φ) atTop (𝓝 v) := by
    apply hOne_tendsto_of_weak_of_norm
    · simpa [Function.comp_def] using hweak
    · simpa [Function.comp_def] using hnormClosure v φ hφ hweak
  have hvNormalized : HOneLTwoNormalized v :=
    hOneLTwoNormalized_of_tendsto
      (fun n => hnormalized (φ n)) hstrong
  have hborn :
      Tendsto
        (fun n => hOneBornProbability (u (φ n))
          (hnormalized (φ n)))
        atTop (𝓝 (hOneBornProbability v hvNormalized)) := by
    have hb := hOneBornProbability_tendsto_of_strong
      (u := u ∘ φ) (v := v)
      (fun n => hnormalized (φ n)) hvNormalized hstrong
    simpa [Function.comp_def] using hb
  exact ⟨v, hv, hvNormalized, φ, hφ, hstrong, hborn⟩

/-- **Strong compactness from the actual `H¹` Born density.**  This is the
specialized direct compactness criterion needed by normalized continuum
Schrödinger variational problems.  Unlike
`isCompact_of_closed_bounded_firstMoment_and_normClosure`, it does not take
an arbitrary measure-valued adapter: normalization, the moment, and the
limiting probability measure all come from `|hOneRepresentative u|²`. -/
@[zil_level structural]
theorem isCompact_of_closed_bounded_hOneBornMoment_and_normClosure
    (K : Set EuclideanHOneThree)
    (hclosed : IsClosed K)
    (B : ℝ) (hbounded : ∀ u ∈ K, ‖u‖ ≤ B)
    (hnormalized : ∀ u ∈ K, HOneLTwoNormalized u)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ u ∈ K,
      ∫⁻ x, hOneBornDensity u x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (hnormClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n, u n ∈ K) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => ‖u (φ n)‖) atTop (𝓝 ‖v‖)) :
    IsCompact K := by
  rw [isCompact_iff_isSeqCompact]
  intro u hu
  obtain ⟨v, _hv, _hvNormalized, φ, hφ, hstrong, _hborn⟩ :=
    bounded_normalized_hOne_firstMoment_has_bornLimit
      u B (fun n => hbounded (u n) (hu n))
      (fun n => hnormalized (u n) (hu n))
      C hC (fun n => hmoment (u n) (hu n))
      (fun v φ hφ hweak =>
        hnormClosure u v φ hu hφ hweak)
  have hvK : v ∈ K :=
    hclosed.mem_of_tendsto hstrong
      (Filter.Eventually.of_forall fun n => hu (φ n))
  exact ⟨v, hvK, φ, hφ, hstrong⟩

/-! ### A.3.2. No-loss closure from an energy split

For variational Hartree problems, convergence of the `H¹` norm should not be
an opaque extra certificate.  The standard direct-method mechanism is:

* weak `H¹` convergence makes the norm lower semicontinuous;
* the minimizing energy converges;
* the nonlinear interaction converges along the localized subsequence; and
* the energy is a positive quadratic kinetic term plus that interaction.

These facts force equality in weak lower semicontinuity and hence strong
`H¹` convergence.  The results below formalize that mechanism without
claiming interaction convergence for an arbitrary kernel.
-/

/-- Weak Hilbert convergence is lower semicontinuous for the norm whenever
the sequence of norms has a limit.  The proof tests weak convergence against
the limit vector and passes Cauchy--Schwarz to the scalar limit. -/
lemma hOne_norm_le_of_weak_of_norm_tendsto
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree) (L : ℝ)
    (hweak : ∀ w : EuclideanHOneThree,
      Tendsto (fun n => inner ℂ (u n) w) atTop
        (𝓝 (inner ℂ v w)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 L)) :
    ‖v‖ ≤ L := by
  have hinner :
      Tendsto (fun n => (inner ℂ (u n) v).re) atTop
        (𝓝 ((inner ℂ v v).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp (hweak v)
  have hproduct :
      Tendsto (fun n => ‖u n‖ * ‖v‖) atTop (𝓝 (L * ‖v‖)) :=
    hnorm.mul_const ‖v‖
  have hlimit :
      (inner ℂ v v).re ≤ L * ‖v‖ :=
    le_of_tendsto_of_tendsto' hinner hproduct fun n => by
      simpa [RCLike.re_eq_complex_re] using
        (re_inner_le_norm (𝕜 := ℂ) (u n) v)
  rw [← RCLike.re_eq_complex_re,
    inner_self_eq_norm_sq (𝕜 := ℂ)] at hlimit
  by_cases hv : ‖v‖ = 0
  · rw [hv]
    exact ge_of_tendsto hnorm
      (Filter.Eventually.of_forall fun n => norm_nonneg (u n))
  · have hvpos : 0 < ‖v‖ :=
      lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    nlinarith

/-- **Energy-split no-loss theorem.**  Suppose a weakly convergent
minimizing sequence has energy

`E(u) = a ‖u‖² + W(u)`, with `a > 0`,

and the interaction `W` converges along the weak subsequence.  If the weak
limit is admissible, so its energy is at least the variational level, then
it attains that level and the complete `H¹` norms converge. -/
@[zil_level structural]
theorem hOne_energy_eq_and_norm_tendsto_of_minimizing_energySplit
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (energy interaction : EuclideanHOneThree → ℝ)
    (kineticWeight level : ℝ) (hkinetic : 0 < kineticWeight)
    (hweak : ∀ w : EuclideanHOneThree,
      Tendsto (fun n => inner ℂ (u n) w) atTop
        (𝓝 (inner ℂ v w)))
    (hsplit_u : ∀ n,
      energy (u n) =
        kineticWeight * ‖u n‖ ^ 2 + interaction (u n))
    (hsplit_v :
      energy v = kineticWeight * ‖v‖ ^ 2 + interaction v)
    (henergy : Tendsto (fun n => energy (u n)) atTop (𝓝 level))
    (hinteraction :
      Tendsto (fun n => interaction (u n)) atTop
        (𝓝 (interaction v)))
    (hlower : level ≤ energy v) :
    energy v = level ∧
      Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖v‖) := by
  have hkinetic_ne : kineticWeight ≠ 0 := ne_of_gt hkinetic
  have hscaled :
      Tendsto (fun n => kineticWeight * ‖u n‖ ^ 2) atTop
        (𝓝 (level - interaction v)) := by
    convert henergy.sub hinteraction using 1
    funext n
    rw [hsplit_u n]
    ring
  have hsquares :
      Tendsto (fun n => ‖u n‖ ^ 2) atTop
        (𝓝 ((level - interaction v) / kineticWeight)) := by
    simpa [hkinetic_ne] using hscaled.div_const kineticWeight
  let q : ℝ := (level - interaction v) / kineticWeight
  have hq : 0 ≤ q := by
    apply ge_of_tendsto
      (show Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 q) by
        simpa [q] using hsquares)
    exact Filter.Eventually.of_forall fun n => sq_nonneg ‖u n‖
  have hnorm_q :
      Tendsto (fun n => ‖u n‖) atTop (𝓝 (Real.sqrt q)) := by
    have hsqrt :=
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (show Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 q) by
          simpa [q] using hsquares)
    convert hsqrt using 1
    funext n
    simp only [Function.comp_apply, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg (u n))]
  have hvle : ‖v‖ ≤ Real.sqrt q :=
    hOne_norm_le_of_weak_of_norm_tendsto u v (Real.sqrt q)
      hweak hnorm_q
  have hsqrt_sq : (Real.sqrt q) ^ 2 = q :=
    Real.sq_sqrt hq
  have hnorm_sq_le : ‖v‖ ^ 2 ≤ q := by
    nlinarith [norm_nonneg v, Real.sqrt_nonneg q]
  have hqeq :
      kineticWeight * q = level - interaction v := by
    dsimp [q]
    field_simp
  have hupper : energy v ≤ level := by
    rw [hsplit_v]
    nlinarith
  have heq : energy v = level :=
    le_antisymm hupper hlower
  have hqnorm : q = ‖v‖ ^ 2 := by
    rw [hsplit_v] at heq
    nlinarith
  rw [hqnorm, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg v)] at hnorm_q
  exact ⟨heq, hnorm_q⟩

/-- The energy-split no-loss theorem followed by the Hilbert
Radon--Riesz argument yields strong convergence in the complete continuum
`H¹` carrier. -/
@[zil_level structural]
theorem hOne_tendsto_of_minimizing_energySplit
    (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
    (energy interaction : EuclideanHOneThree → ℝ)
    (kineticWeight level : ℝ) (hkinetic : 0 < kineticWeight)
    (hweak : ∀ w : EuclideanHOneThree,
      Tendsto (fun n => inner ℂ (u n) w) atTop
        (𝓝 (inner ℂ v w)))
    (hsplit_u : ∀ n,
      energy (u n) =
        kineticWeight * ‖u n‖ ^ 2 + interaction (u n))
    (hsplit_v :
      energy v = kineticWeight * ‖v‖ ^ 2 + interaction v)
    (henergy : Tendsto (fun n => energy (u n)) atTop (𝓝 level))
    (hinteraction :
      Tendsto (fun n => interaction (u n)) atTop
        (𝓝 (interaction v)))
    (hlower : level ≤ energy v) :
    energy v = level ∧ Tendsto u atTop (𝓝 v) := by
  obtain ⟨heq, hnorm⟩ :=
    hOne_energy_eq_and_norm_tendsto_of_minimizing_energySplit
      u v energy interaction kineticWeight level hkinetic hweak
      hsplit_u hsplit_v henergy hinteraction hlower
  exact ⟨heq, hOne_tendsto_of_weak_of_norm u v hweak hnorm⟩

/-- **Born-law direct method with derived no-loss.**  A bounded,
physically normalized minimizing sequence with a finite first Born moment
has a strongly convergent subsequence and an attained minimizer when:

* the admissible constraint is sequentially weakly closed;
* the energy has a positive quadratic `H¹` kinetic term;
* the interaction converges along the selected weak subsequence; and
* the limiting variational level is a lower bound on the admissible set.

The former no-loss-of-`H¹`-norm premise is a conclusion.  Strong convergence
then identifies the limiting probability measure with the actual Born law
of the minimizer. -/
@[zil_level structural]
theorem bounded_normalized_hOne_firstMoment_has_energyMinimizer
    (u : ℕ → EuclideanHOneThree) (B : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ B)
    (hnormalized : ∀ n, HOneLTwoNormalized (u n))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ n,
      ∫⁻ x, hOneBornDensity (u n) x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (admissible : Set EuclideanHOneThree)
    (energy interaction : EuclideanHOneThree → ℝ)
    (kineticWeight level : ℝ) (hkinetic : 0 < kineticWeight)
    (hu_admissible : ∀ n, u n ∈ admissible)
    (hweakClosed :
      ∀ (v : EuclideanHOneThree) (φ : ℕ → ℕ),
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        v ∈ admissible)
    (hsplit : ∀ z ∈ admissible,
      energy z = kineticWeight * ‖z‖ ^ 2 + interaction z)
    (henergy : Tendsto (fun n => energy (u n)) atTop (𝓝 level))
    (hlower : ∀ z ∈ admissible, level ≤ energy z)
    (hinteractionClosure :
      ∀ (v : EuclideanHOneThree) (φ : ℕ → ℕ),
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => interaction (u (φ n))) atTop
          (𝓝 (interaction v))) :
    ∃ v : EuclideanHOneThree,
      v ∈ admissible ∧ ‖v‖ ≤ B ∧ energy v = level ∧
      ∃ hvNormalized : HOneLTwoNormalized v,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (u ∘ φ) atTop (𝓝 v) ∧
          Tendsto
            (fun n => hOneBornProbability (u (φ n))
              (hnormalized (φ n)))
            atTop (𝓝 (hOneBornProbability v hvNormalized)) := by
  obtain ⟨v, hvBound, _ν, _hνmass, φ, hφ, hweak, _hmeasure⟩ :=
    bounded_normalized_hOne_firstMoment_has_joint_subsequence
      u B hu hnormalized C hC hmoment
  have hvAdmissible : v ∈ admissible :=
    hweakClosed v φ hφ hweak
  have henergyφ :
      Tendsto (fun n => energy (u (φ n))) atTop (𝓝 level) :=
    henergy.comp hφ.tendsto_atTop
  have hinteractionφ :
      Tendsto (fun n => interaction (u (φ n))) atTop
        (𝓝 (interaction v)) :=
    hinteractionClosure v φ hφ hweak
  have hclosure :=
    hOne_tendsto_of_minimizing_energySplit
      (u := u ∘ φ) (v := v) energy interaction kineticWeight level
      hkinetic
      (by simpa [Function.comp_def] using hweak)
      (fun n => hsplit (u (φ n)) (hu_admissible (φ n)))
      (hsplit v hvAdmissible)
      (by simpa [Function.comp_def] using henergyφ)
      (by simpa [Function.comp_def] using hinteractionφ)
      (hlower v hvAdmissible)
  have hvNormalized : HOneLTwoNormalized v :=
    hOneLTwoNormalized_of_tendsto
      (fun n => hnormalized (φ n)) hclosure.2
  have hborn :=
    hOneBornProbability_tendsto_of_strong
      (u := u ∘ φ) (v := v)
      (fun n => hnormalized (φ n)) hvNormalized hclosure.2
  exact ⟨v, hvAdmissible, hvBound, hclosure.1, hvNormalized,
    φ, hφ, hclosure.2, by simpa [Function.comp_def] using hborn⟩

/-- **Compactness of the full minimizing orbit with derived no-loss.**
Every sequence in the constrained ground-energy level has a strongly
convergent subsequence when it is uniformly `H¹` bounded, physically
normalized, localized by its actual first Born moment, weakly closes into
the admissible set, and its interaction converges along the selected weak
subsequence.

The energy is constant on the sequence, so the positive kinetic/interaction
split invokes `hOne_tendsto_of_minimizing_energySplit`; no independent
norm-closure hypothesis is accepted. -/
@[zil_level structural]
theorem isCompact_hOneBorn_energyMinimizers_of_interactionClosure
    (admissible : Set EuclideanHOneThree)
    (energy interaction : EuclideanHOneThree → ℝ)
    (kineticWeight level B : ℝ) (hkinetic : 0 < kineticWeight)
    (hbounded : ∀ z,
      z ∈ {z | z ∈ admissible ∧ energy z = level} → ‖z‖ ≤ B)
    (hnormalized : ∀ z,
      z ∈ {z | z ∈ admissible ∧ energy z = level} →
        HOneLTwoNormalized z)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hmoment : ∀ z,
      z ∈ {z | z ∈ admissible ∧ energy z = level} →
      ∫⁻ x, hOneBornDensity z x * ENNReal.ofReal ‖x‖
        ∂volume ≤ C)
    (hweakClosed :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n,
          u n ∈ {z | z ∈ admissible ∧ energy z = level}) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        v ∈ admissible)
    (hsplit : ∀ z ∈ admissible,
      energy z = kineticWeight * ‖z‖ ^ 2 + interaction z)
    (hlower : ∀ z ∈ admissible, level ≤ energy z)
    (hinteractionClosure :
      ∀ (u : ℕ → EuclideanHOneThree) (v : EuclideanHOneThree)
        (φ : ℕ → ℕ),
        (∀ n,
          u n ∈ {z | z ∈ admissible ∧ energy z = level}) →
        StrictMono φ →
        (∀ w : EuclideanHOneThree,
          Tendsto (fun n => inner ℂ (u (φ n)) w) atTop
            (𝓝 (inner ℂ v w))) →
        Tendsto (fun n => interaction (u (φ n))) atTop
          (𝓝 (interaction v))) :
    IsCompact {z | z ∈ admissible ∧ energy z = level} := by
  rw [isCompact_iff_isSeqCompact]
  intro u hu
  obtain ⟨v, _hvBound, _ν, _hνmass, φ, hφ, hweak, _hmeasure⟩ :=
    bounded_normalized_hOne_firstMoment_has_joint_subsequence
      u B (fun n => hbounded (u n) (hu n))
      (fun n => hnormalized (u n) (hu n))
      C hC (fun n => hmoment (u n) (hu n))
  have hvAdmissible : v ∈ admissible :=
    hweakClosed u v φ hu hφ hweak
  have hclosure :=
    hOne_tendsto_of_minimizing_energySplit
      (u := u ∘ φ) (v := v) energy interaction kineticWeight level
      hkinetic
      (by simpa [Function.comp_def] using hweak)
      (fun n => hsplit (u (φ n)) (hu (φ n)).1)
      (hsplit v hvAdmissible)
      (by
        convert
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => level) atTop (𝓝 level)) using 1
        funext n
        exact (hu (φ n)).2)
      (by simpa [Function.comp_def] using
        hinteractionClosure u v φ hu hφ hweak)
      (hlower v hvAdmissible)
  exact ⟨v, ⟨hvAdmissible, hclosure.1⟩, φ, hφ, hclosure.2⟩

/-- Weak convergence on the predicate-defined `H¹(ℝ³)` carrier, expressed
through the exact Bessel-energy coordinates. -/
def HOneWeaklyConverges
    (u : ℕ → EuclideanHs 3 1) (f : EuclideanHs 3 1) : Prop :=
  ∀ w : EuclideanHs 3 1,
    Tendsto
      (fun n => inner ℂ (hOneEnergyCoordinate (u n))
        (hOneEnergyCoordinate w))
      atTop
      (𝓝 (inner ℂ (hOneEnergyCoordinate f)
        (hOneEnergyCoordinate w)))

/-- Predicate-carrier form of weak `H¹` precompactness. A uniform bound on
the existing `sobolevNorm` supplies an `H¹` weakly convergent subsequence. -/
@[zil_level bridge_theorem]
theorem bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence
    (u : ℕ → EuclideanHs 3 1) (C : ℝ)
    (hu : ∀ n, sobolevNorm 1 (u n).1 (u n).2 ≤ C) :
    ∃ f : EuclideanHs 3 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      HOneWeaklyConverges (u ∘ φ) f := by
  obtain ⟨v, φ, hφ, hv⟩ :=
    bounded_hOne_has_weaklyConvergent_subsequence
      (fun n => hOneEnergyCoordinate (u n)) C (fun n => by
        simpa using hu n)
  refine ⟨hOneFromEnergyCoordinate v, φ, hφ, ?_⟩
  intro w
  simpa [HOneWeaklyConverges, Function.comp_def] using
    hv (hOneEnergyCoordinate w)

/-! ## A.4. Conditional direct method on the complete `H¹` carrier -/

/-- Sequential weak lower semicontinuity of a real functional on the
predicate-defined `H¹(ℝ³)` carrier. The scalar limit is explicit so the
definition can be used directly with a minimizing sequence. -/
def HOneSequentiallyWeaklyLowerSemicontinuous
    (J : EuclideanHs 3 1 → ℝ) : Prop :=
  ∀ (u : ℕ → EuclideanHs 3 1) (f : EuclideanHs 3 1) (L : ℝ),
    HOneWeaklyConverges u f →
    Tendsto (fun n => J (u n)) atTop (𝓝 L) →
    J f ≤ L

/-- **Conditional direct-method attainment on continuum `H¹(ℝ³)`.**
If a globally minimizing sequence is uniformly bounded in the existing
Sobolev norm and the functional is sequentially weakly lower
semicontinuous, then the infimum is attained.

For constrained translation-invariant problems such as
Schrödinger--Newton, the hypotheses still require a coercive sequence bound,
tightness/constraint closure, and lower semicontinuity of the promoted
functional; this theorem does not manufacture those analytic inputs. -/
@[zil_level bridge_theorem]
theorem exists_hOne_minimizer_of_bounded_minimizingSequence
    (J : EuclideanHs 3 1 → ℝ) (level C : ℝ)
    (u : ℕ → EuclideanHs 3 1)
    (hu : ∀ n, sobolevNorm 1 (u n).1 (u n).2 ≤ C)
    (hJ : Tendsto (fun n => J (u n)) atTop (𝓝 level))
    (hlower : ∀ f, level ≤ J f)
    (hlsc : HOneSequentiallyWeaklyLowerSemicontinuous J) :
    ∃ f : EuclideanHs 3 1, J f = level := by
  obtain ⟨f, φ, hφ, hf⟩ :=
    bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence u C hu
  have hJφ : Tendsto (fun n => J (u (φ n))) atTop (𝓝 level) :=
    hJ.comp hφ.tendsto_atTop
  have hupper : J f ≤ level :=
    hlsc (u ∘ φ) f level hf (by
      simpa [Function.comp_def] using hJφ)
  exact ⟨f, le_antisymm hupper (hlower f)⟩

/-! # B. Sobolev invariance under free Schrödinger evolution -/

lemma weightedFourier_evolution_ae {n : ℕ}
    (s t : ℝ) (f : EuclideanL2 n) :
    weightedFourier s (freeSchrodingerEvolution t f) =ᵐ[volume]
      fun ξ => freeSchrodingerPhase t ξ * weightedFourier s f ξ := by
  have hFourier :
      𝓕 (freeSchrodingerEvolution t f) =
        freeSchrodingerMultiplier t (𝓕 f) := by
    simp [freeSchrodingerEvolution]
  change
    (fun ξ =>
      (besselPotentialWeight s ξ : ℂ) *
        (𝓕 (freeSchrodingerEvolution t f)) ξ) =ᵐ[volume] _
  rw [hFourier]
  filter_upwards [freeSchrodingerMultiplier_coeFn t (𝓕 f)] with ξ hξ
  dsimp [weightedFourier]
  rw [hξ]
  ring

lemma memLp_phase_mul {n : ℕ}
    (t : ℝ) {g : EuclideanSpace ℝ (Fin n) → ℂ}
    (hg : MemLp g 2) :
    MemLp (fun ξ => freeSchrodingerPhase t ξ * g ξ) 2 := by
  exact hg.congr_norm
    ((((continuous_freeSchrodingerPhase.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      hg.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun ξ => by
      rw [norm_mul, norm_freeSchrodingerPhase, one_mul])

/-- Every free Schrödinger time slice preserves `H^s(ℝⁿ)` membership. -/
lemma freeSchrodingerEvolution_hasSobolevRegularity {n : ℕ}
    {s : ℝ} {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s f) (t : ℝ) :
    HasSobolevRegularity s (freeSchrodingerEvolution t f) := by
  exact (memLp_phase_mul t hf).ae_eq
    (weightedFourier_evolution_ae s t f).symm

lemma sobolevDerivativeFrequency_evolution {n : ℕ}
    {s : ℝ} {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s f) (t : ℝ) :
    sobolevDerivativeFrequency
        (freeSchrodingerEvolution_hasSobolevRegularity hf t) =
      freeSchrodingerMultiplier t (sobolevDerivativeFrequency hf) := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    MemLp.coeFn_toLp
      (freeSchrodingerEvolution_hasSobolevRegularity hf t),
    weightedFourier_evolution_ae s t f,
    freeSchrodingerMultiplier_coeFn t
      (sobolevDerivativeFrequency hf),
    MemLp.coeFn_toLp hf
  ] with ξ hevol hweighted hmult hbase
  change
    (freeSchrodingerEvolution_hasSobolevRegularity hf t).toLp
        (weightedFourier s (freeSchrodingerEvolution t f)) ξ =
      freeSchrodingerMultiplier t
        (sobolevDerivativeFrequency hf) ξ
  rw [hevol, hweighted, hmult]
  change
    freeSchrodingerPhase t ξ * weightedFourier s f ξ =
      freeSchrodingerPhase t ξ *
        hf.toLp (weightedFourier s f) ξ
  rw [hbase]

/-- The free Schrödinger flow exactly conserves every defined `H^s` norm. -/
lemma sobolevNorm_freeSchrodingerEvolution {n : ℕ}
    {s : ℝ} {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s f) (t : ℝ) :
    sobolevNorm s (freeSchrodingerEvolution t f)
        (freeSchrodingerEvolution_hasSobolevRegularity hf t) =
      sobolevNorm s f hf := by
  unfold sobolevNorm
  rw [sobolevDerivativeFrequency_evolution (hf := hf) t,
    norm_freeSchrodingerMultiplier]

/-- Free Schrödinger evolution lifted to the native `H^s` carrier. -/
def freeSchrodingerEvolutionHs {n : ℕ} {s : ℝ}
    (t : ℝ) (f : EuclideanHs n s) : EuclideanHs n s :=
  ⟨freeSchrodingerEvolution t f.1,
    freeSchrodingerEvolution_hasSobolevRegularity f.2 t⟩

@[simp] lemma freeSchrodingerEvolutionHs_zero {n : ℕ} {s : ℝ}
    (f : EuclideanHs n s) :
    freeSchrodingerEvolutionHs 0 f = f := by
  apply Subtype.ext
  simp [freeSchrodingerEvolutionHs]

lemma freeSchrodingerEvolutionHs_add {n : ℕ} {s : ℝ}
    (a b : ℝ) (f : EuclideanHs n s) :
    freeSchrodingerEvolutionHs (a + b) f =
      freeSchrodingerEvolutionHs a (freeSchrodingerEvolutionHs b f) := by
  apply Subtype.ext
  exact freeSchrodingerEvolution_add a b f.1

/-! # C. Rough annular Fourier localization -/

/-- The paper's rough frequency annulus
`A(R) = {ξ | R/2 ≤ ‖ξ‖ ∧ ‖ξ‖ < R}`. -/
def frequencyAnnulus {n : ℕ} (R : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {ξ | R / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ < R}

lemma measurableSet_frequencyAnnulus {n : ℕ} (R : ℝ) :
    MeasurableSet (frequencyAnnulus (n := n) R) := by
  exact
    (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)

/-- The rough annular cutoff on frequency-space `L²`. -/
def annularCutoff {n : ℕ}
    (R : ℝ) (g : EuclideanL2 n) : EuclideanL2 n :=
  ((Lp.memLp g).indicator (measurableSet_frequencyAnnulus R)).toLp
    ((frequencyAnnulus R).indicator fun ξ => g ξ)

lemma annularCutoff_coeFn {n : ℕ}
    (R : ℝ) (g : EuclideanL2 n) :
    annularCutoff R g =ᵐ[volume]
      (frequencyAnnulus R).indicator fun ξ => g ξ :=
  MemLp.coeFn_toLp _

/-- Rough annular localization is an `L²` contraction. -/
lemma norm_annularCutoff_le {n : ℕ}
    (R : ℝ) (g : EuclideanL2 n) :
    ‖annularCutoff R g‖ ≤ ‖g‖ := by
  rw [annularCutoff, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (by finiteness) (eLpNorm_indicator_le _)

/-- Applying the same rough annular cutoff twice changes nothing. -/
@[simp] lemma annularCutoff_idempotent {n : ℕ}
    (R : ℝ) (g : EuclideanL2 n) :
    annularCutoff R (annularCutoff R g) = annularCutoff R g := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    annularCutoff_coeFn R (annularCutoff R g),
    annularCutoff_coeFn R g
  ] with ξ houter hinner
  by_cases hξ : ξ ∈ frequencyAnnulus R
  · simp [houter, hinner, hξ]
  · simp [houter, hinner, hξ]

lemma annularCutoff_commutes_multiplier {n : ℕ}
    (R t : ℝ) (g : EuclideanL2 n) :
    annularCutoff R (freeSchrodingerMultiplier t g) =
      freeSchrodingerMultiplier t (annularCutoff R g) := by
  apply Lp.ext (μ := volume)
  filter_upwards [
    annularCutoff_coeFn R (freeSchrodingerMultiplier t g),
    freeSchrodingerMultiplier_coeFn t g,
    freeSchrodingerMultiplier_coeFn t (annularCutoff R g),
    annularCutoff_coeFn R g
  ] with ξ hleft hmult hright hcut
  by_cases hξ : ξ ∈ frequencyAnnulus R
  · rw [hleft, indicator_of_mem hξ, hright, hcut,
      indicator_of_mem hξ]
    exact hmult
  · rw [hleft, indicator_of_notMem hξ, hright, hcut,
      indicator_of_notMem hξ, mul_zero]

/-- The physical-space rough frequency projection
`χ_{A(R)}(D) = 𝓕⁻ χ_{A(R)} 𝓕`. -/
def annularFrequencyProjection {n : ℕ}
    (R : ℝ) (f : EuclideanL2 n) : EuclideanL2 n :=
  𝓕⁻ (annularCutoff R (𝓕 f))

/-- The physical-space rough frequency projection is idempotent. -/
@[simp] lemma annularFrequencyProjection_idempotent {n : ℕ}
    (R : ℝ) (f : EuclideanL2 n) :
    annularFrequencyProjection R (annularFrequencyProjection R f) =
      annularFrequencyProjection R f := by
  simp [annularFrequencyProjection]

/-- The physical-space rough annular projection is an `L²` contraction. -/
lemma norm_annularFrequencyProjection_le {n : ℕ}
    (R : ℝ) (f : EuclideanL2 n) :
    ‖annularFrequencyProjection R f‖ ≤ ‖f‖ := by
  have hinv :
      ‖𝓕⁻ (annularCutoff R (𝓕 f))‖ =
        ‖annularCutoff R (𝓕 f)‖ := by
    simpa using
      (MeasureTheory.Lp.norm_fourier_eq
        (𝓕⁻ (annularCutoff R (𝓕 f)))).symm
  rw [annularFrequencyProjection, hinv]
  exact (norm_annularCutoff_le R (𝓕 f)).trans_eq
    (MeasureTheory.Lp.norm_fourier_eq f)

/-- Rough annular projection commutes with the free Schrödinger flow. -/
lemma annularFrequencyProjection_commutes_evolution {n : ℕ}
    (R t : ℝ) (f : EuclideanL2 n) :
    annularFrequencyProjection R (freeSchrodingerEvolution t f) =
      freeSchrodingerEvolution t (annularFrequencyProjection R f) := by
  simp [annularFrequencyProjection, freeSchrodingerEvolution,
    annularCutoff_commutes_multiplier]

/-! # D. Frequency localization inside `H^s` -/

lemma weightedFourier_annularFrequencyProjection_ae {n : ℕ}
    (s R : ℝ) (f : EuclideanL2 n) :
    weightedFourier s (annularFrequencyProjection R f) =ᵐ[volume]
      (frequencyAnnulus R).indicator (weightedFourier s f) := by
  have hFourier :
      𝓕 (annularFrequencyProjection R f) =
        annularCutoff R (𝓕 f) := by
    simp [annularFrequencyProjection]
  change
    (fun ξ =>
      (besselPotentialWeight s ξ : ℂ) *
        (𝓕 (annularFrequencyProjection R f)) ξ) =ᵐ[volume] _
  rw [hFourier]
  filter_upwards [annularCutoff_coeFn R (𝓕 f)] with ξ hξ
  by_cases hmem : ξ ∈ frequencyAnnulus R
  · rw [hξ, indicator_of_mem hmem, indicator_of_mem hmem]
    rfl
  · rw [hξ, indicator_of_notMem hmem, mul_zero,
      indicator_of_notMem hmem]

/-- Rough annular projection preserves `H^s` membership. -/
lemma annularFrequencyProjection_hasSobolevRegularity {n : ℕ}
    {s : ℝ} {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s f) (R : ℝ) :
    HasSobolevRegularity s (annularFrequencyProjection R f) := by
  exact
    (hf.indicator (measurableSet_frequencyAnnulus R)).ae_eq
      (weightedFourier_annularFrequencyProjection_ae s R f).symm

set_option backward.isDefEq.respectTransparency false in
/-- Rough annular projection contracts the Bessel-potential `H^s` norm. -/
lemma sobolevNorm_annularFrequencyProjection_le {n : ℕ}
    {s : ℝ} {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s f) (R : ℝ) :
    sobolevNorm s (annularFrequencyProjection R f)
        (annularFrequencyProjection_hasSobolevRegularity hf R) ≤
      sobolevNorm s f hf := by
  unfold sobolevNorm sobolevDerivativeFrequency
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono
  · finiteness
  calc
    eLpNorm
        (weightedFourier s (annularFrequencyProjection R f)) 2 volume =
        eLpNorm
          ((frequencyAnnulus R).indicator (weightedFourier s f)) 2 volume := by
      exact eLpNorm_congr_ae
        (weightedFourier_annularFrequencyProjection_ae s R f)
    _ ≤ eLpNorm (weightedFourier s f) 2 volume :=
      eLpNorm_indicator_le _

/-- Capstone for the paper's rigorously implemented Sobolev/frequency layer:
free evolution conserves `H^s`, while rough annular localization is an
idempotent contraction commuting with that evolution. -/
lemma euclideanSobolev_freeEvolution_annularLocalization {n : ℕ}
    {s : ℝ} {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s f) (R t : ℝ) :
    HasSobolevRegularity s (freeSchrodingerEvolution t f) ∧
    sobolevNorm s (freeSchrodingerEvolution t f)
        (freeSchrodingerEvolution_hasSobolevRegularity hf t) =
      sobolevNorm s f hf ∧
    annularCutoff R (annularCutoff R (𝓕 f)) =
      annularCutoff R (𝓕 f) ∧
    ‖annularFrequencyProjection R f‖ ≤ ‖f‖ ∧
    annularFrequencyProjection R (freeSchrodingerEvolution t f) =
      freeSchrodingerEvolution t (annularFrequencyProjection R f) ∧
    HasSobolevRegularity s (annularFrequencyProjection R f) ∧
    sobolevNorm s (annularFrequencyProjection R f)
        (annularFrequencyProjection_hasSobolevRegularity hf R) ≤
    sobolevNorm s f hf := by
  exact ⟨freeSchrodingerEvolution_hasSobolevRegularity hf t,
    sobolevNorm_freeSchrodingerEvolution hf t,
    annularCutoff_idempotent R (𝓕 f),
    norm_annularFrequencyProjection_le R f,
    annularFrequencyProjection_commutes_evolution R t f,
    annularFrequencyProjection_hasSobolevRegularity hf R,
    sobolevNorm_annularFrequencyProjection_le hf R⟩

/-- Full hierarchy capstone for the implemented paper layer: `H⁰ = L²`,
higher Sobolev membership and norm dominate lower order, free evolution
conserves the chosen Sobolev norm, and the rough annular projection is an
idempotent contraction commuting with the flow. -/
@[zil_level bridge_theorem]
lemma euclideanSobolev_hierarchy_freeEvolution_annularLocalization {n : ℕ}
    {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) {f : EuclideanL2 n}
    (hf : HasSobolevRegularity s₂ f) (R t : ℝ) :
    HasSobolevRegularity 0 f ∧
    sobolevNorm 0 f (hasSobolevRegularity_zero f) = ‖f‖ ∧
    HasSobolevRegularity s₁ f ∧
    sobolevNorm s₁ f (hf.mono hs) ≤ sobolevNorm s₂ f hf ∧
    sobolevNorm s₂ (freeSchrodingerEvolution t f)
        (freeSchrodingerEvolution_hasSobolevRegularity hf t) =
      sobolevNorm s₂ f hf ∧
    annularFrequencyProjection R (annularFrequencyProjection R f) =
      annularFrequencyProjection R f ∧
    ‖annularFrequencyProjection R f‖ ≤ ‖f‖ ∧
    annularFrequencyProjection R (freeSchrodingerEvolution t f) =
      freeSchrodingerEvolution t (annularFrequencyProjection R f) ∧
    HasSobolevRegularity s₂ (annularFrequencyProjection R f) ∧
    sobolevNorm s₂ (annularFrequencyProjection R f)
        (annularFrequencyProjection_hasSobolevRegularity hf R) ≤
      sobolevNorm s₂ f hf := by
  exact ⟨hasSobolevRegularity_zero f,
    sobolevNorm_zero_eq_l2Norm f,
    hf.mono hs,
    sobolevNorm_mono hs hf,
    sobolevNorm_freeSchrodingerEvolution hf t,
    annularFrequencyProjection_idempotent R f,
    norm_annularFrequencyProjection_le R f,
    annularFrequencyProjection_commutes_evolution R t f,
    annularFrequencyProjection_hasSobolevRegularity hf R,
    sobolevNorm_annularFrequencyProjection_le hf R⟩

/-! # E. The homogeneous energy space on `ℝ³`

The homogeneous Sobolev space is represented intrinsically by gradients:
start with compactly supported Schwartz functions, map them into
`L²(ℝ³; (ℝ³ →L[ℝ] ℂ))` by the Fréchet derivative, and take the closed linear
span.  This is the usual completion modulo the zero-gradient seminorm, but it
avoids choosing representatives of homogeneous Sobolev classes.
-/

/-- The Fourier representative `|ξ| f̂(ξ)` defining the homogeneous
first-order Sobolev seminorm. -/
def homogeneousOneWeightedFourier
    (f : EuclideanL2 3) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun ξ => (‖ξ‖ : ℂ) * (𝓕 f) ξ

lemma aestronglyMeasurable_homogeneousOneWeightedFourier
    (f : EuclideanL2 3) :
    AEStronglyMeasurable (homogeneousOneWeightedFourier f) := by
  exact
    ((Complex.continuous_ofReal.comp continuous_norm).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable (𝓕 f))

/-- Fourier-definition membership in `Ḣ¹(ℝ³)` for an `L²` representative. -/
def HasHomogeneousSobolevRegularityOne (f : EuclideanL2 3) : Prop :=
  MemLp (homogeneousOneWeightedFourier f) 2

/-- The `L²` representative of `|D|f`. -/
def homogeneousSobolevDerivativeFrequency
    {f : EuclideanL2 3} (hf : HasHomogeneousSobolevRegularityOne f) :
    EuclideanL2 3 :=
  hf.toLp (homogeneousOneWeightedFourier f)

/-- The genuine Fourier homogeneous `Ḣ¹` seminorm `‖|D|f‖₂`. -/
def homogeneousSobolevOneNorm
    (f : EuclideanL2 3) (hf : HasHomogeneousSobolevRegularityOne f) : ℝ :=
  ‖homogeneousSobolevDerivativeFrequency hf‖

private lemma norm_le_besselPotentialWeight_one
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖ξ‖ ≤ besselPotentialWeight 1 ξ := by
  rw [besselPotentialWeight, ← Real.sqrt_eq_rpow,
    Real.le_sqrt (norm_nonneg ξ) (by positivity)]
  linarith

/-- Inhomogeneous `H¹(ℝ³)` continuously embeds in homogeneous `Ḣ¹(ℝ³)`
with constant one. -/
lemma HasSobolevRegularity.hasHomogeneousOne
    {f : EuclideanL2 3} (hf : HasSobolevRegularity 1 f) :
    HasHomogeneousSobolevRegularityOne f := by
  refine hf.of_le
    (aestronglyMeasurable_homogeneousOneWeightedFourier f)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [homogeneousOneWeightedFourier, weightedFourier, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg ξ), abs_of_pos (besselPotentialWeight_pos 1 ξ)]
  exact mul_le_mul_of_nonneg_right
    (norm_le_besselPotentialWeight_one ξ) (norm_nonneg ((𝓕 f) ξ))

set_option backward.isDefEq.respectTransparency false in
/-- Quantitative form of `H¹(ℝ³) ↪ Ḣ¹(ℝ³)`. -/
lemma homogeneousSobolevOneNorm_le_sobolevNorm_one
    {f : EuclideanL2 3} (hf : HasSobolevRegularity 1 f) :
    homogeneousSobolevOneNorm f hf.hasHomogeneousOne ≤ sobolevNorm 1 f hf := by
  unfold homogeneousSobolevOneNorm homogeneousSobolevDerivativeFrequency
    sobolevNorm sobolevDerivativeFrequency
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono
  · finiteness
  exact eLpNorm_mono_ae (Filter.Eventually.of_forall fun ξ => by
    rw [homogeneousOneWeightedFourier, weightedFourier, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg ξ), abs_of_pos (besselPotentialWeight_pos 1 ξ)]
    exact mul_le_mul_of_nonneg_right
      (norm_le_besselPotentialWeight_one ξ) (norm_nonneg ((𝓕 f) ξ)))

private lemma besselPotentialWeight_one_le_one_add_norm
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    besselPotentialWeight 1 ξ ≤ 1 + ‖ξ‖ := by
  rw [besselPotentialWeight, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [sq_nonneg ‖ξ‖, norm_nonneg ξ]

/-- On `ℝ³`, an `L²` function with one homogeneous derivative in `L²`
belongs to the inhomogeneous space `H¹`.  This is the exact continuum
implication `L² ∩ Ḣ¹ = H¹`; the `L²` premise is carried by the type of `f`
and is therefore not silently inferred for a general tempered Newton
potential. -/
@[zil_level structural]
lemma HasHomogeneousSobolevRegularityOne.hasSobolevOne
    {f : EuclideanL2 3} (hf : HasHomogeneousSobolevRegularityOne f) :
    HasSobolevRegularity 1 f := by
  have hFourier : MemLp (fun ξ => (𝓕 f) ξ) 2 := Lp.memLp (𝓕 f)
  have hsum : MemLp
      (fun ξ => (𝓕 f) ξ + homogeneousOneWeightedFourier f ξ) 2 :=
    hFourier.add hf
  refine hsum.of_le
    (aestronglyMeasurable_weightedFourier 1 f)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [weightedFourier, homogeneousOneWeightedFourier]
  have hfactor :
      (𝓕 f) ξ + (‖ξ‖ : ℂ) * (𝓕 f) ξ =
        ((1 + ‖ξ‖ : ℝ) : ℂ) * (𝓕 f) ξ := by
    push_cast
    ring
  rw [hfactor, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (besselPotentialWeight_pos 1 ξ),
    abs_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖)]
  exact mul_le_mul_of_nonneg_right
    (besselPotentialWeight_one_le_one_add_norm ξ) (norm_nonneg ((𝓕 f) ξ))

/-- Compactly supported complex Schwartz functions on `ℝ³`, the core used
to construct the homogeneous energy space. -/
def CompactlySupportedSchwartzThree :
    Submodule ℂ 𝓢(EuclideanSpace ℝ (Fin 3), ℂ) where
  carrier := {f | HasCompactSupport (f : EuclideanSpace ℝ (Fin 3) → ℂ)}
  zero_mem' := HasCompactSupport.zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun _ _ hf => hf.smul_left

/-- The `L²` gradient map on the compactly supported Schwartz core. -/
def compactSchwartzGradientL2 :
    CompactlySupportedSchwartzThree →ₗ[ℂ]
      Lp (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ) 2
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  ((SchwartzMap.toLpCLM ℂ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))).comp
    (SchwartzMap.fderivCLM ℂ (EuclideanSpace ℝ (Fin 3)) ℂ)).toLinearMap.comp
      CompactlySupportedSchwartzThree.subtype

/-- The genuine homogeneous `Ḣ¹(ℝ³)` carrier, realized as the closed
`L²`-subspace generated by gradients of compactly supported Schwartz
functions.  Its inherited norm is exactly the homogeneous energy norm. -/
abbrev EuclideanDotHOneThree : Type :=
  (LinearMap.range compactSchwartzGradientL2).topologicalClosure

instance : CompleteSpace EuclideanDotHOneThree := by
  unfold EuclideanDotHOneThree
  infer_instance

/-- Every core gradient belongs to the completed homogeneous energy space. -/
def compactSchwartzToDotHOne (f : CompactlySupportedSchwartzThree) :
    EuclideanDotHOneThree :=
  ⟨compactSchwartzGradientL2 f,
    (LinearMap.range compactSchwartzGradientL2).le_topologicalClosure
      ⟨f, rfl⟩⟩

@[simp] lemma norm_compactSchwartzToDotHOne
    (f : CompactlySupportedSchwartzThree) :
    ‖compactSchwartzToDotHOne f‖ = ‖compactSchwartzGradientL2 f‖ :=
  rfl

/-- The continuum `Ḣ¹(ℝ³) → L⁶(ℝ³)` Sobolev inequality on the dense
compactly supported Schwartz core.  The right-hand side is the actual `L²`
Fréchet-gradient norm used by `EuclideanDotHOneThree`; no finite-mode or
inhomogeneous proxy occurs. -/
@[zil_level bridge_theorem]
lemma eLpNorm_six_le_gradient_two
    (f : CompactlySupportedSchwartzThree) :
    eLpNorm (f : EuclideanSpace ℝ (Fin 3) → ℂ) 6
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) ≤
      MeasureTheory.SNormLESNormFDerivOfEqConst ℂ
          (volume : Measure (EuclideanSpace ℝ (Fin 3))) 2 *
        eLpNorm (fderiv ℝ (f : EuclideanSpace ℝ (Fin 3) → ℂ)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  exact MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (u := (f : EuclideanSpace ℝ (Fin 3) → ℂ))
    (p := 2) (p' := 6) (f.1.smooth 1) f.2 (by norm_num) (by simp) (by norm_num)

/-! # F. Weak Poisson solvability and zero-boundary uniqueness in `Ḣ¹`

The Fourier-energy coordinate of a homogeneous Sobolev class is `|D|u ∈ L²`.
Consequently the Hilbert carrier below is not a finite approximation: its
elements are equivalence classes of measurable functions on all of `ℝ³`.
Fréchet--Riesz is the Lax--Milgram theorem for the Dirichlet form in these
coordinates.
-/

/-- The Fourier energy-coordinate carrier of `Ḣ¹(ℝ³)`, namely the continuum
`L²` carrier of `|D|u`. -/
abbrev FourierDotHOneThree : Type := EuclideanL2 3

/-- The dual source space `Ḣ⁻¹(ℝ³)`. -/
abbrev FourierDotHMinusOneThree : Type :=
  StrongDual ℂ FourierDotHOneThree

/-- The weak Dirichlet/Poisson equation in Fourier energy coordinates. -/
def IsFourierDotHOneWeakSolution
    (source : FourierDotHMinusOneThree)
    (energyDerivative : FourierDotHOneThree) : Prop :=
  ∀ test : FourierDotHOneThree, ⟪energyDerivative, test⟫_ℂ = source test

/-- The canonical `Ḣ¹` weak solution of a source in `Ḣ⁻¹`, obtained from
Fréchet--Riesz (equivalently Lax--Milgram for the Dirichlet form). -/
noncomputable def fourierDotHOnePoissonSolution
    (source : FourierDotHMinusOneThree) : FourierDotHOneThree :=
  (InnerProductSpace.toDual ℂ FourierDotHOneThree).symm source

/-- The Riesz representative solves the weak Poisson equation. -/
lemma fourierDotHOnePoissonSolution_weak
    (source : FourierDotHMinusOneThree) :
    IsFourierDotHOneWeakSolution source
      (fourierDotHOnePoissonSolution source) := by
  intro test
  exact InnerProductSpace.toDual_symm_apply

/-- **Zero-boundary uniqueness.** A `Ḣ¹` solution is determined uniquely by
its `Ḣ⁻¹` source. Constants and other non-decaying harmonic additions are
absent because the carrier is the homogeneous energy completion. -/
lemma fourierDotHOnePoissonSolution_unique
    (source : FourierDotHMinusOneThree)
    {energyDerivative : FourierDotHOneThree}
    (henergy : IsFourierDotHOneWeakSolution source energyDerivative) :
    energyDerivative = fourierDotHOnePoissonSolution source := by
  apply (InnerProductSpace.toDual ℂ FourierDotHOneThree).injective
  ext test
  rw [InnerProductSpace.toDual_apply_apply, henergy test]
  exact (fourierDotHOnePoissonSolution_weak source test).symm

/-- Existence and uniqueness of the continuum `Ḣ¹₀` weak Poisson solution. -/
@[zil_level structural]
lemma existsUnique_fourierDotHOneWeakSolution
    (source : FourierDotHMinusOneThree) :
    ∃! energyDerivative : FourierDotHOneThree,
      IsFourierDotHOneWeakSolution source energyDerivative :=
  ⟨fourierDotHOnePoissonSolution source,
    fourierDotHOnePoissonSolution_weak source,
    fun _ h => fourierDotHOnePoissonSolution_unique source h⟩

/-- Sharp energy estimate for the weak solution: its `Ḣ¹` norm equals the
operator norm of the `Ḣ⁻¹` source. -/
@[zil_level structural]
lemma norm_fourierDotHOnePoissonSolution
    (source : FourierDotHMinusOneThree) :
    ‖fourierDotHOnePoissonSolution source‖ = ‖source‖ :=
  (InnerProductSpace.toDual ℂ FourierDotHOneThree).symm.norm_map source

/-! # G. Schwartz sources are genuine `Ḣ⁻¹` data

For a Schwartz density `ρ`, the Fourier energy coordinate of the Newton
solution is `ρ̂(ξ) / |ξ|`.  Its square has the locally singular factor
`|ξ|⁻²`, which is integrable precisely because the ambient dimension is
three; away from the origin the inverse norm is bounded and Schwartz `L²`
decay closes the estimate.  This removes the former abstract `Ḣ⁻¹` premise
for the source class used by the continuum Newton construction.
-/

/-- Division of a Schwartz Fourier profile by the radial frequency.  Lean's
inverse convention makes the value at `ξ = 0` equal to zero, which is harmless
for the `L²` equivalence class. -/
def inverseNormSchwartzThree
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun ξ => ((‖ξ‖⁻¹ : ℝ) : ℂ) * f ξ

lemma inverseNormSchwartzThree_aestronglyMeasurable
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    AEStronglyMeasurable (inverseNormSchwartzThree f) := by
  exact
    ((Complex.continuous_ofReal.measurable.comp
      continuous_norm.measurable.inv).aestronglyMeasurable.mul
        f.continuous.aestronglyMeasurable)

/-- In dimension three, `f(ξ)/|ξ| ∈ L²` for every Schwartz function `f`.
The proof is the actual local-singularity/exterior-decay decomposition, not
an assumed Sobolev-membership certificate. -/
@[zil_level structural]
lemma inverseNormSchwartzThree_memLp_two
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    MemLp (inverseNormSchwartzThree f) 2 := by
  rw [memLp_two_iff_integrable_sq_norm
    (inverseNormSchwartzThree_aestronglyMeasurable f)]
  rw [← integrableOn_univ]
  let E3 := EuclideanSpace ℝ (Fin 3)
  have huniv : Metric.ball (0 : E3) 1 ∪ (Metric.ball (0 : E3) 1)ᶜ = univ :=
    union_compl_self _
  rw [← huniv, integrableOn_union]
  constructor
  · apply integrableOn_ball_of_norm_le_rpow (μ := volume) (hd := by simp)
      (f := fun ξ => ‖inverseNormSchwartzThree f ξ‖ ^ 2)
      (C := (SchwartzMap.seminorm ℝ 0 0 f) ^ 2) (α := 2)
      (r := 1)
    · norm_num
    · exact Filter.Eventually.of_forall fun ξ => by
        by_cases hξ : ξ = 0
        · subst ξ
          simp [inverseNormSchwartzThree]
        · rw [Real.norm_of_nonneg (sq_nonneg _)]
          rw [inverseNormSchwartzThree, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_inv, abs_norm, mul_pow]
          have hf := SchwartzMap.norm_le_seminorm ℝ f ξ
          have hsq := pow_le_pow_left₀ (norm_nonneg (f ξ)) hf 2
          rw [Real.rpow_neg (norm_nonneg ξ)]
          have hinvpow :
              ‖ξ‖⁻¹ ^ 2 = (‖ξ‖ ^ (2 : ℝ))⁻¹ := by
            rw [Real.rpow_two]
            exact inv_pow ‖ξ‖ 2
          have hbase :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖ξ‖⁻¹)
          rw [hinvpow] at hbase
          rw [hinvpow]
          simpa only [mul_comm] using hbase
    · exact
        (inverseNormSchwartzThree_aestronglyMeasurable f).norm.pow 2
  · have hfint :
        Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => ‖f ξ‖ ^ 2) :=
      (f.memLp 2 volume).integrable_norm_pow (by norm_num)
    rw [IntegrableOn]
    apply (hfint.mono_measure Measure.restrict_le_self).mono
    · exact
        ((inverseNormSchwartzThree_aestronglyMeasurable f).norm.pow 2).mono_measure
          Measure.restrict_le_self
    · filter_upwards [
        ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with ξ hξ
      rw [Real.norm_of_nonneg (sq_nonneg _),
        Real.norm_of_nonneg (sq_nonneg _)]
      rw [inverseNormSchwartzThree, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_inv, abs_norm, mul_pow]
      have hnorm : 1 ≤ ‖ξ‖ := by
        simpa [Metric.mem_ball, dist_zero_right, not_lt] using hξ
      have hinv : ‖ξ‖⁻¹ ≤ 1 :=
        (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hnorm)).2 hnorm
      have hinv_sq : ‖ξ‖⁻¹ ^ 2 ≤ 1 :=
        (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg ξ)) hinv 2).trans_eq
          (one_pow 2)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hinv_sq (sq_nonneg ‖f ξ‖)

/-- Fourier transform of a Schwartz source. -/
noncomputable def schwartzSourceFourierThree
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.fourierTransformCLM ℂ ρ

/-- The `L²` energy coordinate `ρ̂/|ξ|` of a Schwartz Newton source. -/
noncomputable def schwartzSourceEnergyVector
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    FourierDotHOneThree :=
  (inverseNormSchwartzThree_memLp_two (schwartzSourceFourierThree ρ)).toLp
    (inverseNormSchwartzThree (schwartzSourceFourierThree ρ))

/-- Every Schwartz density canonically defines a source in `Ḣ⁻¹(ℝ³)`. -/
noncomputable def schwartzSourceDotHMinusOne
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    FourierDotHMinusOneThree :=
  InnerProductSpace.toDual ℂ FourierDotHOneThree
    (schwartzSourceEnergyVector ρ)

/-- The unique weak Newton solution has energy coordinate `ρ̂/|ξ|`. -/
@[zil_level structural]
lemma fourierDotHOnePoissonSolution_schwartzSource
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    fourierDotHOnePoissonSolution (schwartzSourceDotHMinusOne ρ) =
      schwartzSourceEnergyVector ρ := by
  simp [fourierDotHOnePoissonSolution, schwartzSourceDotHMinusOne]

/-- The Fourier Newton multiplier `ρ̂(ξ)/|ξ|²`.  It is defined pointwise as
a measurable representative; unlike its energy derivative, it need not be
globally `L²` when the source has nonzero total mass. -/
noncomputable def schwartzNewtonFourierPotential
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun ξ => (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
    schwartzSourceFourierThree ρ ξ

lemma schwartzNewtonFourierPotential_energy_pointwise
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    (‖ξ‖ : ℂ) * schwartzNewtonFourierPotential ρ ξ =
      inverseNormSchwartzThree (schwartzSourceFourierThree ρ) ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [schwartzNewtonFourierPotential, inverseNormSchwartzThree]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    rw [schwartzNewtonFourierPotential, inverseNormSchwartzThree]
    push_cast
    field_simp

lemma schwartzNewtonFourierPotential_aestronglyMeasurable
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    AEStronglyMeasurable (schwartzNewtonFourierPotential ρ) := by
  change AEStronglyMeasurable (fun ξ =>
    (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * schwartzSourceFourierThree ρ ξ)
  exact
    ((Complex.continuous_ofReal.measurable.comp
      (continuous_norm.pow 2).measurable.inv).aestronglyMeasurable.mul
        (schwartzSourceFourierThree ρ).continuous.aestronglyMeasurable)

/-- Exact `H¹` upgrade criterion for the Schwartz Newton solution:
its homogeneous derivative is automatically in `L²`; therefore the full
Bessel-weighted Fourier profile is in `L²` exactly when the potential itself
has the additional infrared `L²` integrability. -/
@[zil_level structural]
lemma schwartzNewtonFourierPotential_besselOne_memLp_iff
    (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    MemLp (fun ξ =>
        (besselPotentialWeight 1 ξ : ℂ) *
          schwartzNewtonFourierPotential ρ ξ) 2 ↔
      MemLp (schwartzNewtonFourierPotential ρ) 2 := by
  constructor
  · intro hweighted
    refine hweighted.of_le
      (schwartzNewtonFourierPotential_aestronglyMeasurable ρ)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (besselPotentialWeight_pos 1 ξ)]
    exact le_mul_of_one_le_left (norm_nonneg _) (by
      rw [show (1 : ℝ) = besselPotentialWeight 0 ξ by simp]
      exact besselPotentialWeight_mono (by norm_num) ξ)
  · intro hpotential
    have henergy :
        MemLp (fun ξ =>
          (‖ξ‖ : ℂ) * schwartzNewtonFourierPotential ρ ξ) 2 :=
      (inverseNormSchwartzThree_memLp_two
        (schwartzSourceFourierThree ρ)).ae_eq
          (Filter.Eventually.of_forall fun ξ =>
            (schwartzNewtonFourierPotential_energy_pointwise ρ ξ).symm)
    have hsum := hpotential.add henergy
    refine hsum.of_le
      (((Complex.continuous_ofReal.comp
        (continuous_besselPotentialWeight 1)).aestronglyMeasurable).mul
          (schwartzNewtonFourierPotential_aestronglyMeasurable ρ))
      (Filter.Eventually.of_forall fun ξ => ?_)
    have hfactor :
        schwartzNewtonFourierPotential ρ ξ +
            (‖ξ‖ : ℂ) * schwartzNewtonFourierPotential ρ ξ =
          ((1 + ‖ξ‖ : ℝ) : ℂ) *
            schwartzNewtonFourierPotential ρ ξ := by
      push_cast
      ring
    change
      ‖(besselPotentialWeight 1 ξ : ℂ) *
          schwartzNewtonFourierPotential ρ ξ‖ ≤
        ‖schwartzNewtonFourierPotential ρ ξ +
          (‖ξ‖ : ℂ) * schwartzNewtonFourierPotential ρ ξ‖
    rw [hfactor, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (besselPotentialWeight_pos 1 ξ),
      abs_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖)]
    exact mul_le_mul_of_nonneg_right
      (besselPotentialWeight_one_le_one_add_norm ξ)
      (norm_nonneg (schwartzNewtonFourierPotential ρ ξ))

end Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
