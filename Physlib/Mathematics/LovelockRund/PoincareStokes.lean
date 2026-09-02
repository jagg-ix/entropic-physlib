/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Poincaré, Stokes, and divergence bridges

This module formalizes the integral theorems used in Lovelock--Rund Sections
5.3, 5.5, and 7.6 by reusing Mathlib's existing results.

* The one-dimensional Stokes theorem is the fundamental theorem of calculus.
* A closed 1-form on an open convex subset of a normed space admits a
  primitive. The model space may be infinite dimensional.
* The divergence theorem is exposed for Bochner integrals on rectangular
  boxes in `Fin (n + 1) → ℝ`.

No integral theorem is postulated as an axiom or an abstract boundary-flux
carrier.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open Set MeasureTheory
open scoped Interval Topology

/-- One-dimensional Stokes theorem or fundamental theorem of calculus. -/
theorem intervalStokes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b : ℝ}
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Integral of an exact derivative around an interval with equal endpoint
values vanishes. -/
theorem intervalStokes_closed_endpoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b : ℝ}
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b)
    (hend : f b = f a) :
    ∫ x in a..b, f' x = 0 := by
  rw [intervalStokes hderiv hint, hend, sub_self]

/-- A 1-form in the representation used by Mathlib's curve-integral and
Poincaré APIs. -/
abbrev LinearOneForm (𝕜 E F : Type*)
    [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  E → E →L[𝕜] F

/-- Poincaré lemma for a closed 1-form on an open convex set. The ambient
normed space is not assumed finite dimensional. -/
theorem poincareLemma_oneForm
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    [CompleteSpace F]
    {s : Set E} {ω : LinearOneForm 𝕜 E F}
    (hs : Convex ℝ s) (hso : IsOpen s)
    (hω : DifferentiableOn ℝ ω s)
    (hclosed : ∀ a ∈ s, ∀ x y,
      fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ potential : E → F,
      ∀ a ∈ s, HasFDerivAt potential (ω a) a :=
  hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso hω hclosed

/-- Closed 1-forms have additive segment integrals on convex sets, expressing
path independence along affine triangles. -/
theorem closedOneForm_segment_add
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    {a b c : E} {s : Set E}
    {ω : LinearOneForm 𝕜 E F}
    {dω : E → E →L[ℝ] E →L[𝕜] F}
    (hs : Convex ℝ s)
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hclosed : ∀ z ∈ s,
      ∀ x ∈ tangentConeAt ℝ s z,
      ∀ y ∈ tangentConeAt ℝ s z,
        dω z x y = dω z y x)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    (∫ᶜ x in Path.segment a b, ω x) +
        ∫ᶜ x in Path.segment b c, ω x =
      ∫ᶜ x in Path.segment a c, ω x :=
  hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
    hω hclosed ha hb hc

/-- Coordinate box used by the Bochner divergence theorem. -/
abbrev BoxPoint (n : ℕ) := Fin (n + 1) → ℝ

/-- Vector-valued field on a coordinate box. -/
abbrev BoxVector (n : ℕ) (E : Type*) := Fin (n + 1) → E

/-- Coordinate divergence computed from a Fréchet derivative. -/
def boxDivergence
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f' : BoxPoint n → BoxPoint n →L[ℝ] BoxVector n E)
    (x : BoxPoint n) : E :=
  ∑ i, f' x (Pi.single i 1) i

/-- Bochner divergence theorem on a rectangular box. -/
theorem boxDivergenceTheorem
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : BoxPoint n) (hle : a ≤ b)
    (f : BoxPoint n → BoxVector n E)
    (f' : BoxPoint n → BoxPoint n →L[ℝ] BoxVector n E)
    (singular : Set (BoxPoint n)) (hsingular : singular.Countable)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈
      (Set.pi Set.univ fun i => Ioo (a i) (b i)) \ singular,
        HasFDerivAt f (f' x) x)
    (hintegrable : IntegrableOn (boxDivergence f') (Icc a b)) :
    (∫ x in Icc a b, boxDivergence f' x) =
      ∑ i : Fin (n + 1),
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            f (i.insertNth (b i) x) i) -
          ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            f (i.insertNth (a i) x) i) := by
  simpa [boxDivergence] using
    MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
      a b hle f f' singular hsingular hcontinuous hderiv hintegrable

/-- If the total oriented boundary flux vanishes, then the integrated
divergence vanishes. -/
theorem integral_boxDivergence_eq_zero_of_boundary
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : BoxPoint n) (hle : a ≤ b)
    (f : BoxPoint n → BoxVector n E)
    (f' : BoxPoint n → BoxPoint n →L[ℝ] BoxVector n E)
    (singular : Set (BoxPoint n)) (hsingular : singular.Countable)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈
      (Set.pi Set.univ fun i => Ioo (a i) (b i)) \ singular,
        HasFDerivAt f (f' x) x)
    (hintegrable : IntegrableOn (boxDivergence f') (Icc a b))
    (hboundary :
      (∑ i : Fin (n + 1),
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            f (i.insertNth (b i) x) i) -
          ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            f (i.insertNth (a i) x) i)) = 0) :
    ∫ x in Icc a b, boxDivergence f' x = 0 := by
  rw [boxDivergenceTheorem a b hle f f' singular hsingular
    hcontinuous hderiv hintegrable, hboundary]

end Physlib.Mathematics.LovelockRund

end
