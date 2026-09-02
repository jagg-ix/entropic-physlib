/-
Copyright (c) 2026 Physlib Contributors.
Released under Apache 2.0 license.
Authors: Physlib Contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# Tube Domains in Several Complex Variables

This module contains the elementary tube-domain facts used by analytic
continuation arguments in Wightman and Osterwalder-Schrader reconstruction.

## Main definitions

* `Physlib.SCV.TubeDomain` is the tube `T(C) = {z : C^m | Im z in C}`.
* `Physlib.SCV.realSubspace` is the real boundary plane of `C^m`.
* `Physlib.SCV.realEmbed` is the coordinatewise embedding `R^m -> C^m`.

## Main results

* `Physlib.SCV.tubeDomain_isOpen`
* `Physlib.SCV.tubeDomain_isPreconnected`
* `Physlib.SCV.bochner_tube_extension`

## References

* S. Bochner, "A theorem on analytic continuation of functions in several
  variables", Annals of Mathematics 39(1), 14-19, 1938.
* L. Hormander, *An Introduction to Complex Analysis in Several Variables*,
  Theorem 2.5.10.
-/

@[expose] public noncomputable section

open Complex Topology Set

namespace Physlib.SCV

/-! ## A. Tube Domains -/

/-- The tube domain `T(C) = { z in C^m : Im z in C }`. -/
def TubeDomain {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  {z | (fun i => (z i).im) ∈ C}

/-- The real boundary plane in `C^m`. -/
def realSubspace (m : ℕ) : Set (Fin m → ℂ) :=
  {z | ∀ i, (z i).im = 0}

/-- The coordinatewise embedding `R^m -> C^m`. -/
def realEmbed {m : ℕ} (x : Fin m → ℝ) : Fin m → ℂ :=
  fun i => (x i : ℂ)

/-- A tube domain over an open real base is open. -/
lemma tubeDomain_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (TubeDomain C) :=
  hC.preimage (continuous_pi fun i => Complex.continuous_im.comp (continuous_apply i))

/-- The tube domain over a convex real base is convex as a real subset of `C^m`. -/
lemma tubeDomain_convex {m : ℕ} {C : Set (Fin m → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ (TubeDomain C) := by
  intro z hz w hw a b ha hb hab
  show (fun i => ((a • z + b • w) i).im) ∈ C
  have him :
      (fun i => ((a • z + b • w) i).im) =
        a • (fun i => (z i).im) + b • (fun i => (w i).im) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      smul_eq_mul]
  rw [him]
  exact hC hz hw ha hb hab

/-- A tube domain over a convex nonempty real base is preconnected. -/
lemma tubeDomain_isPreconnected {m : ℕ} {C : Set (Fin m → ℝ)}
    (hC : Convex ℝ C) (_hne : C.Nonempty) :
    IsPreconnected (TubeDomain C) :=
  (tubeDomain_convex hC).isPreconnected

/-! ## B. Convex Hull Base -/

/-- In finite dimensions the convex hull of an open set is open. -/
lemma isOpen_convexHull_of_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (convexHull ℝ C) := by
  have hsubset : C ⊆ interior (convexHull ℝ C) :=
    hC.subset_interior_iff.mpr (subset_convexHull ℝ C)
  have hconv : Convex ℝ (interior (convexHull ℝ C)) :=
    (convex_convexHull ℝ C).interior
  have hle : convexHull ℝ C ⊆ interior (convexHull ℝ C) :=
    convexHull_min hsubset hconv
  rw [show convexHull ℝ C = interior (convexHull ℝ C) from
    Set.Subset.antisymm hle interior_subset]
  exact isOpen_interior

/-- `T(C)` is contained in `T(conv C)`. -/
lemma tubeDomain_subset_convexHull {m : ℕ} {C : Set (Fin m → ℝ)} :
    TubeDomain C ⊆ TubeDomain (convexHull ℝ C) :=
  fun _ hz => subset_convexHull ℝ C hz

/-- The tube over the convex hull of an open base is open. -/
lemma tubeDomain_convexHull_isOpen {m : ℕ} {C : Set (Fin m → ℝ)} (hC : IsOpen C) :
    IsOpen (TubeDomain (convexHull ℝ C)) :=
  tubeDomain_isOpen (isOpen_convexHull_of_isOpen hC)

/-- The tube over the convex hull of a nonempty open base is connected. -/
lemma tubeDomain_convexHull_isConnected {m : ℕ} {C : Set (Fin m → ℝ)}
    (_hC : IsOpen C) (hne : C.Nonempty) :
    IsConnected (TubeDomain (convexHull ℝ C)) := by
  constructor
  · obtain ⟨y, hy⟩ := hne
    refine ⟨fun i => (0 : ℂ) + (y i : ℂ) * I, ?_⟩
    show (fun i => (((0 : ℂ) + (y i : ℂ) * I).im)) ∈ convexHull ℝ C
    have hyim : (fun i => (((0 : ℂ) + (y i : ℂ) * I).im)) = y := by
      ext i
      simp [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
    rw [hyim]
    exact subset_convexHull ℝ C hy
  · exact tubeDomain_isPreconnected (convex_convexHull ℝ C)
      (hne.mono (subset_convexHull ℝ C))

/-! ## C. Bochner Extension for Convex Tube Bases -/

/-- Bochner extension over a convex tube base.

When the real base `C` is already convex, `convexHull R C = C`; hence a
holomorphic function on `T(C)` is already a holomorphic function on
`T(conv C)`. This is the exact convex-base case used by cone-domain transport.
-/
lemma bochner_tube_extension {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC_conv : Convex ℝ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C)) :
    ∃ F_ext : (Fin m → ℂ) → ℂ,
      DifferentiableOn ℂ F_ext (TubeDomain (convexHull ℝ C)) ∧
        ∀ z ∈ TubeDomain C, F_ext z = F z := by
  refine ⟨F, ?_, ?_⟩
  · simpa [hC_conv.convexHull_eq] using hF
  · intro z _hz
    rfl

end Physlib.SCV

end
