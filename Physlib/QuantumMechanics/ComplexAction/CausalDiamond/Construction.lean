/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
public import Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification

/-!
# The causal diamond, built from the complex-action timelike / spacelike / 45° structure

The Jacobson–Visser thermodynamics of `CausalDiamondThermodynamics` was stated for an *abstract* area
function `A : ℝ² → ℝ`. This file **constructs the causal diamond geometrically**, in the `(t, r)`
plane represented as `ℂ` (`Re = ` time, `Im = ` radius), reusing the complex-action/entropic-time causal structure already
in this repository:

* `lorentzianForm q = (Re q)² − (Im q)²` (`ComplexDelta.Convergence`) — the 2D Minkowski interval;
* `timelike` / `spacelike` / `timelikeFuture` / `timelikePast` (`Rapidity.FutureIncludedLorentzian`);
* `lightlike` — the **45°** null condition (`Rapidity.LightCone45RapidityUnification`).

A causal diamond is the intersection of the causal future of a past vertex `p` with the causal past of
a future vertex `p'` (Jacobson–Visser Fig. 1). For the canonical diamond the vertices are
`p = −R` (at `t = −R`, `r = 0`) and `p' = +R`, and:

* the **interior** is timelike-separated from both vertices (`center_mem_interior`);
* the **null boundary** `𝓗` is the 45° light cone of `p` (future) and `p'` (past) (`boundary_lightlike_45`);
* the **edge** `∂Σ` (the bifurcation surface) is where the two null cones meet, e.g. `q = iR`
  (`t = 0`, `r = R`) (`edge_point_mem`, `edge_lightlike_from_both`);
* the diamond is symmetric under reflection across `Σ` (`t → −t`), which swaps the vertices
  (`reflection_symmetry`);
* the flat conformal Killing vector `ζ` vanishes at the vertices and the edge — the fixed points of
  the conformal isometry that preserves the diamond (`confKilling_vanishes_vertices`,
  `confKilling_vanishes_edge`).

This realizes geometrically the timelike (interior) / spacelike (exterior) / 45° (boundary) trichotomy
that the abstract thermodynamics presupposed, and ties the diamond's causal interior to the
Nagao–Nielsen "permitted" contour cone `lorentzianForm > 0`.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, §2. This development: `Rapidity.FutureIncludedLorentzian`,
  `Rapidity.LightCone45RapidityUnification`, `ComplexDelta.Convergence`, `CausalDiamondThermodynamics`.

No new axioms.
-/

set_option autoImplicit false

open Complex

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction

open ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification

/-! ## §A — causal precedence and the diamond -/

/-- **The causal future** `J⁺(p)` of a point `p`: the closed forward light cone, i.e. all `q` with
`q − p` timelike-or-lightlike (`0 ≤ L(q − p)`) and future-directed (`0 ≤ Re(q − p)`). -/
def causalFuture (p : ℂ) : Set ℂ := {q | 0 ≤ lorentzianForm (q - p) ∧ 0 ≤ (q - p).re}

/-- **The causal past** `J⁻(p')` of a point `p'`: the closed backward light cone. -/
def causalPast (p' : ℂ) : Set ℂ := {q | 0 ≤ lorentzianForm (p' - q) ∧ 0 ≤ (p' - q).re}

/-- **The causal diamond** `D(p, p') = J⁺(p) ∩ J⁻(p')` — the domain of dependence of the ball whose
edge is the intersection of the future cone of `p` and the past cone of `p'` (Jacobson–Visser Fig. 1). -/
def causalDiamond (p p' : ℂ) : Set ℂ := causalFuture p ∩ causalPast p'

/-- **The open interior** of the diamond: strictly timelike-separated (future) from `p`, and strictly
timelike-separated (past) from `p'`. -/
def diamondInterior (p p' : ℂ) : Set ℂ :=
  {q | timelikeFuture (q - p) ∧ timelikeFuture (p' - q)}

/-- **The edge `∂Σ`** (bifurcation surface): the points that are simultaneously on the future null
cone of `p` and the past null cone of `p'`, where the two 45° boundaries meet. -/
def diamondEdge (p p' : ℂ) : Set ℂ :=
  {q | lightlike (q - p) ∧ lightlike (p' - q) ∧ 0 ≤ (q - p).re ∧ 0 ≤ (p' - q).re}

theorem mem_causalDiamond {p p' q : ℂ} :
    q ∈ causalDiamond p p' ↔
      (0 ≤ lorentzianForm (q - p) ∧ 0 ≤ (q - p).re) ∧
      (0 ≤ lorentzianForm (p' - q) ∧ 0 ≤ (p' - q).re) := Iff.rfl

/-! ## §B — interior, vertices, and the edge of the canonical diamond `p = −R`, `p' = R` -/

/-- **The interior is contained in the diamond** (strict timelike ⟹ closed causal). -/
theorem interior_subset_diamond (p p' : ℂ) : diamondInterior p p' ⊆ causalDiamond p p' := by
  intro q hq
  obtain ⟨⟨hL1, hr1⟩, ⟨hL2, hr2⟩⟩ := hq
  exact ⟨⟨le_of_lt hL1, le_of_lt hr1⟩, ⟨le_of_lt hL2, le_of_lt hr2⟩⟩

/-- **The center is in the interior** `0 ∈ I(−R, R)`: the origin is strictly timelike-separated
(future) from `p = −R` and (past) from `p' = R`, since `0 − (−R) = R = R − 0` is future timelike
(`L(R) = R² > 0`, `Re R = R > 0`). The deepest point of the diamond. -/
theorem center_mem_interior {R : ℝ} (hR : 0 < R) :
    (0 : ℂ) ∈ diamondInterior (-(R : ℂ)) (R : ℂ) := by
  have hL : lorentzianForm (R : ℂ) = R ^ 2 := by
    simp [lorentzianForm]
  constructor
  · refine ⟨?_, ?_⟩
    · show 0 < lorentzianForm (0 - -(R : ℂ))
      rw [zero_sub, neg_neg, hL]; positivity
    · show 0 < (0 - -(R : ℂ)).re
      rw [zero_sub, neg_neg]; simpa using hR
  · refine ⟨?_, ?_⟩
    · show 0 < lorentzianForm ((R : ℂ) - 0)
      rw [sub_zero, hL]; positivity
    · show 0 < ((R : ℂ) - 0).re
      rw [sub_zero]; simpa using hR

/-- **The center is in the diamond** (corollary). -/
theorem center_mem_diamond {R : ℝ} (hR : 0 < R) :
    (0 : ℂ) ∈ causalDiamond (-(R : ℂ)) (R : ℂ) :=
  interior_subset_diamond _ _ (center_mem_interior hR)

/-- **The past vertex `p = −R` lies in the closed diamond.** -/
theorem past_vertex_mem_diamond {R : ℝ} (hR : 0 < R) :
    (-(R : ℂ)) ∈ causalDiamond (-(R : ℂ)) (R : ℂ) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show 0 ≤ lorentzianForm (-(R : ℂ) - -(R : ℂ)); simp [lorentzianForm]
  · show 0 ≤ (-(R : ℂ) - -(R : ℂ)).re; simp
  · show 0 ≤ lorentzianForm ((R : ℂ) - -(R : ℂ))
    have : (R : ℂ) - -(R : ℂ) = (2 * R : ℝ) := by push_cast; ring
    rw [this]; simp [lorentzianForm]; positivity
  · show 0 ≤ ((R : ℂ) - -(R : ℂ)).re
    have : (R : ℂ) - -(R : ℂ) = (2 * R : ℝ) := by push_cast; ring
    rw [this]; simp; positivity

/-- **The edge point `q = iR` lies on the bifurcation surface `∂Σ`** (`t = 0`, `r = R`): it is on the
future null cone of `p = −R` *and* the past null cone of `p' = R`. This is the corner where the two
45° boundaries meet — the spacelike edge of the ball `Σ`. -/
theorem edge_point_mem {R : ℝ} (hR : 0 < R) :
    (Complex.I * R) ∈ diamondEdge (-(R : ℂ)) (R : ℂ) := by
  have hp : Complex.I * R - -(R : ℂ) = (R : ℂ) + Complex.I * R := by ring
  have hf : (R : ℂ) - Complex.I * R = (R : ℂ) - Complex.I * R := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show lightlike (Complex.I * R - -(R : ℂ))
    rw [lightlike, hp]; simp [lorentzianForm]
  · show lightlike ((R : ℂ) - Complex.I * R)
    rw [lightlike]; simp [lorentzianForm]
  · show 0 ≤ (Complex.I * R - -(R : ℂ)).re
    rw [hp]; simp; positivity
  · show 0 ≤ ((R : ℂ) - Complex.I * R).re
    simp; positivity

/-- **Edge points are lightlike from both vertices** — restating the defining property of `∂Σ`: the
edge is the locus where `q − p` and `p' − q` are *both* null (45°), i.e. the bifurcation surface of
the conformal Killing horizon. -/
theorem edge_lightlike_from_both {p p' q : ℂ} (hq : q ∈ diamondEdge p p') :
    lightlike (q - p) ∧ lightlike (p' - q) := ⟨hq.1, hq.2.1⟩

/-- **The edge is contained in the diamond** (null ⟹ causal). -/
theorem edge_subset_diamond (p p' : ℂ) : diamondEdge p p' ⊆ causalDiamond p p' := by
  intro q hq
  obtain ⟨hl1, hl2, hr1, hr2⟩ := hq
  rw [lightlike] at hl1 hl2
  exact ⟨⟨le_of_eq hl1.symm, hr1⟩, ⟨le_of_eq hl2.symm, hr2⟩⟩

/-! ## §C — reflection symmetry across `Σ` (the `t → −t` isometry) -/

/-- **Reflection across the maximal slice `Σ`** `σ(q) = −\overline{q}` (`t → −t`, `r → r`): the
isometry of the diamond that swaps the two vertices. -/
def slicereflect (q : ℂ) : ℂ := -(starRingEnd ℂ q)

@[simp] theorem slicereflect_ofReal (R : ℝ) : slicereflect (R : ℂ) = -(R : ℂ) := by
  simp [slicereflect]

/-- **The diamond is symmetric under reflection across `Σ`** (Jacobson–Visser §2: "reflection across
`Σ`"). The reflection `σ(q) = −\overline q` swaps the future cone of `p = −R` with the past cone of
`p' = R`, so it maps the diamond onto itself. -/
theorem reflection_symmetry {R : ℝ} (q : ℂ) :
    q ∈ causalDiamond (-(R : ℂ)) (R : ℂ) ↔
      slicereflect q ∈ causalDiamond (-(R : ℂ)) (R : ℂ) := by
  have key1 : (R : ℂ) - slicereflect q = starRingEnd ℂ (q - -(R : ℂ)) := by
    simp [slicereflect, map_add]; ring
  have key2 : slicereflect q - -(R : ℂ) = starRingEnd ℂ ((R : ℂ) - q) := by
    simp [slicereflect, map_sub]; ring
  constructor
  · rintro ⟨⟨hL1, hr1⟩, ⟨hL2, hr2⟩⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [key2, lorentzianForm_conj]; exact hL2
    · rw [key2, Complex.conj_re]; exact hr2
    · rw [key1, lorentzianForm_conj]; exact hL1
    · rw [key1, Complex.conj_re]; exact hr1
  · rintro ⟨⟨hL1, hr1⟩, ⟨hL2, hr2⟩⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← lorentzianForm_conj (q - -(R : ℂ)), ← key1]; exact hL2
    · rw [show (q - -(R : ℂ)).re = ((R : ℂ) - slicereflect q).re by rw [key1, Complex.conj_re]]
      exact hr2
    · rw [← lorentzianForm_conj ((R : ℂ) - q), ← key2]; exact hL1
    · rw [show ((R : ℂ) - q).re = (slicereflect q - -(R : ℂ)).re by rw [key2, Complex.conj_re]]
      exact hr1

/-! ## §D — the null boundary is the 45° cone; the interior is the permitted contour cone -/

/-- **The future null boundary is the 45° light cone** of `p`: a point on the future boundary `𝓗⁺`
satisfies the 45° condition `|Re(q − p)| = |Im(q − p)|` (equal legs, slope `±1`). Ties the diamond's
null boundary to `Rapidity.LightCone45RapidityUnification`. -/
theorem boundary_lightlike_45 {p q : ℂ} (h : lightlike (q - p)) :
    |(q - p).re| = |(q - p).im| := (lightlike_iff_abs_eq (q - p)).mp h

/-- **The interior is the permitted (timelike) contour cone**: every interior point is timelike from
`p`, i.e. lies in `lorentzianForm > 0` — the Nagao–Nielsen "permitted" convergence cone used for the
complex-action contour (`ComplexDelta.Contour`). The diamond's causal interior *is* the complex-action timelike
cone. -/
theorem interior_timelike {p p' q : ℂ} (hq : q ∈ diamondInterior p p') :
    timelike (q - p) := hq.1.1

/-- **The edge is not interior** — it is genuinely the boundary: a null (lightlike) separation is not
strictly timelike, so `∂Σ ∩ I(p,p') = ∅`. -/
theorem edge_not_interior {p p' q : ℂ} (hq : q ∈ diamondEdge p p') :
    q ∉ diamondInterior p p' := by
  intro hint
  have h0 : lorentzianForm (q - p) = 0 := hq.1
  have hpos : 0 < lorentzianForm (q - p) := hint.1.1
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-! ## §E — the flat conformal Killing vector vanishes at the fixed points -/

/-- **Time component of the flat conformal Killing vector** `ζ^t = R² − t² − r²` (Jacobson–Visser
Eq. 2.6 in the flat limit `L → ∞`; the modular flow generator of the diamond). -/
def confKillingTime (R t r : ℝ) : ℝ := R ^ 2 - t ^ 2 - r ^ 2

/-- **Radial component of the flat conformal Killing vector** `ζ^r = −2 t r`. -/
def confKillingRad (R t r : ℝ) : ℝ := -2 * t * r

/-- **The conformal Killing vector vanishes at the two vertices** `p = (∓R, 0)` (Jacobson–Visser §2:
`ζ` "leaves fixed the vertices"). Both components are zero at `t = ±R`, `r = 0`. -/
theorem confKilling_vanishes_vertices (R : ℝ) :
    (confKillingTime R R 0 = 0 ∧ confKillingRad R R 0 = 0) ∧
    (confKillingTime R (-R) 0 = 0 ∧ confKillingRad R (-R) 0 = 0) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [confKillingTime, confKillingRad] <;> ring

/-- **The conformal Killing vector vanishes on the edge** `∂Σ` `= (0, R)` (Jacobson–Visser §2: `ζ`
"vanishes at `∂Σ`"). Both components are zero at `t = 0`, `r = R`: the edge is the bifurcation surface
fixed by the conformal flow. -/
theorem confKilling_vanishes_edge (R : ℝ) :
    confKillingTime R 0 R = 0 ∧ confKillingRad R 0 R = 0 := by
  constructor <;> simp [confKillingTime, confKillingRad] <;> ring

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction

end
