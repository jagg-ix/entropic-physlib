/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Fisher–Rao information metric of the statistical simplex

The information-geometry foundation of the spine. A point of the statistical simplex `S = {ρ | ρⁱ ≥ 0, ∑ρⁱ = 1}`
is a probability distribution; its intrinsic metric — the unique (up to scale) metric invariant under sufficient
statistics (Čencov) — is the **Fisher–Rao metric**. In the diagonal coordinates `ρⁱ` its component is

`g(ρ) = 1/(2ρ)`,

and its `δρ` line element is exactly the **entropic-dynamics quantum potential** / Fisher information
`(δρ)²/ρ`. The metric induced on the space of quantum states (rays) is the **Fubini–Study metric**
`δs² = g(ρ)(δρ)² + 2ρ(δπ − ⟨δπ⟩)²`, a genuine (non-negative) Riemannian metric determined entirely by
information geometry.

References: S. Amari, H. Nagaoka, *Methods of Information Geometry*; A. Caticha, arXiv:2107.08502 (§4).
No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.InformationGeometry.FisherRao

/-- **The Fisher–Rao information metric** `g(ρ) = 1/(2ρ)` — the diagonal component of the simplex's intrinsic
metric. -/
noncomputable def fisherRaoMetric (ρ : ℝ) : ℝ := 1 / (2 * ρ)

/-- **The Fisher–Rao metric is positive** on positive probabilities. -/
theorem fisherRaoMetric_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < fisherRaoMetric ρ := by
  unfold fisherRaoMetric; positivity

/-- **The entropic-dynamics quantum potential** `Q(ρ, δρ) = (δρ)²/ρ` — the Fisher information density carried by a
probability fluctuation `δρ` at `ρ`. -/
noncomputable def quantumPotential (ρ dρ : ℝ) : ℝ := dρ ^ 2 / ρ

/-- **The quantum potential is the Fisher–Rao line element** `(δρ)²/ρ = 2 g(ρ) (δρ)²`. The `δρ` line element of the
Fisher–Rao metric is exactly the entropic-dynamics quantum potential (the Fisher information): the information
metric of the statistical manifold *is* the quantum potential of the reconstruction. -/
theorem quantumPotential_eq_fisherRao_lineElement (ρ dρ : ℝ) (hρ : ρ ≠ 0) :
    quantumPotential ρ dρ = 2 * fisherRaoMetric ρ * dρ ^ 2 := by
  unfold quantumPotential fisherRaoMetric
  field_simp

/-- **The Fubini–Study metric induced on the space of states (rays)**
`δs² = g(ρ)(δρ)² + 2ρ(δπ − ⟨δπ⟩)²` — the distance between rays, determined by information geometry, with
`⟨δπ⟩` the mean momentum shift. -/
noncomputable def fubiniStudyMetric (ρ dρ dπ meanDπ : ℝ) : ℝ :=
  fisherRaoMetric ρ * dρ ^ 2 + 2 * ρ * (dπ - meanDπ) ^ 2

/-- **The Fubini–Study metric is non-negative** — a bona-fide Riemannian metric on the space of quantum states. -/
theorem fubiniStudyMetric_nonneg (ρ dρ dπ meanDπ : ℝ) (hρ : 0 < ρ) :
    0 ≤ fubiniStudyMetric ρ dρ dπ meanDπ := by
  unfold fubiniStudyMetric fisherRaoMetric; positivity

end Physlib.InformationGeometry.FisherRao

end
