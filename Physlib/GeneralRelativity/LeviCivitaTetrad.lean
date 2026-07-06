/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Levi-Civita connection and the canonical tetrad

The geometric core of the QM→GR bridge. The **Levi-Civita connection** is the unique metric-compatible,
**torsion-free** connection; its Christoffel symbols
`Γ_{λμν} = ½(∂_μ g_{νλ} + ∂_ν g_{μλ} − ∂_λ g_{μν})` are **symmetric** in the lower pair `μν` (vanishing torsion).
Canonical tetrad gravity encodes the metric through a frame field `e^a_μ` via the tetrad postulate
`g_{μν} = η_{ab} e^a_μ e^b_ν`, which is manifestly symmetric. These two facts — the symmetry of the connection
and of the tetrad-built metric — are the algebraic backbone on which the weak-field / Newtonian limit
(`ClockToGravity`) rests.

References: Levi-Civita; canonical tetrad (vierbein) gravity. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.GeneralRelativity.LeviCivitaTetrad

/-! ## The Levi-Civita connection is torsion-free -/

/-- **The Levi-Civita Christoffel symbol (lower indices)**
`Γ_{λμν} = ½(∂_μ g_{νλ} + ∂_ν g_{μλ} − ∂_λ g_{μν})`, built from the metric derivatives `dg i j k = ∂_i g_{jk}`. -/
noncomputable def christoffelLower {ι : Type*} (dg : ι → ι → ι → ℝ) (l a b : ι) : ℝ :=
  (dg a b l + dg b a l - dg l a b) / 2

/-- **The Levi-Civita connection is torsion-free** `Γ_{λμν} = Γ_{λνμ}`. For a symmetric metric
(`∂_i g_{jk} = ∂_i g_{kj}`) the Christoffel symbol is symmetric in its lower pair — the vanishing of torsion. -/
theorem christoffelLower_symm {ι : Type*} (dg : ι → ι → ι → ℝ)
    (hsym : ∀ i j k, dg i j k = dg i k j) (l a b : ι) :
    christoffelLower dg l a b = christoffelLower dg l b a := by
  unfold christoffelLower
  rw [hsym l a b]
  ring

/-! ## The canonical tetrad reproduces a symmetric metric -/

/-- **The tetrad metric** `g_{μν} = η_{ab} e^a_μ e^b_ν` — the metric built from a frame field `e` and the flat
fibre metric `η` (the tetrad postulate). -/
noncomputable def tetradMetric {ι κ : Type*} [Fintype ι] (η : ι → ι → ℝ) (e : ι → κ → ℝ) (μ ν : κ) : ℝ :=
  ∑ a, ∑ b, η a b * e a μ * e b ν

/-- **The tetrad-built metric is symmetric** `g_{μν} = g_{νμ}`. For a symmetric fibre metric `η_{ab} = η_{ba}` the
tetrad postulate `g = η(e,e)` yields a symmetric spacetime metric — the consistency of canonical tetrad gravity. -/
theorem tetradMetric_symm {ι κ : Type*} [Fintype ι] (η : ι → ι → ℝ) (e : ι → κ → ℝ)
    (hη : ∀ a b, η a b = η b a) (μ ν : κ) :
    tetradMetric η e μ ν = tetradMetric η e ν μ := by
  unfold tetradMetric
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hη y x]
  ring

end Physlib.GeneralRelativity.LeviCivitaTetrad

end
