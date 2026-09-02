/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain
public import Mathlib.Topology.Algebra.Module.Simple
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Density of the Bender–Dunne time-of-arrival domain

The domain `D(T_{−1,1}) = {φ : ∫φ = 0 ∧ ∫qφ = 0}` (the two moment conditions of Bunao & Galapon,
arXiv:1509.00340, Eq. 11) is **dense** in `L²(ℝ)`. This module proves the general functional-analytic
mechanism behind that density and assembles it into the two-moment result for `benderDunneDomain`.

The engine is a textbook dichotomy: over a nontrivially normed field, a linear functional's kernel is either
closed or dense (`LinearMap.isClosed_or_dense_ker`), and it is closed exactly when the functional is continuous
(`LinearMap.continuous_iff_isClosed_ker`). Hence a **discontinuous** (unbounded) functional has a **dense** kernel.
Each moment `∫· , ∫q·` is unbounded on `L²(ℝ)` — its would-be Riesz representer (`1`, resp. `q`) is not in
`L²(ℝ)`, nor is any nonzero combination — so each moment condition already cuts out a dense subspace, and the
intersection is handled by iterating the argument inside the first kernel.

* **§A — the mechanism.** **`discontinuous_ker_dense`** (a discontinuous functional has dense kernel) and its
  closure form **`discontinuous_ker_topologicalClosure_eq_top`**.
* **§B — the two-moment intersection.** **`inter_ker_dense`** (`ker m₀ ∩ ker m₁` is dense when `m₀` is
  discontinuous and `m₁` is discontinuous *restricted to* `ker m₀`), via the dense-in-dense transfer
  `dense_subtype_map`.
* **§C — the Bender–Dunne domain.** **`benderDunneDomain_dense`** — `D(T_{−1,1}) = benderDunneDomain m₀ m₁` is
  dense in `L²(ℝ)` under the two unboundedness hypotheses.

**Honest layering — where the analysis sits.** The mechanism (§A–§C) is exact and unconditional. The two
hypotheses `¬Continuous m₀` and `¬Continuous (m₁ ∘ ker m₀ ↪)` are the genuine analytic content: they say the
moment functionals are unbounded, which for the concrete `∫·`, `∫q·` on `L²(ℝ)` holds because `1`, `q`, and every
nonzero combination `α·1 + β·q` fail to be square-integrable (no Riesz representer). Discharging them from scratch
requires exhibiting the unbounded sequences (or the divergence `∑ₙ|∫ψ₂ₙ|² = ∞` of the Hermite moments against the
`HermiteL2Basis` orthonormal basis); here they are carried as explicit hypotheses. The literal `∫·` is only a
*partial* functional on `L²` (defined on the Schwartz subdomain), so the theorem is stated for its realization as
a total functional — the standard model of an unbounded operator's form domain.

## References

* Bunao & Galapon, arXiv:1509.00340 (2015), Eq. 11. Completes the density behind
  `BenderDunneTimeOperatorDomain` and `BenderDunneOperatorAnalytic`, using the `HermiteL2Basis` keystone.


-/

set_option autoImplicit false

open Submodule

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneDensity

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]


/-- **The kernel of a discontinuous linear functional is dense.** Over a nontrivially normed field a functional's
kernel is closed or dense (`isClosed_or_dense_ker`), and closed iff the functional is continuous
(`continuous_iff_isClosed_ker`); so an unbounded functional cuts out a dense subspace. This is the reason each
Bender–Dunne moment condition `∫· = 0` defines a dense domain. -/
lemma discontinuous_ker_dense (l : E →ₗ[𝕜] 𝕜) (h : ¬ Continuous l) :
    Dense (LinearMap.ker l : Set E) :=
  l.isClosed_or_dense_ker.resolve_left fun hc => h (l.continuous_iff_isClosed_ker.mpr hc)

/-- **Closure form** `(ker l).topologicalClosure = ⊤` for a discontinuous functional `l`. -/
lemma discontinuous_ker_topologicalClosure_eq_top (l : E →ₗ[𝕜] 𝕜) (h : ¬ Continuous l) :
    (LinearMap.ker l).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp (discontinuous_ker_dense l h)


/-- **Dense-in-dense transfer.** If `W` is dense in `E` and `V` is dense in `W`, then the image of `V` in `E` is
dense — the closure of the image contains `W`, hence its closure `⊤`. -/
lemma dense_subtype_map {W : Submodule 𝕜 E} (hW : Dense (W : Set E))
    {V : Submodule 𝕜 W} (hV : Dense (V : Set W)) :
    Dense ((V.map W.subtype : Submodule 𝕜 E) : Set E) := by
  have himg : ((V.map W.subtype : Submodule 𝕜 E) : Set E) = W.subtype '' (V : Set W) := by
    simp [Submodule.map_coe]
  have key : (W : Set E) ⊆ closure (W.subtype '' (V : Set W)) := by
    have hsub : W.subtype '' closure (V : Set W) ⊆ closure (W.subtype '' (V : Set W)) :=
      image_closure_subset_closure_image continuous_subtype_val
    rw [hV.closure_eq] at hsub
    intro y hy
    exact hsub ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
  rw [himg, dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hW.closure_eq]
  exact closure_minimal key isClosed_closure

/-- **The two-moment kernel is dense** `ker m₀ ∩ ker m₁` — when `m₀` is discontinuous (so `ker m₀` is dense) and
`m₁` is discontinuous restricted to `ker m₀` (so the further condition still leaves a dense subspace inside
`ker m₀`). This iterates `discontinuous_ker_dense`: the second moment stays unbounded on the zeroth moment's
kernel. -/
lemma inter_ker_dense (m₀ m₁ : E →ₗ[𝕜] 𝕜) (h₀ : ¬ Continuous m₀)
    (h₁ : ¬ Continuous (m₁.comp (LinearMap.ker m₀).subtype)) :
    Dense ((LinearMap.ker m₀ ⊓ LinearMap.ker m₁ : Submodule 𝕜 E) : Set E) := by
  set W := LinearMap.ker m₀ with hWdef
  have hW : Dense (W : Set E) := discontinuous_ker_dense m₀ h₀
  have hV : Dense (LinearMap.ker (m₁.comp W.subtype) : Set W) :=
    discontinuous_ker_dense (m₁.comp W.subtype) h₁
  have hmap : (LinearMap.ker (m₁.comp W.subtype)).map W.subtype = W ⊓ LinearMap.ker m₁ := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
    · rintro ⟨hxW, hx1⟩; exact ⟨⟨x, hxW⟩, hx1, rfl⟩
  rw [← hmap]
  exact dense_subtype_map hW hV


/-- **The Bender–Dunne time-of-arrival domain is dense in `L²(ℝ)`** `D(T_{−1,1}) = {φ : ∫φ = 0 ∧ ∫qφ = 0}` — the
paper's density result (Eq. 11). Given the two moment functionals are unbounded (`m₀` discontinuous; `m₁`
discontinuous on `ker m₀`), `benderDunneDomain m₀ m₁ = ker m₀ ⊓ ker m₁` is dense. -/
lemma benderDunneDomain_dense (m₀ m₁ : E →ₗ[𝕜] 𝕜) (h₀ : ¬ Continuous m₀)
    (h₁ : ¬ Continuous (m₁.comp (LinearMap.ker m₀).subtype)) :
    Dense (benderDunneDomain m₀ m₁ : Set E) := by
  rw [benderDunneDomain]
  exact inter_ker_dense m₀ m₁ h₀ h₁

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneDensity
