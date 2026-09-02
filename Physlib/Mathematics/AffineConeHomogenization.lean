/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Homogenization of affine half-space intersections into a cone

Ports the verified homogenization core (§1) of
`CATEPTMain/Integration/EnergyTensorConeLane.lean` (reference tree, own authorship; adapted
there from the `energy-tensor-cone` study, Zenodo DOI 10.5281/zenodo.18522456).

Averaged quantum energy inequalities (AQEIs) constrain a stress-energy configuration `x` by
*affine* half-spaces: `I(T,γ) ≥ −B(γ)` becomes `0 ≤ L_i x + b_i` with `L_i` the smeared
functional and `b_i ≥ 0` the Fewster-type bound.  The admissible set

  `AffineAdmissible L b = {x | ∀ i, 0 ≤ L_i x + b_i}`

is closed, convex, and (when nonempty) path-connected — but **not** a cone: the inhomogeneous
bounds `b_i` do not scale with `x`.  The classical algebraic-geometry remedy is to homogenize
into one dimension higher,

  `HomCone L b = {(x,t) | 0 ≤ t ∧ ∀ i, 0 ≤ L_i x + t·b_i} ⊆ E × ℝ`,

which *is* a genuine cone (`homCone_smul_nonneg`), closed and convex, containing the original
admissible set as its `t = 1` slice (`slice_one_iff`).  This is the structure that makes the
AQEI constraint geometry amenable to conic optimization.

**Honest layering.**  Exact convex analysis on Mathlib carriers.  The source file's §§2–6 are
deliberately not ported: its `LorentzSpace`/stress-energy layer duplicates physlib's
relativity carriers, and its extreme-point and aqei-bridge sections are `True`-stub references
to an external computation.

## References

* C. J. Fewster, *Lectures on quantum energy inequalities*, arXiv:1208.5399.
* Source: `CATEPTMain/Integration/EnergyTensorConeLane.lean` §1 (reference tree, own
  authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Mathematics.AffineConeHomogenization

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable {ι : Type*}

/-- **The affine admissible set** `{x | ∀ i, 0 ≤ L_i x + b_i}` — the natural shape of AQEI
constraints, with `L_i` the smeared stress-energy functionals and `b_i` the inhomogeneous
bounds.  Closed and convex, but *not* a cone: scaling `x ↦ αx` for `α > 1` can violate the
constraints because the `b_i` do not scale. -/
def AffineAdmissible (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i : ι, 0 ≤ (L i) x + b i}

/-- **The homogenized cone** in `E × ℝ`: `{(x,t) | 0 ≤ t ∧ ∀ i, 0 ≤ L_i x + t·b_i}` — the
affine set embedded as the `t = 1` slice of a genuine cone one dimension higher. -/
def HomCone (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : Set (E × ℝ) :=
  {p | 0 ≤ p.2 ∧ ∀ i : ι, 0 ≤ (L i) p.1 + p.2 * b i}

/-- The affine admissible set is closed: an intersection of closed affine half-spaces. -/
theorem affineAdmissible_isClosed (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    IsClosed (AffineAdmissible (E := E) L b) := by
  have hi : ∀ i : ι, IsClosed {x : E | 0 ≤ (L i) x + b i} := fun i =>
    isClosed_Ici.preimage ((L i).continuous.add continuous_const)
  have hset : AffineAdmissible (E := E) L b = ⋂ i : ι, {x : E | 0 ≤ (L i) x + b i} := by
    ext x
    simp [AffineAdmissible]
  simpa [hset] using isClosed_iInter hi

/-- The affine admissible set is convex. -/
theorem affineAdmissible_convex (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    Convex ℝ (AffineAdmissible (E := E) L b) := by
  have hi : ∀ i : ι, Convex ℝ {x : E | 0 ≤ (L i) x + b i} := by
    intro i x hx y hy a c ha hc hac
    have key : a * b i + c * b i = b i := by rw [← add_mul, hac, one_mul]
    have h1 : 0 ≤ a * ((L i) x + b i) := mul_nonneg ha hx
    have h2 : 0 ≤ c * ((L i) y + b i) := mul_nonneg hc hy
    show 0 ≤ (L i) (a • x + c • y) + b i
    have hlin : (L i) (a • x + c • y) = a * (L i) x + c * (L i) y := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hlin, ← key]
    nlinarith
  have hset : AffineAdmissible (E := E) L b = ⋂ i : ι, {x : E | 0 ≤ (L i) x + b i} := by
    ext x
    simp [AffineAdmissible]
  simpa [hset] using convex_iInter hi

/-- **The slice relation**: the affine admissible set is exactly the `t = 1` cross-section of
the homogenized cone. -/
theorem slice_one_iff (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (x : E) :
    x ∈ AffineAdmissible (E := E) L b ↔ (x, (1 : ℝ)) ∈ HomCone (E := E) L b := by
  constructor
  · intro hx
    exact ⟨by norm_num, fun i => by simpa using hx i⟩
  · intro hx i
    simpa using hx.2 i

/-- The homogenized cone is closed. -/
theorem homCone_isClosed (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    IsClosed (HomCone (E := E) L b) := by
  have h0 : IsClosed {p : E × ℝ | 0 ≤ p.2} := isClosed_Ici.preimage continuous_snd
  have hi : ∀ i : ι, IsClosed {p : E × ℝ | 0 ≤ (L i) p.1 + p.2 * b i} := fun i =>
    isClosed_Ici.preimage
      (((L i).continuous.comp continuous_fst).add (continuous_snd.mul continuous_const))
  have hset : HomCone (E := E) L b
      = {p | 0 ≤ p.2} ∩ ⋂ i : ι, {p | 0 ≤ (L i) p.1 + p.2 * b i} := by
    ext p
    simp [HomCone, Set.mem_iInter]
  simpa [hset] using h0.inter (isClosed_iInter hi)

/-- The homogenized cone is convex. -/
theorem homCone_convex (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    Convex ℝ (HomCone (E := E) L b) := by
  intro p hp q hq a c ha hc hac
  have ht : (a • p + c • q).2 = a * p.2 + c * q.2 := by simp
  have hf : (a • p + c • q).1 = a • p.1 + c • q.1 := by simp
  constructor
  · rw [ht]
    exact add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hc hq.1)
  · intro i
    rw [hf, ht]
    simp only [map_add, map_smul, smul_eq_mul]
    have h1 := hp.2 i
    have h2 := hq.2 i
    nlinarith

/-- **The homogenized set is a genuine cone**: closed under nonnegative scaling — exactly the
property the affine admissible set lacks. -/
theorem homCone_smul_nonneg (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (p : E × ℝ) (α : ℝ) (hp : p ∈ HomCone (E := E) L b) (hα : 0 ≤ α) :
    (α • p) ∈ HomCone (E := E) L b := by
  have ht : (α • p).2 = α * p.2 := by simp
  have hf : (α • p).1 = α • p.1 := by simp
  constructor
  · rw [ht]
    exact mul_nonneg hα hp.1
  · intro i
    rw [hf, ht, map_smul, smul_eq_mul]
    nlinarith [hp.2 i]

/-- The affine admissible set, when nonempty, is path-connected — the AQEI constraint
geometry is one well-behaved piece. -/
theorem affineAdmissible_pathConnected [ContinuousAdd E] [ContinuousSMul ℝ E]
    (L : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (hne : (AffineAdmissible (E := E) L b).Nonempty) :
    IsPathConnected (AffineAdmissible (E := E) L b) :=
  (affineAdmissible_convex L b).isPathConnected hne

end Physlib.Mathematics.AffineConeHomogenization

end
