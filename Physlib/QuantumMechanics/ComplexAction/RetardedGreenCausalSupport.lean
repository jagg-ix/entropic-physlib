/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
meta import Zil

/-!
# Finite causal propagation: `supp(G⁺f) ⊆ J⁺(supp f)`

The finite-propagation axiom requires that a retarded field sourced by `f` is
supported inside the causal future of the source's support,
`supp(G⁺f) ⊆ J⁺(supp f)`.  The repository proved this only *pointwise*
(`retarded_in_causalFuture`: a single retarded argument lies on the future cone).

It is first proved at the causal-set level natural to the Sorkin--Johnston
construction, for `φ(x) = ∑_y G_ret(x,y) f(y)`.  The second section removes the
finite-source restriction and proves the same inclusion for the genuine Bochner
integral `φ(x) = ∫ G_ret(x,y) f(y) dμ(y)` over an arbitrary measure space.
This is continuum measure-level propagation; distribution-valued wavefront-set
control and globally-hyperbolic PDE existence remain separate analytic results.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen

variable {α : Type*}

/-- **The causal future of a set** under the causal order `later`: the points that
are later than some point of `S` (`J⁺(S) = {x | ∃ y ∈ S, later x y}`). -/
def causalFutureOf (later : α → α → Prop) (S : Set α) : Set α :=
  {x | ∃ y ∈ S, later x y}

/-- **The retarded response** of a source `f` under the causal Green kernel `G`:
`φ(x) = ∑_y G_ret(x,y)·f(y)`, the field produced at `x` by the source. -/
def retardedResponse [Fintype α] (G : α → α → ℝ) (later : α → α → Prop)
    [DecidableRel later] (f : α → ℝ) (x : α) : ℝ :=
  ∑ y, retardedGreen G later x y * f y

/-- **The retarded Green vanishes outside the causal future**: if `G_ret(x,y) ≠ 0`
then `x` is later than `y`. -/
@[zil_level structural]
theorem retardedGreen_ne_zero_imp_later (G : α → α → ℝ) (later : α → α → Prop)
    [DecidableRel later] {x y : α} (h : retardedGreen G later x y ≠ 0) : later x y := by
  by_contra hlt
  rw [retardedGreen, if_neg hlt] at h
  exact h rfl

/-- **Finite causal propagation — `supp(G⁺f) ⊆ J⁺(supp f)`.**  The retarded
response of a source is supported in the causal future of the source's support:
the field can be nonzero only at points causally later than some point where the
source is nonzero.  This is the support-over-sources form of finite causal
propagation, not merely the pointwise future-cone membership of a single argument. -/
@[zil_level bridge_theorem]
theorem retardedResponse_support_subset_causalFuture [Fintype α]
    (G : α → α → ℝ) (later : α → α → Prop) [DecidableRel later] (f : α → ℝ) :
    Function.support (retardedResponse G later f)
      ⊆ causalFutureOf later (Function.support f) := by
  intro x hx
  rw [Function.mem_support, retardedResponse] at hx
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  rw [mul_ne_zero_iff] at hy
  exact ⟨y, Function.mem_support.mpr hy.2, retardedGreen_ne_zero_imp_later G later hy.1⟩

/-- **The retarded response is empty for an empty source.**  A vanishing source
produces no field — the non-vacuity companion showing the causal-future bound is
not vacuously about the empty support only. -/
@[zil_level structural]
theorem retardedResponse_zero [Fintype α] (G : α → α → ℝ) (later : α → α → Prop)
    [DecidableRel later] : retardedResponse G later (0 : α → ℝ) = 0 := by
  funext x
  simp [retardedResponse]

/-! ## Continuum measure-theoretic propagation -/

/-- **Continuum retarded response.**  This is the Bochner integral analogue of
`retardedResponse`: `φ(x) = ∫ G_ret(x,y) f(y) dμ(y)`.  The source space may be
infinite and the measure arbitrary. -/
noncomputable def retardedIntegralResponse [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (G : α → α → ℝ)
    (later : α → α → Prop) [DecidableRel later]
    (f : α → ℝ) (x : α) : ℝ :=
  ∫ y, retardedGreen G later x y * f y ∂μ

/-- Outside the causal future of the source support, the complete retarded
integrand vanishes pointwise.  Hence no integrability side condition is needed
to prove that the Bochner response vanishes there. -/
@[zil_level structural]
theorem retardedIntegralResponse_eq_zero_of_not_mem_causalFuture
    [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (G : α → α → ℝ) (later : α → α → Prop) [DecidableRel later]
    (f : α → ℝ) {x : α}
    (hx : x ∉ causalFutureOf later (Function.support f)) :
    retardedIntegralResponse μ G later f x = 0 := by
  have hintegrand : (fun y => retardedGreen G later x y * f y) = 0 := by
    funext y
    by_cases hxy : later x y
    · have hfy : f y = 0 := by
        by_contra hne
        exact hx ⟨y, Function.mem_support.mpr hne, hxy⟩
      simp [retardedGreen, hxy, hfy]
    · simp [retardedGreen, hxy]
  simp [retardedIntegralResponse, hintegrand]

/-- **Continuum finite causal propagation.**  For an arbitrary measure space,
the Bochner-integrated retarded response satisfies the exact support inclusion
`supp(G⁺f) ⊆ J⁺(supp f)`.  This removes the finite-source/Fintype restriction of
`retardedResponse_support_subset_causalFuture`. -/
@[zil_level bridge_theorem]
theorem retardedIntegralResponse_support_subset_causalFuture
    [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (G : α → α → ℝ) (later : α → α → Prop) [DecidableRel later]
    (f : α → ℝ) :
    Function.support (retardedIntegralResponse μ G later f)
      ⊆ causalFutureOf later (Function.support f) := by
  intro x hx
  by_contra hcausal
  exact hx (retardedIntegralResponse_eq_zero_of_not_mem_causalFuture
    μ G later f hcausal)

/-- A zero continuum source has zero retarded response. -/
@[zil_level structural]
theorem retardedIntegralResponse_zero [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (G : α → α → ℝ)
    (later : α → α → Prop) [DecidableRel later] :
    retardedIntegralResponse μ G later (0 : α → ℝ) = 0 := by
  funext x
  simp [retardedIntegralResponse]

end Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen

zil attach retardedResponse_support_subset_causalFuture where
  formalizes @ "claim:the-retarded-response-of-a-source-is-supported-in-the-causal-future-of-the-source-support-supp-g-ret-f-subset-j-plus-supp-f",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedGreen",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-causal-set-discrete-support-inclusion-not-the-continuum-distributional-convolution-support"

zil attach retardedGreen_ne_zero_imp_later where
  formalizes @ "claim:the-retarded-green-kernel-vanishes-outside-the-causal-future-of-its-source-argument"

zil attach retardedIntegralResponse_support_subset_causalFuture where
  formalizes @ "claim:on-an-arbitrary-measure-space-the-Bochner-integrated-retarded-response-is-supported-in-the-causal-future-of-the-source-support-supp-g-ret-f-subset-j-plus-supp-f",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedGreen_ne_zero_imp_later",
  epistemic_status @ "consistency-identity",
  caveat @ "scope:continuum-measure-Bochner-support-theorem-not-the-stronger-distribution-valued-wavefront-set-or-globally-hyperbolic-PDE-existence-theorem"

zil attach retardedIntegralResponse_eq_zero_of_not_mem_causalFuture where
  supported_by @ "lean:retardedResponse_support_subset_causalFuture",
  formalizes @ "claim:outside-the-causal-future-of-the-source-support-the-continuum-retarded-integrand-and-therefore-its-Bochner-integral-vanish"

zil_file_contract physlib.retardedGreenCausalSupport where
  promises "The retarded response of a source under the causal Green kernel is supported in the causal future of the source's support: supp(G_ret f) is contained in J-plus of supp f, since the retarded Green kernel G_ret(x,y) = [x later than y] G(x,y) vanishes unless x is causally later than y. The theorem is proved both for the finite causal-set sum and for a genuine Bochner integral over an arbitrary measure space; in both cases a vanishing source produces no field."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedGreen"
  ]
  forbids_substitutes [
    "claiming the stronger distribution-valued wavefront-set theorem from the measure-level Bochner support result alone",
    "reading the discrete causal-set order as a metric light cone"
  ]
  witnessed_by [
    retardedGreen_ne_zero_imp_later,
    retardedResponse_support_subset_causalFuture,
    retardedResponse_zero,
    retardedIntegralResponse_eq_zero_of_not_mem_causalFuture,
    retardedIntegralResponse_support_subset_causalFuture,
    retardedIntegralResponse_zero
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.retardedGreenCausalSupport
