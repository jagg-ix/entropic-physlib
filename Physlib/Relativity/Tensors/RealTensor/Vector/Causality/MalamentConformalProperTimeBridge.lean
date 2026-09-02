/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeAlexandrovZeeman
public import Physlib.Relativity.Special.ProperTime
meta import Zil

/-!
# Malament closure: the metric-rigidity iff and proper time under causal automorphisms

The deep geometric reduction of the Alexandrov–Zeeman converse is now complete: the
null-cone metric rigidity `same_null_cone_proportional` and the full affine classification
`affine_causalAutomorphism_eq_translation_dilation_lorentz` (every affine causal automorphism
is `x ↦ √c·g(x) + e 0` with `g` Lorentz and `√c` a positive dilation) are proved without any
conformality premise.  This module links those results to the causal-structure and
proper-time formalizations.

* `same_null_cone_iff_proportional` — closes Malament's rigidity to a genuine **iff** by
  adjoining the sufficiency direction (a nonzero rescaling preserves the null cone) to the
  necessity `same_null_cone_proportional`: a symmetric continuous bilinear form has the same
  null cone as `η` *iff* it is a nonzero scalar multiple of `η`.

* `properTime_causalAutomorphism` — evaluates proper time under the classification: a causal
  automorphism scales proper time by exactly its dilation factor `√c`,
  `τ(e q, e p) = √c · τ(q, p)`.  The Lorentz and translation parts leave proper time
  invariant (extending `ProperTimeLorentzInvariance.properTime_lorentz_invariant`); only the
  dilation rescales it.  So the causal order fixes proper time — and the metric — exactly up
  to the conformal factor `√c`, the concrete content of Malament's theorem.

* `causalAutomorphism_decomposition_with_properTime` — exposes the Lorentz map, translation,
  positive dilation, and proper-time scaling with one shared witness.  Downstream physical
  calibration can therefore remove the dilation without reconstructing the geometric proof.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace SpaceTime

/-! ## The full Malament metric-rigidity iff -/

/-- **Malament metric rigidity, as an iff.**  A symmetric continuous bilinear form has the
same null cone as the Minkowski form iff it is a nonzero scalar multiple of it — the
necessity is `same_null_cone_proportional`; the sufficiency is that a nonzero rescaling
preserves the zero set. -/
@[zil_level bridge_theorem]
theorem same_null_cone_iff_proportional (B : Vector 3 →L[ℝ] Vector 3 →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u) :
    (∀ v, ⟪v, v⟫ₘ = 0 ↔ B v v = 0) ↔ ∃ c : ℝ, c ≠ 0 ∧ ∀ u v, B u v = c * ⟪u, v⟫ₘ := by
  constructor
  · intro hcone
    obtain ⟨c, hc⟩ := same_null_cone_proportional B hBsymm hcone
    set e₀ : Vector 3 := basis (Sum.inl 0) with he₀def
    have he0 : ⟪e₀, e₀⟫ₘ = (1 : ℝ) := by
      rw [he₀def, minkowskiProduct_basis_left, basis_apply, if_pos rfl,
        minkowskiMatrix.inl_0_inl_0]
      ring
    refine ⟨c, fun hc0 => ?_, hc⟩
    have hb0 : B e₀ e₀ = 0 := by rw [hc, he0, hc0]; ring
    have hzero : ⟪e₀, e₀⟫ₘ = 0 := (hcone _).mpr hb0
    rw [he0] at hzero
    exact one_ne_zero hzero
  · rintro ⟨c, hc, hB⟩ v
    rw [hB v v]
    constructor
    · intro h; rw [h, mul_zero]
    · intro h; exact (mul_eq_zero.mp h).resolve_left hc

/-! ## Proper time under a causal automorphism -/

/-- **The causal decomposition and proper-time law with one shared dilation witness.**
This is the reusable bundled form of the affine Alexandrov–Zeeman classification: the same
positive `c` occurs in `e x = √c • g x + e 0` and in
`τ(e q,e p) = √c · τ(q,p)`. -/
@[zil_level bridge_theorem]
theorem causalAutomorphism_decomposition_with_properTime
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : Vector 3 →ₗ[ℝ] Vector 3,
      IsLorentz g ∧
      (∀ x, e x = Real.sqrt c • g x + e 0) ∧
      ∀ q p : SpaceTime 3,
        properTime (e q) (e p) = Real.sqrt c * properTime q p := by
  obtain ⟨c, hc, g, hg, he⟩ :=
    affine_causalAutomorphism_eq_translation_dilation_lorentz e hcausal
  refine ⟨c, hc, g, hg, he, fun q p => ?_⟩
  have hstep : (e p) - (e q) = Real.sqrt c • g (p - q) := by
    rw [he p, he q, map_sub g p q, _root_.smul_sub]
    abel
  have hmink : ⟪(e p) - (e q), (e p) - (e q)⟫ₘ = c * ⟪p - q, p - q⟫ₘ := by
    rw [hstep]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hg (p - q) (p - q)]
    linear_combination ⟪p - q, p - q⟫ₘ * Real.mul_self_sqrt hc.le
  unfold properTime
  rw [hmink]
  exact Real.sqrt_mul hc.le _

/-- **Proper time scales by the dilation factor of a causal automorphism.**  Writing the
automorphism as `e x = √c·g(x) + e 0` (`affine_causalAutomorphism_eq_translation_dilation_lorentz`),
the translation cancels and the Lorentz map `g` preserves the Minkowski norm, so proper time
is multiplied by exactly `√c`.  The causal order therefore determines proper time (and the
metric) up to the conformal factor `√c`. -/
@[zil_level bridge_theorem]
theorem properTime_causalAutomorphism (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) :
    ∃ c : ℝ, 0 < c ∧ ∀ q p : SpaceTime 3,
      properTime (e q) (e p) = Real.sqrt c * properTime q p := by
  obtain ⟨c, hc, _, _, _, hscale⟩ :=
    causalAutomorphism_decomposition_with_properTime e hcausal
  exact ⟨c, hc, hscale⟩

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach same_null_cone_iff_proportional where
  formalizes @ "claim:a-symmetric-continuous-bilinear-form-has-the-same-null-cone-as-the-minkowski-form-if-and-only-if-it-is-a-nonzero-scalar-multiple-of-it-the-full-malament-metric-rigidity-iff",
  supported_by @ "lean:Lorentz.Vector.same_null_cone_proportional"

zil attach properTime_causalAutomorphism where
  formalizes @ "claim:a-causal-automorphism-scales-proper-time-by-exactly-its-dilation-factor-root-c-so-the-causal-order-determines-proper-time-and-the-metric-up-to-the-conformal-factor",
  supported_by @ "lean:Lorentz.Vector.affine_causalAutomorphism_eq_translation_dilation_lorentz",
  supported_by @ "lean:SpaceTime.properTime"

zil attach causalAutomorphism_decomposition_with_properTime where
  formalizes @ "claim:an-affine-causal-automorphism-has-one-shared-positive-dilation-witness-in-both-its-translation-dilation-lorentz-decomposition-and-its-proper-time-scaling-law",
  supported_by @ "lean:Lorentz.Vector.affine_causalAutomorphism_eq_translation_dilation_lorentz",
  supported_by @ "lean:SpaceTime.properTime"

zil_file_contract physlib.malamentConformalProperTimeBridge where
  promises "Linking the completed Alexandrov-Zeeman geometric reduction to the causal-structure and proper-time formalizations. The null-cone metric rigidity is closed to an iff: a symmetric continuous bilinear form has the same null cone as the Minkowski form if and only if it is a nonzero scalar multiple of it, adjoining the sufficiency that a nonzero rescaling preserves the zero set to the necessity same_null_cone_proportional. The affine causal decomposition and proper-time law are bundled with one shared positive dilation witness: the same root c multiplies the Lorentz map and every proper-time interval. Proper time under a causal automorphism therefore scales by exactly its dilation factor root c; the translation cancels and the Lorentz map preserves the Minkowski norm. So the causal order determines proper time and the metric up to the conformal factor root c, the concrete content of Malament's theorem."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Lorentz.Vector.same_null_cone_proportional",
    "lean:Lorentz.Vector.affine_causalAutomorphism_eq_translation_dilation_lorentz",
    "lean:SpaceTime.properTime"
  ]
  forbids_substitutes [
    "dropping the nonzero condition on the scalar in the rigidity iff",
    "reading the dilation rescaling of proper time as an invariance"
  ]
  witnessed_by [
    same_null_cone_iff_proportional,
    causalAutomorphism_decomposition_with_properTime,
    properTime_causalAutomorphism
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.malamentConformalProperTimeBridge
