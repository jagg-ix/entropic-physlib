/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.MalamentConformalProperTimeBridge
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLorentzReconstruction
meta import Zil

/-!
# Conformal invariants of a causal automorphism

The affine classification `affine_causalAutomorphism_eq_translation_dilation_lorentz` writes
a causal automorphism as `e x = √c·g(x) + e 0`.  The consequences for the metric quantities:

* `intervalSq_causalAutomorphism` — the spacetime interval scales by the dilation factor,
  `⟪e p − e q, e p − e q⟫ₘ = c·⟪p − q, p − q⟫ₘ`;
* `causalCharacter_causalAutomorphism` — the causal character (timelike/null/spacelike) is
  *preserved* (the positive factor `c` keeps the sign), so a causal automorphism is indeed a
  causal-order automorphism;
* `properTime_ratio_causalAutomorphism` — the global scale `√c` cancels in a ratio, so
  **proper-time ratios are exact causal invariants**: `τ(eq,ep)·τ(q',p') = τ(q,p)·τ(eq',ep')`.

So while the causal order fixes proper time (and the metric) only up to the conformal factor
`√c`, every *scale-invariant* proper-time quantity is an exact invariant of the causal order —
the physical content of Malament's theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace SpaceTime

/-- **The spacetime interval scales by the dilation factor** of a causal automorphism:
`⟪e p − e q, e p − e q⟫ₘ = c·⟪p − q, p − q⟫ₘ`. -/
@[zil_level bridge_theorem]
theorem intervalSq_causalAutomorphism (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) :
    ∃ c : ℝ, 0 < c ∧ ∀ q p : SpaceTime 3,
      ⟪(e p) - (e q), (e p) - (e q)⟫ₘ = c * ⟪p - q, p - q⟫ₘ := by
  obtain ⟨c, hc, g, hg, he⟩ :=
    affine_causalAutomorphism_eq_translation_dilation_lorentz e hcausal
  refine ⟨c, hc, fun q p => ?_⟩
  have hstep : (e p) - (e q) = Real.sqrt c • g (p - q) := by
    rw [he p, he q, map_sub g p q, _root_.smul_sub]; abel
  rw [hstep]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hg (p - q) (p - q)]
  linear_combination ⟪p - q, p - q⟫ₘ * Real.mul_self_sqrt hc.le

/-- **A causal automorphism preserves the causal character** — timelike, null, and spacelike
separations map to separations of the same character, because the interval scales by the
positive factor `c`. -/
@[zil_level bridge_theorem]
theorem causalCharacter_causalAutomorphism (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) (q p : SpaceTime 3) :
    causalCharacter ((e p) - (e q)) = causalCharacter (p - q) := by
  obtain ⟨c, hc, hint⟩ := intervalSq_causalAutomorphism e hcausal
  rw [causalCharacter_eq_ofForm, causalCharacter_eq_ofForm, hint q p,
    causalCharacterOfForm_smul_pos hc]

/-- **Proper-time ratios are exact causal invariants.**  Under a causal automorphism every
proper time scales by the same factor `√c`, which cancels in a ratio:
`τ(eq,ep)·τ(q',p') = τ(q,p)·τ(eq',ep')`.  The causal order fixes the metric only up to the
global scale, but scale-invariant proper-time quantities are exactly determined. -/
@[zil_level bridge_theorem]
theorem properTime_ratio_causalAutomorphism (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) (q p q' p' : SpaceTime 3) :
    properTime (e q) (e p) * properTime q' p' = properTime q p * properTime (e q') (e p') := by
  obtain ⟨c, _, hscale⟩ := properTime_causalAutomorphism e hcausal
  rw [hscale q p, hscale q' p']
  ring

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach properTime_ratio_causalAutomorphism where
  formalizes @ "claim:proper-time-ratios-are-exact-causal-invariants-the-global-dilation-scale-root-c-cancels-so-scale-invariant-proper-time-quantities-are-exactly-determined-by-the-causal-order",
  supported_by @ "lean:SpaceTime.properTime"

zil attach intervalSq_causalAutomorphism where
  supported_by @ "lean:affine_causalAutomorphism_eq_translation_dilation_lorentz",
  formalizes @ "claim:the-spacetime-interval-scales-by-the-dilation-factor-c-of-a-causal-automorphism"

zil attach causalCharacter_causalAutomorphism where
  supported_by @ "lean:intervalSq_causalAutomorphism",
  formalizes @ "claim:a-causal-automorphism-preserves-the-causal-character-timelike-null-or-spacelike-since-the-interval-scales-by-a-positive-factor"

zil_file_contract physlib.causalAutomorphismConformalInvariants where
  promises "The conformal invariants of a causal automorphism, from the affine classification e x = root c times g x plus e zero. The spacetime interval scales by the dilation factor c. The causal character timelike null or spacelike is preserved because the positive factor c keeps the sign, so a causal automorphism is a causal-order automorphism. And proper-time ratios are exact causal invariants: the global scale root c cancels in a ratio, so tau of e q e p times tau of q prime p prime equals tau of q p times tau of e q prime e p prime. While the causal order fixes proper time and the metric only up to the conformal factor root c, every scale-invariant proper-time quantity is an exact invariant of the causal order."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:SpaceTime.properTime",
    "lean:Lorentz.Vector.affine_causalAutomorphism_eq_translation_dilation_lorentz"
  ]
  forbids_substitutes [
    "reading the dilation scaling of proper time or the interval as an invariance",
    "claiming absolute proper time rather than only its ratios is fixed by the causal order"
  ]
  witnessed_by [
    intervalSq_causalAutomorphism,
    causalCharacter_causalAutomorphism,
    properTime_ratio_causalAutomorphism
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.causalAutomorphismConformalInvariants
