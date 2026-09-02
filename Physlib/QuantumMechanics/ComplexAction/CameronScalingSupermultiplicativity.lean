/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
meta import Zil

/-!
# Cameron weights: the cubic–quadratic scaling obstruction and super-multiplicativity

Ports the genuine, **mathematical kernel** of the Navier–Stokes Cameron / vortex-stretching
files (`NSCameronKoopmanBridge`, `PalinstrophyCameronBound`, `CameronVSGapExposition`,
`TriadicInteractionBridge`). Those files carry reduced-carrier stubs (`cameronWeightAtMode := 1`,
`…Integral := 0`), the Millennium content as `axiom`s, fitted constants (`1/32`, `1/1000`), and `Bool`
`LabeledClaim`/diagnosis records — none portable. Two pieces are genuine real analysis:

* **the scaling obstruction**: the Cameron vortex-stretching functional scales like `α³` while the
  enstrophy scales like `α²`, so **no global linear bound** `Vc ≤ K·Ω` can hold — for every `K` there is a
  scale at which `K·(α²c₂) < α³c₁` (`cameron_exceeds_linear_enstrophy`,
  `no_global_linear_cameron_bound`). This is the exact cubic-vs-quadratic scaling mismatch, the reason
  the Cameron-to-plain gap is the Millennium obstruction;
* **super-multiplicativity of the Cameron weights** `W_k = e^{−c·k^{2/3}}`: because the exponent `2/3 ≤ 1`
  makes `x ↦ x^{2/3}` subadditive (`(j+l)^{2/3} ≤ j^{2/3} + l^{2/3}`), the weights satisfy
  `W_j·W_l ≤ W_{j+l}` (`cameronWeight_supermultiplicative`) — the output-mode weight dominates the
  input-product weight, which is exactly what blocks a mode-by-mode factorization of vortex stretching.

* **§A — the cubic–quadratic scaling obstruction** (`cameron_exceeds_linear_enstrophy`,
  `no_global_linear_cameron_bound`).
* **§B — Cameron-weight super-multiplicativity** (`cameronWeight`, `cameronWeight_supermultiplicative`).

## References

* Subadditivity of `x ↦ x^p` for `p ∈ [0,1]` (`Real.rpow_add_le_add_rpow`); the cubic scaling of vortex
  stretching vs the quadratic scaling of enstrophy. Source (kernel only; `:= 0`/`:= 1` stubs, Millennium
  `axiom`s, fitted constants, `Bool` records): `NavierStokes/{NSCameronKoopmanBridge,
  PalinstrophyCameronBound, CameronVSGapExposition, TriadicInteractionBridge}.lean`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity


/-- **[The cubic functional exceeds any linear multiple of the quadratic] at large scale.** With the
Cameron vortex stretching scaling as `α³·c₁` and the enstrophy as `α²·c₂` (`c₁, c₂ > 0`), for *every*
constant `K` there is a scale `α > 0` at which `K·(α²c₂) < α³c₁`. -/
lemma cameron_exceeds_linear_enstrophy (c₁ c₂ K : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ α : ℝ, 0 < α ∧ K * (α ^ 2 * c₂) < α ^ 3 * c₁ := by
  refine ⟨|K| * c₂ / c₁ + 1, by positivity, ?_⟩
  set α := |K| * c₂ / c₁ + 1 with hαdef
  have hα : 0 < α := by rw [hαdef]; positivity
  have hKle : K ≤ |K| := le_abs_self K
  have hαc₁ : K * c₂ < α * c₁ := by
    have he : α * c₁ = |K| * c₂ + c₁ := by rw [hαdef]; field_simp
    rw [he]; nlinarith [mul_le_mul_of_nonneg_right hKle hc₂.le]
  nlinarith [mul_pos (mul_pos hα hα) (sub_pos.mpr hαc₁), hα]

/-- **[No global linear Cameron bound] `¬ ∃ K, ∀ α > 0, α³c₁ ≤ K(α²c₂)`.** The cubic-vs-quadratic scaling
mismatch rules out any global linear bound of the Cameron vortex stretching by the enstrophy — the
Cameron-to-plain gap that *is* the Navier–Stokes regularity obstruction. -/
lemma no_global_linear_cameron_bound (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ¬ ∃ K : ℝ, ∀ α : ℝ, 0 < α → α ^ 3 * c₁ ≤ K * (α ^ 2 * c₂) := by
  rintro ⟨K, hK⟩
  obtain ⟨α, hα, hlt⟩ := cameron_exceeds_linear_enstrophy c₁ c₂ K hc₁ hc₂
  exact absurd (hK α hα) (not_le.mpr hlt)


/-- **The Cameron weight at scale `x`** `W = e^{−c·x^{2/3}}` (exponential suppression of high modes). -/
noncomputable def cameronWeight (c x : ℝ) : ℝ := Real.exp (-c * x ^ (2 / 3 : ℝ))

/-- **[Super-multiplicativity] `W_j·W_l ≤ W_{j+l}`.** Because `x ↦ x^{2/3}` is subadditive
(`(j+l)^{2/3} ≤ j^{2/3} + l^{2/3}`, exponent `≤ 1`), the Cameron weights are super-multiplicative: the
output-mode weight dominates the product of the input weights (`c ≥ 0`, `j, l ≥ 0`). This is exactly what
blocks a mode-by-mode factorization of the triadic vortex stretching. -/
lemma cameronWeight_supermultiplicative (c j l : ℝ) (hc : 0 ≤ c) (hj : 0 ≤ j) (hl : 0 ≤ l) :
    cameronWeight c j * cameronWeight c l ≤ cameronWeight c (j + l) := by
  unfold cameronWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsub : (j + l) ^ (2 / 3 : ℝ) ≤ j ^ (2 / 3 : ℝ) + l ^ (2 / 3 : ℝ) :=
    Real.rpow_add_le_add_rpow hj hl (by norm_num) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hsub hc]

end Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity.no_global_linear_cameron_bound where
  formalizes @ "claim:the-cubic-cameron-vortex-stretching-functional-admits-no-global-linear-bound-by-the-quadratic-enstrophy",
  supported_by @ "paper:cameron-navier-stokes-vortex-stretching-scaling-obstruction"

zil attach Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity.cameron_exceeds_linear_enstrophy where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:at-large-scale-the-cubic-cameron-functional-outgrows-any-linear-multiple-of-the-quadratic-enstrophy",
  requires @ "claim:the-cubic-cameron-vortex-stretching-functional-admits-no-global-linear-bound-by-the-quadratic-enstrophy"

zil attach Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity.cameronWeight_supermultiplicative where
  formalizes @ "claim:the-cameron-weights-are-super-multiplicative-from-subadditivity-of-the-two-thirds-power-blocking-mode-factorization"

zil_file_contract physlib.cameronScalingSupermultiplicativity where
  promises "The Cameron scaling obstruction: the cubic vortex-stretching functional alpha^3 c_1 outgrows any linear multiple of the quadratic enstrophy alpha^2 c_2 at large scale, so no global linear bound exists (the Navier-Stokes regularity obstruction); and the Cameron weights exp(-c x^{2/3}) are super-multiplicative from subadditivity of the two-thirds power, blocking mode-by-mode factorization of triadic vortex stretching."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity.cameronWeight"]
  forbids_substitutes ["any fitted-constant or axiom-carrying Navier-Stokes stub, only the two scale-analysis kernels are ported here"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity.no_global_linear_cameron_bound,
    Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity.cameron_exceeds_linear_enstrophy,
    Physlib.QuantumMechanics.ComplexAction.CameronScalingSupermultiplicativity.cameronWeight_supermultiplicative]

/- ZIL-END -/
