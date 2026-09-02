/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
meta import Zil

/-!
# Spin-glass magnetic-response scaling

This module formalizes the algebraic scaling kernel of Baity-Jesi et al.,
*Scaling law describes the spin-glass response in theory, experiments and simulations*
(arXiv:2007.03871v2).  For correlation length `ξ`, spatial dimension `D`, replicon exponent
`θ`, and magnetic field `H`, the paper's scaling variable is

`x = ξ^(D - θ/2) H²`.

Its response consists of a regular `H²` term and a nonlinear correction
`ξ^(-θ/2) G(x)`.  The results below prove:

* the response is even in the magnetic field;
* a monomial `G(x) = c xⁿ` has correlation-length exponent
  `nD - (n+1)θ/2` and field order `H^(2n)`;
* the first two nonlinear orders are exactly
  `ξ^(2D-3θ/2)H⁴` and `ξ^(3D-2θ)H⁶`;
* changing correlation length gives the coefficient ratios used in the paper's data-collapse test.

## Honest scope

The scaling ansatz and the small-`x` expansion of `G` are physical inputs from the paper.  The Lean
results prove their exact algebraic consequences; they do not derive the ansatz from the
Edwards--Anderson Hamiltonian or certify the experimental fit.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.StatisticalMechanics.SpinGlassResponseScaling

/-! ## A. Scaling variable and response -/

/-- The paper's dimensionless magnetic scaling variable
`x = ξ^(D - θ/2) H²`. -/
noncomputable def scalingVariable (ξ D θ H : ℝ) : ℝ :=
  ξ ^ (D - θ / 2) * H ^ 2

/-- The nonlinear part `ξ^(-θ/2) G(x)` of the logarithmic effective-time response. -/
noncomputable def nonlinearCorrection (ξ D θ H : ℝ) (G : ℝ → ℝ) : ℝ :=
  ξ ^ (-θ / 2) * G (scalingVariable ξ D θ H)

/-- Equation (1)'s response, with the constant `S/T` represented by `S / T`. -/
noncomputable def logResponse (S T ξ D θ H : ℝ) (G : ℝ → ℝ) : ℝ :=
  S / T * scalingVariable ξ D θ H + nonlinearCorrection ξ D θ H G

/-- The scaling variable is even under magnetic-field reversal. -/
lemma scalingVariable_neg (ξ D θ H : ℝ) :
    scalingVariable ξ D θ (-H) = scalingVariable ξ D θ H := by
  simp [scalingVariable]

/-- The complete scaling response is even under `H ↦ -H`, independently of the choice of `G`. -/
lemma logResponse_neg (S T ξ D θ H : ℝ) (G : ℝ → ℝ) :
    logResponse S T ξ D θ (-H) G = logResponse S T ξ D θ H G := by
  simp [logResponse, nonlinearCorrection, scalingVariable]

/-! ## B. Nonlinear hierarchy -/

/-- The correlation-length exponent of the `xⁿ` nonlinear term:
`nD - (n+1)θ/2`. -/
noncomputable def nonlinearExponent (n : ℕ) (D θ : ℝ) : ℝ :=
  (n : ℝ) * D - ((n : ℝ) + 1) * θ / 2

/-- The `H⁴` correction has exponent `2D - 3θ/2`. -/
lemma nonlinearExponent_two (D θ : ℝ) :
    nonlinearExponent 2 D θ = 2 * D - 3 * θ / 2 := by
  norm_num [nonlinearExponent]

/-- The `H⁶` correction has exponent `3D - 2θ`. -/
lemma nonlinearExponent_three (D θ : ℝ) :
    nonlinearExponent 3 D θ = 3 * D - 2 * θ := by
  simp [nonlinearExponent]
  ring

/-- A monomial scaling function `G(x)=c xⁿ` produces exactly
`c ξ^(nD-(n+1)θ/2) H^(2n)`. -/
lemma powerCorrection_eq (n : ℕ) (ξ D θ H c : ℝ) (hξ : 0 < ξ) :
    nonlinearCorrection ξ D θ H (fun x => c * x ^ n) =
      c * ξ ^ nonlinearExponent n D θ * H ^ (2 * n) := by
  unfold nonlinearCorrection scalingVariable
  simp only
  rw [mul_pow, ← Real.rpow_natCast (ξ ^ (D - θ / 2)) n, ← Real.rpow_mul hξ.le]
  have hp : ξ ^ (-θ / 2) * ξ ^ ((D - θ / 2) * (n : ℝ)) =
      ξ ^ nonlinearExponent n D θ := by
    rw [← Real.rpow_add hξ]
    congr 1
    unfold nonlinearExponent
    ring
  rw [show (H ^ 2) ^ n = H ^ (2 * n) by rw [pow_mul]]
  rw [← hp]
  ring

/-- The leading small-`x` correction `G(x)=c x²` is the paper's
`c ξ^(2D-3θ/2)H⁴` term. -/
lemma quadraticCorrection_eq (ξ D θ H c : ℝ) (hξ : 0 < ξ) :
    nonlinearCorrection ξ D θ H (fun x => c * x ^ 2) =
      c * ξ ^ (2 * D - 3 * θ / 2) * H ^ 4 := by
  rw [powerCorrection_eq 2 ξ D θ H c hξ, nonlinearExponent_two]

/-- The next correction `G(x)=c x³` is `c ξ^(3D-2θ)H⁶`. -/
lemma sexticCorrection_eq (ξ D θ H c : ℝ) (hξ : 0 < ξ) :
    nonlinearCorrection ξ D θ H (fun x => c * x ^ 3) =
      c * ξ ^ (3 * D - 2 * θ) * H ^ 6 := by
  rw [powerCorrection_eq 3 ξ D θ H c hξ, nonlinearExponent_three]

/-- The polynomial truncation `G(x)=c₄x²+c₆x³` reproduces the `H⁴/H⁶`
response hierarchy used in the experimental fit. -/
lemma polynomialCorrection_eq (ξ D θ H c₄ c₆ : ℝ) (hξ : 0 < ξ) :
    nonlinearCorrection ξ D θ H (fun x => c₄ * x ^ 2 + c₆ * x ^ 3) =
      c₄ * ξ ^ (2 * D - 3 * θ / 2) * H ^ 4 +
        c₆ * ξ ^ (3 * D - 2 * θ) * H ^ 6 := by
  have hsplit :
      nonlinearCorrection ξ D θ H (fun x => c₄ * x ^ 2 + c₆ * x ^ 3) =
        nonlinearCorrection ξ D θ H (fun x => c₄ * x ^ 2) +
          nonlinearCorrection ξ D θ H (fun x => c₆ * x ^ 3) := by
    unfold nonlinearCorrection
    ring
  rw [hsplit, quadraticCorrection_eq ξ D θ H c₄ hξ,
    sexticCorrection_eq ξ D θ H c₆ hξ]

/-! ## C. Correlation-length ratios -/

/-- The regular `H²` scaling variable transforms with the paper's exponent `D-θ/2`. -/
lemma scalingVariable_ratio (ξ₁ ξ₂ D θ H : ℝ) (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    scalingVariable ξ₂ D θ H =
      (ξ₂ / ξ₁) ^ (D - θ / 2) * scalingVariable ξ₁ D θ H := by
  unfold scalingVariable
  rw [Real.div_rpow hξ₂.le hξ₁.le]
  field_simp [(Real.rpow_pos_of_pos hξ₁ (D - θ / 2)).ne']

/-- Every nonlinear coefficient transforms by the correlation-length ratio raised to its
order-dependent exponent `nD-(n+1)θ/2`. -/
lemma powerCorrection_ratio (n : ℕ) (ξ₁ ξ₂ D θ H c : ℝ)
    (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    nonlinearCorrection ξ₂ D θ H (fun x => c * x ^ n) =
      (ξ₂ / ξ₁) ^ nonlinearExponent n D θ *
        nonlinearCorrection ξ₁ D θ H (fun x => c * x ^ n) := by
  rw [powerCorrection_eq n ξ₂ D θ H c hξ₂,
    powerCorrection_eq n ξ₁ D θ H c hξ₁,
    Real.div_rpow hξ₂.le hξ₁.le]
  rw [div_mul_eq_mul_div, ← mul_assoc]
  field_simp [(Real.rpow_pos_of_pos hξ₁ (nonlinearExponent n D θ)).ne']

/-- The `H⁴` coefficient ratio is `(ξ₂/ξ₁)^(2D-3θ/2)`, the middle relation in
the paper's correlation-length consistency test. -/
lemma quadraticCorrection_ratio (ξ₁ ξ₂ D θ H c : ℝ)
    (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    nonlinearCorrection ξ₂ D θ H (fun x => c * x ^ 2) =
      (ξ₂ / ξ₁) ^ (2 * D - 3 * θ / 2) *
        nonlinearCorrection ξ₁ D θ H (fun x => c * x ^ 2) := by
  simpa only [nonlinearExponent_two] using
    powerCorrection_ratio 2 ξ₁ ξ₂ D θ H c hξ₁ hξ₂

/-- The `H⁶` coefficient ratio is `(ξ₂/ξ₁)^(3D-2θ)`, the final relation in
the paper's correlation-length consistency test. -/
lemma sexticCorrection_ratio (ξ₁ ξ₂ D θ H c : ℝ)
    (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    nonlinearCorrection ξ₂ D θ H (fun x => c * x ^ 3) =
      (ξ₂ / ξ₁) ^ (3 * D - 2 * θ) *
        nonlinearCorrection ξ₁ D θ H (fun x => c * x ^ 3) := by
  simpa only [nonlinearExponent_three] using
    powerCorrection_ratio 3 ξ₁ ξ₂ D θ H c hξ₁ hξ₂

end Physlib.StatisticalMechanics.SpinGlassResponseScaling

end

/- ZIL-BEGIN -/

zil attach Physlib.StatisticalMechanics.SpinGlassResponseScaling.logResponse_neg where
  formalizes @ "claim:spin-glass-effective-time-response-is-even-under-magnetic-field-reversal",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:scaling-law-describes-the-spin-glass-response-2007.03871v2",
  caveat @ "claim:the-scaling-ansatz-is-paper-supplied-not-derived-from-the-edwards-anderson-hamiltonian"

zil attach Physlib.StatisticalMechanics.SpinGlassResponseScaling.powerCorrection_eq where
  formalizes @ "claim:spin-glass-nonlinear-x-power-n-has-field-order-2n-and-correlation-length-exponent-nD-minus-n-plus-one-theta-over-two",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:scaling-law-describes-the-spin-glass-response-2007.03871v2",
  caveat @ "claim:the-lean-result-proves-the-exponent-hierarchy-conditionally-on-the-paper-scaling-form"

zil attach Physlib.StatisticalMechanics.SpinGlassResponseScaling.polynomialCorrection_eq where
  formalizes @ "claim:spin-glass-small-field-nonlinear-response-has-H4-and-H6-correlation-length-scalings",
  supported_by @ "paper:scaling-law-describes-the-spin-glass-response-2007.03871v2",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:spin-glass-nonlinear-x-power-n-has-field-order-2n-and-correlation-length-exponent-nD-minus-n-plus-one-theta-over-two",
  caveat @ "claim:the-correlation-length-scaling-exponents-are-a-model-ansatz-the-theorem-itself-is-the-exact-polynomial-response-identity"

zil attach Physlib.StatisticalMechanics.SpinGlassResponseScaling.quadraticCorrection_ratio where
  formalizes @ "claim:spin-glass-H4-coefficient-ratio-is-the-correlation-length-ratio-to-2D-minus-three-theta-over-two",
  supported_by @ "paper:scaling-law-describes-the-spin-glass-response-2007.03871v2",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:this-is-the-exact-ratio-law-not-a-certification-of-the-reported-experimental-values"

zil attach Physlib.StatisticalMechanics.SpinGlassResponseScaling.sexticCorrection_ratio where
  formalizes @ "claim:spin-glass-H6-coefficient-ratio-is-the-correlation-length-ratio-to-3D-minus-two-theta",
  supported_by @ "paper:scaling-law-describes-the-spin-glass-response-2007.03871v2",
  epistemic_status @ "ansatz-loaded",
  caveat @ "claim:this-is-the-exact-ratio-law-not-a-certification-of-the-reported-experimental-values"

zil_file_contract physlib.spinGlassResponseScaling where
  promises "The algebraic core of the spin-glass magnetic-response scaling law: evenness in H; the general nonlinear hierarchy xi^(nD-(n+1)theta/2) H^(2n); its H^4 and H^6 terms; and the exact correlation-length coefficient ratios."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Real.rpow"]
  forbids_substitutes ["deriving the physical scaling ansatz from algebra alone",
    "treating exact coefficient ratios as independent experimental verification"]
  witnessed_by [Physlib.StatisticalMechanics.SpinGlassResponseScaling.logResponse_neg,
    Physlib.StatisticalMechanics.SpinGlassResponseScaling.powerCorrection_eq,
    Physlib.StatisticalMechanics.SpinGlassResponseScaling.polynomialCorrection_eq,
    Physlib.StatisticalMechanics.SpinGlassResponseScaling.quadraticCorrection_ratio,
    Physlib.StatisticalMechanics.SpinGlassResponseScaling.sexticCorrection_ratio]

/- ZIL-END -/
