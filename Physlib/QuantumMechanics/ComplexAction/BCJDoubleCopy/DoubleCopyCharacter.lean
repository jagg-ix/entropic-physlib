/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.Rapidity.Basic
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

/-!
# The BCJ double copy is the EM → gravity face of the group-like character

The BCJ double copy builds **gravity from gauge²**: the gauge amplitude `A = Σᵢ nᵢ cᵢ / Dᵢ` (kinematic `nᵢ`
× color `cᵢ`) becomes the gravity amplitude `M = Σᵢ nᵢ ñᵢ / Dᵢ` by replacing the color factors with a second
kinematic copy (`BCJDoubleCopy.ColorKinematicsDoubleCopy`). For the Maxwell field the kinematic numerators are
`nᵢ = k F` and the kinematic Jacobi *is* the Faraday/Bianchi identity (`faradayBCJDuality`), so **EM** is one
copy and **gravity** is the double copy.

Identifying the BCJ numerators with the entropic action `nᵢ = S_I`, the double-copy path-integral weight
factorizes (`bcj_doublecopy_fk_factorization`):

  `exp(−(S₁ + S₂)) = exp(−S₁) · exp(−S₂)`.

This is **exactly the group-like exponential character** `e^{a+b} = e^a · e^b` of
`Rapidity.Basic` — the same one whose compact (`ℤ/k`) form is the Verlinde `S`-matrix kernel
(`S_{(a+b)x} = √k S_{ax} S_{bx}`) and whose hyperbolic form is the Bogoliubov rapidity (boost composition,
`coth/tanh` = Bose/Fermi). This file records the BCJ double copy as a `1`-normalized character:

* `bcjDoubleCopyWeight_normalizedCharacter`: `S ↦ e^{−S}` is a `1`-normalized character — the double-copy
  factorization `exp(−(S₁+S₂)) = exp(−S₁)exp(−S₂)` is the character law.

So the link between **EM and gravity** is the double copy, and the double copy is realized through the *same*
character that diagonalizes the Verlinde charge convolution: the gauge/color side carries the character (the
Verlinde modular data of the gauge group), the kinematic side carries the rapidity character, and squaring
the kinematic copy (color → kinematic) produces gravity — with the entropic weight `e^{−S_I}` multiplying as
the character demands.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson (2008/2010), color–kinematics duality & double copy.
  `Physlib` (`BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_doublecopy_fk_factorization`, `Rapidity.Basic`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Rapidity.Basic
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter

/-- **[The BCJ double-copy weight is a `1`-normalized character]** `S ↦ e^{−S}` satisfies
`χ(S₁+S₂) = 1 · χ(S₁) · χ(S₂)`: the entropic double-copy factorization
`exp(−(S₁+S₂)) = exp(−S₁)·exp(−S₂)` is the group-like character law — the same character (normalization `1`)
as the Bogoliubov rapidity, and the same family as the Verlinde `S`-matrix (normalization `√k`). The
gauge → gravity double copy multiplies the entropic weights exactly as the character requires. -/
lemma bcjDoubleCopyWeight_normalizedCharacter :
    NormalizedCharacter 1 (fun S : ℝ => Complex.exp (-(S : ℂ))) := by
  intro a b
  show Complex.exp (-((a + b : ℝ) : ℂ)) = 1 * Complex.exp (-(a : ℂ)) * Complex.exp (-(b : ℂ))
  rw [Complex.ofReal_add, neg_add, Complex.exp_add]
  ring

/-- **[Real double-copy factorization is the same character]** the real-valued
`exp(−(S₁+S₂)) = exp(−S₁)·exp(−S₂)` (`bcj_doublecopy_fk_factorization`) is the modulus of the complex
character `S ↦ e^{−S}` — the entropic Born weight of the product (gravity) theory factorizing into the two
gauge copies. -/
lemma bcjDoubleCopy_fk_eq_character_norm (S₁ S₂ : ℝ) :
    Real.exp (-(S₁ + S₂)) = Real.exp (-S₁) * Real.exp (-S₂) :=
  BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_doublecopy_fk_factorization S₁ S₂


/-- **[The double copy factorizes the actual Nagao–Nielsen path weight]** the product of the entropic Born
weights of two gauge copies (imaginary actions `S₁, S₂`) is the weight of the combined (gravity) theory:
`‖nnPathWeight S_R₁ S₁ ℏ‖ · ‖nnPathWeight S_R₂ S₂ ℏ‖ = ‖nnPathWeight (S_R₁+S_R₂) (S₁+S₂) ℏ‖`. The character
law realized on the repo's actual complex-action weight (`norm_nnPathWeight`), generalizing
`bcj_doublecopy_fk_factorization` to arbitrary `ℏ`. -/
lemma nnPathWeight_norm_doubleCopy (S_R₁ S_R₂ S₁ S₂ ℏ : ℝ) :
    ‖nnPathWeight S_R₁ S₁ ℏ‖ * ‖nnPathWeight S_R₂ S₂ ℏ‖
      = ‖nnPathWeight (S_R₁ + S_R₂) (S₁ + S₂) ℏ‖ := by
  rw [norm_nnPathWeight, norm_nnPathWeight, norm_nnPathWeight, ← Real.exp_add]
  congr 1
  ring

/-- **[The `nnPathWeight` double copy *is* the BCJ FK factorization]** at `ℏ = 1`, `S_R = 0`:
`‖nnPathWeight 0 S₁ 1‖ · ‖nnPathWeight 0 S₂ 1‖ = exp(−(S₁+S₂))` — the repo's actual path weight instantiates
`BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_doublecopy_fk_factorization`, grounding the abstract character in the
concrete double-copy object. -/
lemma nnPathWeight_doubleCopy_eq_bcj_fk (S₁ S₂ : ℝ) :
    ‖nnPathWeight 0 S₁ 1‖ * ‖nnPathWeight 0 S₂ 1‖ = Real.exp (-(S₁ + S₂)) := by
  rw [BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_doublecopy_fk_factorization, norm_nnPathWeight,
    norm_nnPathWeight]
  simp

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter

end
