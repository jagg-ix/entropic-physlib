/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Physlib.QFT.HamiltonianRenormalisation.SingleBosonExchangeSchwingerDyson

/-!
# Matter-Liouville-ghost factorization for conformal welding

This module records the finite algebraic content used by Guillaume Baverez and Antoine Jego,
*Conformal welding and the matter-Liouville-ghost factorisation*, arXiv:2502.17076v2.

The analytic results of the paper concern SLE loop measures, Gaussian free fields, welding
homeomorphisms, and quasiconformal flows.  The present file starts with the parts which can
already be checked directly in this repository:

* the parameter identities from Eq. (1.1), including `c_m + c_L = 26`;
* the `bc` ghost central charge `-26` and conformal-weight contribution `-1`;
* the path-integral exponent in Eq. (1.10) as a matter factor times a ghost Jacobian factor;
* the potential-difference formula `Omega` from Eq. (1.14);
* the zero-mode factorization used in Lemma 6.1;
* a bridge from the welding ghost Jacobian to the finite Faddeev-Popov ghost complex already
  used by the Schwinger-Dyson single-boson-exchange path-integral insertion.

## References

* G. Baverez, A. Jego, *Conformal welding and the matter-Liouville-ghost factorisation*,
  arXiv:2502.17076v2, Eqs. (1.1), (1.6)--(1.10), (1.13)--(1.14), Lemma 6.1, and Section 5.2.1.
* P. Di Francesco, P. Mathieu, D. Senechal, *Conformal Field Theory*, Section 5.3.3 for the
  `bc` ghost central charge and conformal weights.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QFT.ConformalWelding.MatterLiouvilleGhostFactorization

open Physlib.QFT.HamiltonianRenormalisation

/-! ## A. Matter, Liouville, and ghost central charges -/

/-- The Liouville background charge `Q = gamma / 2 + 2 / gamma`. -/
noncomputable def backgroundCharge (gamma : ℝ) : ℝ :=
  gamma / 2 + 2 / gamma

/-- The matter central charge `c_m = 1 - 6 (gamma / 2 - 2 / gamma)^2`. -/
noncomputable def matterCentralCharge (gamma : ℝ) : ℝ :=
  1 - 6 * (gamma / 2 - 2 / gamma) ^ 2

/-- The Liouville central charge `c_L = 1 + 6 Q^2`. -/
noncomputable def liouvilleCentralCharge (gamma : ℝ) : ℝ :=
  1 + 6 * backgroundCharge gamma ^ 2

/-- The `bc` ghost central charge in bosonic string theory. -/
def bcGhostCentralCharge : ℝ :=
  -26

/-- The `c` field of the `bc` system has conformal weight `-1`. -/
def bcGhostConformalWeight : ℝ :=
  -1

/-- Eq. (1.1): the matter and Liouville central charges sum to `26`. -/
lemma matter_add_liouvilleCentralCharge_eq_26 (gamma : ℝ) (hgamma : gamma ≠ 0) :
    matterCentralCharge gamma + liouvilleCentralCharge gamma = 26 := by
  unfold matterCentralCharge liouvilleCentralCharge backgroundCharge
  field_simp [hgamma]
  ring

/-- Eq. (1.1), rearranged as `c_L = 26 - c_m`. -/
lemma liouvilleCentralCharge_eq_26_sub_matter (gamma : ℝ) (hgamma : gamma ≠ 0) :
    liouvilleCentralCharge gamma = 26 - matterCentralCharge gamma := by
  have h := matter_add_liouvilleCentralCharge_eq_26 gamma hgamma
  linarith

/-- The matter, Liouville, and `bc` ghost central charges cancel. -/
lemma matter_liouville_bcGhost_centralCharge_cancel (gamma : ℝ) (hgamma : gamma ≠ 0) :
    matterCentralCharge gamma + liouvilleCentralCharge gamma + bcGhostCentralCharge = 0 := by
  rw [matter_add_liouvilleCentralCharge_eq_26 gamma hgamma]
  simp [bcGhostCentralCharge]

/-- The `bc` ghost contribution is the negative of the critical bosonic-string charge. -/
lemma bcGhostCentralCharge_eq_neg_critical :
    bcGhostCentralCharge = -26 :=
  rfl

/-- The ghost conformal-weight contribution is `-1`. -/
lemma bcGhostConformalWeight_eq_neg_one :
    bcGhostConformalWeight = -1 :=
  rfl

/-! ## B. Welding actions and Jacobian exponents -/

/-- The scalar part of the Liouville field action `phi . Phi = phi + Q log |Phi'|`. -/
def liouvilleFieldTransform (Q phi logJacobian : ℝ) : ℝ :=
  phi + Q * logJacobian

/-- Eq. (1.8) for the scalar log-Jacobian part of the Liouville field action. -/
lemma liouvilleFieldTransform_comp (Q phi logJacobian₁ logJacobian₂ : ℝ) :
    liouvilleFieldTransform Q (liouvilleFieldTransform Q phi logJacobian₁) logJacobian₂ =
      liouvilleFieldTransform Q phi (logJacobian₁ + logJacobian₂) := by
  unfold liouvilleFieldTransform
  ring

/-- The matter part of the welding exponent, `c_m S_1 / (24 pi)`. -/
noncomputable def matterWeldingExponent (cm S1 : ℝ) : ℝ :=
  cm * S1 / (24 * Real.pi)

/-- The `bc` ghost Jacobian exponent:
`(-26) S_1 / (24 pi) + 2 (-1) K`. -/
noncomputable def bcGhostWeldingExponent (S1 K : ℝ) : ℝ :=
  bcGhostCentralCharge * S1 / (24 * Real.pi) + 2 * bcGhostConformalWeight * K

/-- The matter plus ghost exponent appearing in the formal welding measure. -/
noncomputable def matterGhostWeldingExponent (cm S1 K : ℝ) : ℝ :=
  matterWeldingExponent cm S1 + bcGhostWeldingExponent S1 K

/-- Eq. (1.10): the matter plus ghost exponent is
`(c_m - 26) S_1 / (24 pi) - 2K`. -/
lemma matterGhostWeldingExponent_eq (cm S1 K : ℝ) :
    matterGhostWeldingExponent cm S1 K =
      (cm - 26) * S1 / (24 * Real.pi) - 2 * K := by
  unfold matterGhostWeldingExponent matterWeldingExponent bcGhostWeldingExponent
    bcGhostCentralCharge bcGhostConformalWeight
  ring

/-- Using `c_L = 26 - c_m`, the welding exponent can be written as
`-c_L S_1 / (24 pi) - 2K`. -/
lemma matterGhostWeldingExponent_eq_neg_liouville
    (gamma S1 K : ℝ) (hgamma : gamma ≠ 0) :
    matterGhostWeldingExponent (matterCentralCharge gamma) S1 K =
      -liouvilleCentralCharge gamma * S1 / (24 * Real.pi) - 2 * K := by
  rw [matterGhostWeldingExponent_eq,
    liouvilleCentralCharge_eq_26_sub_matter gamma hgamma]
  ring

/-- The welding path-integral weight associated with the matter plus ghost exponent. -/
noncomputable def matterGhostWeldingWeight (cm S1 K : ℝ) : ℝ :=
  Real.exp (matterGhostWeldingExponent cm S1 K)

/-- The matter welding weight. -/
noncomputable def matterWeldingWeight (cm S1 : ℝ) : ℝ :=
  Real.exp (matterWeldingExponent cm S1)

/-- The `bc` ghost welding weight. -/
noncomputable def bcGhostWeldingWeight (S1 K : ℝ) : ℝ :=
  Real.exp (bcGhostWeldingExponent S1 K)

/-- The matter-Liouville-ghost factorization of the welding weight. -/
lemma matterGhostWeldingWeight_factorizes (cm S1 K : ℝ) :
    matterGhostWeldingWeight cm S1 K =
      matterWeldingWeight cm S1 * bcGhostWeldingWeight S1 K := by
  unfold matterGhostWeldingWeight matterWeldingWeight bcGhostWeldingWeight
    matterGhostWeldingExponent
  rw [Real.exp_add]

/-! ## C. The `Omega` potential difference from Eq. (1.14) -/

/-- The welding potential `c_L S_1 / (24 pi) + 2K`. -/
noncomputable def weldingPotential (cL S1 K : ℝ) : ℝ :=
  cL * S1 / (24 * Real.pi) + 2 * K

/-- Eq. (1.14): `Omega(h₂,h₁) = c_L(S₁(h₂)-S₁(h₁))/(24pi)+2(K(h₂)-K(h₁))`. -/
noncomputable def weldingOmega (cL S1₂ S1₁ K₂ K₁ : ℝ) : ℝ :=
  cL * (S1₂ - S1₁) / (24 * Real.pi) + 2 * (K₂ - K₁)

/-- `Omega` is the difference of the welding potential. -/
lemma weldingOmega_eq_potential_sub (cL S1₂ S1₁ K₂ K₁ : ℝ) :
    weldingOmega cL S1₂ S1₁ K₂ K₁ =
      weldingPotential cL S1₂ K₂ - weldingPotential cL S1₁ K₁ := by
  unfold weldingOmega weldingPotential
  ring

/-- The welding quasi-invariance weight `exp(-Omega)`. -/
noncomputable def weldingRadonNikodymWeight (cL S1₂ S1₁ K₂ K₁ : ℝ) : ℝ :=
  Real.exp (-(weldingOmega cL S1₂ S1₁ K₂ K₁))

/-- No deformation gives unit welding Radon-Nikodym weight. -/
lemma weldingRadonNikodymWeight_self (cL S1 K : ℝ) :
    weldingRadonNikodymWeight cL S1 S1 K K = 1 := by
  simp [weldingRadonNikodymWeight, weldingOmega]

/-- The Radon-Nikodym weight is the exponential of the negative potential difference. -/
lemma weldingRadonNikodymWeight_eq_potential (cL S1₂ S1₁ K₂ K₁ : ℝ) :
    weldingRadonNikodymWeight cL S1₂ S1₁ K₂ K₁ =
      Real.exp (-(weldingPotential cL S1₂ K₂ - weldingPotential cL S1₁ K₁)) := by
  rw [weldingRadonNikodymWeight, weldingOmega_eq_potential_sub]

/-- `Omega` is additive under composition of welding deformations. -/
lemma weldingOmega_cocycle (cL S1₃ S1₂ S1₁ K₃ K₂ K₁ : ℝ) :
    weldingOmega cL S1₃ S1₁ K₃ K₁ =
      weldingOmega cL S1₃ S1₂ K₃ K₂ + weldingOmega cL S1₂ S1₁ K₂ K₁ := by
  unfold weldingOmega
  ring

/-- Reversing a welding deformation changes the sign of `Omega`. -/
lemma weldingOmega_swap (cL S1₂ S1₁ K₂ K₁ : ℝ) :
    weldingOmega cL S1₁ S1₂ K₁ K₂ = -weldingOmega cL S1₂ S1₁ K₂ K₁ := by
  unfold weldingOmega
  ring

/-- The quasi-invariance weights form the multiplicative cocycle associated with `Omega`. -/
lemma weldingRadonNikodymWeight_cocycle (cL S1₃ S1₂ S1₁ K₃ K₂ K₁ : ℝ) :
    weldingRadonNikodymWeight cL S1₃ S1₁ K₃ K₁ =
      weldingRadonNikodymWeight cL S1₃ S1₂ K₃ K₂ *
        weldingRadonNikodymWeight cL S1₂ S1₁ K₂ K₁ := by
  unfold weldingRadonNikodymWeight
  rw [weldingOmega_cocycle, neg_add, Real.exp_add]

/-- The forward and reverse quasi-invariance weights multiply to one. -/
lemma weldingRadonNikodymWeight_mul_swap (cL S1₂ S1₁ K₂ K₁ : ℝ) :
    weldingRadonNikodymWeight cL S1₂ S1₁ K₂ K₁ *
        weldingRadonNikodymWeight cL S1₁ S1₂ K₁ K₂ = 1 := by
  unfold weldingRadonNikodymWeight
  rw [weldingOmega_swap, neg_neg, ← Real.exp_add]
  simp

/-! ## D. Zero-mode factorization from Lemma 6.1 -/

/-- The zero-mode density `exp(-2Q a)` used for the SLE/GFF trace field. -/
noncomputable def sleTraceZeroModeDensity (Q a : ℝ) : ℝ :=
  Real.exp (-(2 * Q * a))

/-- The boundary Liouville zero-mode density `exp(-Q c)`. -/
noncomputable def boundaryLiouvilleZeroModeDensity (Q c : ℝ) : ℝ :=
  Real.exp (-(Q * c))

/-- The product of two independent boundary Liouville zero-mode densities. -/
noncomputable def boundaryLiouvillePairZeroModeDensity (Q c cstar : ℝ) : ℝ :=
  boundaryLiouvilleZeroModeDensity Q c * boundaryLiouvilleZeroModeDensity Q cstar

/-- The scalar change of variables in Lemma 6.1:
`exp(-2Q(a-(x+y)/2)) = exp(Q(x+y)) exp(-2Qa)`. -/
lemma sleTraceZeroModeDensity_shift (Q a x y : ℝ) :
    sleTraceZeroModeDensity Q (a - (x + y) / 2) =
      Real.exp (Q * (x + y)) * sleTraceZeroModeDensity Q a := by
  unfold sleTraceZeroModeDensity
  rw [← Real.exp_add]
  congr 1
  ring

/-- The two boundary zero modes factor as `exp(-Q(c+cstar))`. -/
lemma boundaryLiouvillePairZeroModeDensity_eq_exp_sum (Q c cstar : ℝ) :
    boundaryLiouvillePairZeroModeDensity Q c cstar =
      Real.exp (-(Q * (c + cstar))) := by
  unfold boundaryLiouvillePairZeroModeDensity boundaryLiouvilleZeroModeDensity
  rw [← Real.exp_add]
  congr 1
  ring

/-! ## E. Bridge to the finite Faddeev-Popov ghost complex -/

/-- The welding ghost Jacobian multiplied by the finite Faddeev-Popov determinant supplied by
the repository's ghost-complex interface. -/
noncomputable def ghostComplexWeldingJacobian {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (A : Fin n → ℝ) (S1 K : ℝ) : ℝ :=
  ghostComplexFPDeterminant C A * bcGhostWeldingWeight S1 K

/-- In the abelian finite model, the ghost-complex welding Jacobian is independent of the
chosen gauge-field representative. -/
lemma ghostComplexWeldingJacobian_field_independent {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (A A' : Fin n → ℝ) (S1 K : ℝ) :
    ghostComplexWeldingJacobian C A S1 K = ghostComplexWeldingJacobian C A' S1 K := by
  unfold ghostComplexWeldingJacobian
  rw [ghostComplexFPDeterminant_field_independent C A A']

/-- If the finite Faddeev-Popov determinant is normalized to one, the ghost-complex welding
Jacobian reduces to the `bc` ghost welding weight. -/
lemma ghostComplexWeldingJacobian_eq_bcGhost_of_unit_det {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (A : Fin n → ℝ) (S1 K : ℝ)
    (hdet : ghostComplexFPDeterminant C A = 1) :
    ghostComplexWeldingJacobian C A S1 K = bcGhostWeldingWeight S1 K := by
  simp [ghostComplexWeldingJacobian, hdet]

/-- The ghost-complex condition used by the SBE path-integral layer is the finite BRST
nilpotence condition for the Faddeev-Popov operator. -/
lemma ghostComplexWelding_square_zero {n : ℕ}
    (C : FaddeevPopovGhostComplex n) (alpha : Fin n → ℝ) :
    C.nextVariation.mulVec (C.gaugeVariation.mulVec alpha) = 0 :=
  ghostComplex_square_zero C alpha

end Physlib.QFT.ConformalWelding.MatterLiouvilleGhostFactorization

end
