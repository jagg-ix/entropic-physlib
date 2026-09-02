/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-!
# Greaves–Thomas §5 (Eq. 15): the complex Lorentz inner product and `M ⊂ Mℂ`

Formalizes Eq. 15 and the conjugation facts of §5 of *H. Greaves, T. Thomas, "The CPT Theorem"*
(arXiv:1204.4674) — the ingredients of the complexification underlying the Classical PT Theorem. Complex
Minkowski space is `Mℂ = ℂ ⊗ M`, modelled here as `M × M` (real and imaginary parts: `(a,b) ≙ a + bi`).
The real inner product `η` extends by complex bilinearity to (their Eq. 15)

  `ηℂ(a+bi, c+di) = η(a,c) − η(b,d) + i[η(a,d) + η(b,c)]`.

Complex conjugation on `Mℂ` is `∗ : a+bi ↦ a−bi` (Example 6); its fixed points are exactly the real
vectors `M ⊂ Mℂ`, which is the geometric content of `(PT-3)` — the elements of `L₊` fixed by `∗` are those
preserving `M`.

* **§A — the complex inner product `ηℂ`** (`etaC`, `etaC_real`, `etaC_symm`, `etaC_iAct`). `ηℂ` reproduces
  Eq. 15, restricts to `η` on real vectors, is symmetric when `η` is, and is `ℂ`-homogeneous:
  `ηℂ(i·v, w) = i·ηℂ(v, w)` for the multiplication-by-`i` map `i·(a,b) = (−b,a)` — i.e. Eq. 15 is genuinely
  `ℂ`-bilinear.
* **§B — complex conjugation `∗` on `Mℂ`** (`starM`, `starM_involutive`, `starM_fixed_iff`, `etaC_starM`).
  `∗` is an involution; `∗v = v ⟺ v` is real (`v.2 = 0`); and `ηℂ(∗v, ∗w) = conj(ηℒ(v,w))` — the
  characterization `(gv)∗ = g∗ v∗` of complex conjugation of Example 6, whence `(PT-3)`.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §5 (Eq. 15; Example 6; `(PT-2)`–`(PT-3)`,
  the proper complex Lorentz group and `M ⊂ Mℂ`).
* Repo context: the complex-action lightcone form `ComplexDelta.Convergence.lorentzianForm` is the `1+1` real shadow of
  this complexified inner product.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ComplexLorentzInnerProduct

open Complex

variable {M : Type*} [AddCommGroup M] [Module ℝ M]


/-- **[Greaves–Thomas Eq. 15] The complex Lorentz inner product** `ηℂ` — the complex-bilinear extension of a
real bilinear form `η` to `Mℂ = M × M` (`(a,b) ≙ a + bi`):
`ηℂ(a+bi, c+di) = η(a,c) − η(b,d) + i[η(a,d) + η(b,c)]`. -/
noncomputable def etaC (η : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (v w : M × M) : ℂ :=
  ((η v.1 w.1 - η v.2 w.2 : ℝ) : ℂ) + I * ((η v.1 w.2 + η v.2 w.1 : ℝ) : ℂ)

/-- Multiplication by `i` on `Mℂ = M × M`: `i·(a+bi) = −b + ai`. -/
def iAct (v : M × M) : M × M := (-v.2, v.1)

/-- **`ηℂ` restricts to `η` on real vectors** `ηℂ((a,0),(c,0)) = η(a,c)` — Eq. 15 extends `η`. -/
lemma etaC_real (η : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (a c : M) :
    etaC η (a, 0) (c, 0) = ((η a c : ℝ) : ℂ) := by
  simp [etaC]

/-- **`ηℂ` is symmetric when `η` is** `ηℂ(v,w) = ηℂ(w,v)`. -/
lemma etaC_symm (η : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (hsymm : ∀ a b, η a b = η b a) (v w : M × M) :
    etaC η v w = etaC η w v := by
  simp only [etaC]
  rw [hsymm v.1 w.1, hsymm v.2 w.2, hsymm v.1 w.2, hsymm v.2 w.1]
  ring

/-- **`ηℂ` is `ℂ`-homogeneous in the first argument** `ηℂ(i·v, w) = i · ηℂ(v, w)` — Eq. 15 is genuinely
`ℂ`-bilinear (not merely the real form on `Mℂ`). -/
lemma etaC_iAct (η : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (v w : M × M) :
    etaC η (iAct v) w = I * etaC η v w := by
  simp only [etaC, iAct, map_neg, LinearMap.neg_apply]
  push_cast
  linear_combination (-((η v.1 w.2 : ℂ) + (η v.2 w.1 : ℂ))) * Complex.I_sq


/-- **[Greaves–Thomas Example 6] Complex conjugation on `Mℂ`** `∗(a+bi) = a − bi`. -/
def starM (v : M × M) : M × M := (v.1, -v.2)

omit [Module ℝ M] in
/-- **`∗` is an involution** `∗∗ = id`. -/
lemma starM_involutive (v : M × M) : starM (starM v) = v := by
  simp [starM]

/-- **[(PT-3)] `∗v = v` iff `v` is real** — the fixed points of complex conjugation are exactly the real
vectors `M ⊂ Mℂ`. The `g ∈ L₊` fixed by `∗` are those preserving `M`. -/
lemma starM_fixed_iff (v : M × M) : starM v = v ↔ v.2 = 0 := by
  simp only [starM, Prod.ext_iff, true_and]
  rw [neg_eq_iff_add_eq_zero, ← two_smul ℝ, smul_eq_zero]
  simp

/-- **[Example 6] Conjugation-compatibility** `ηℂ(∗v, ∗w) = conj(ηℂ(v, w))` — the antiholomorphic symmetry
`(gv)∗ = g∗ v∗` of the complex inner product. -/
lemma etaC_starM (η : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (v w : M × M) :
    etaC η (starM v) (starM w) = (starRingEnd ℂ) (etaC η v w) := by
  simp only [etaC, starM, map_neg, LinearMap.neg_apply, neg_neg, map_add, map_mul,
    Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ComplexLorentzInnerProduct

end
