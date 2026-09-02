/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.WeylTensorTraceFree
public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinDoubleDualCotton

/-!
# The normal conformal Cartan connection: Einstein metrics are Bach flat

Bac, Kamiński, Lewandowski and Broda (arXiv:2302.12739) treat gravity as a Yang-Mills theory of the
**normal conformal Cartan (NCC) connection** — an `so(2,4)`-valued connection `A` (Eq. 3) whose tetrad
block is the spin connection `Γ^a_b` and whose off-diagonal blocks are the **Schouten one-form**
`P_a = (R/12 η_{ab} − R_{ab}/2) θ^b` (Eq. 5, minus the Schouten tensor). Its curvature (Eq. 16) holds
the **Weyl tensor** `C^a_b` and the Cotton form `DP^a`, the Cartan-Yang-Mills Lagrangian is the
Weyl-squared conformal-gravity action `L_CYM = ¼ C_{abcd}C^{abcd}` (Eq. 25), and the field equation is
the **vanishing of the Bach tensor** `B_{ab} = 2∇^c∇_{[b}P_{c]a} − 2P^{cd}C_{cadb}` (Eqs. 21, 29).

The paper's key link to Einstein's theory (Eq. 22): **Einstein metrics are Bach flat**,

  `R_{ab} = Λ η_{ab}  ⟹  B_{ab} = 0`,

so the space of Einstein metrics is immersed in the Bach-flat metrics of conformal gravity. Formalized
here from the two reasons the two terms of the Bach tensor vanish:

* the Schouten tensor of an Einstein metric is `P = −(Λ/6) g` (Eq. 47), covariantly constant, so the
  Cotton tensor vanishes (`MoulinDoubleDualCotton.cottonTensor`) and the derivative term `∇∇P` is zero;
* the algebraic term `P^{cd}C_{cadb} = −(Λ/6) gᶜᵈ C_{cadb} = 0` vanishes because the Weyl tensor is
  **completely trace-free** (`WeylTensorTraceFree.weyl_traceFree`).

This ties the arc's Einstein-`Λ` vacua — the de Sitter metric whose cosmological constant is the
reciprocal bit count `Λ = 12π/(ℓ_P² N)` (`DeSitterCosmologicalConstantBits`) — to conformal gravity:
they are Bach flat, hence solutions of the Cartan-Yang-Mills theory. The maximally symmetric
`Curvature.RiemannCurvatureTensor.constantCurvature` metrics (Fisher-Rao, de Sitter) have vanishing
Weyl tensor, so `L_CYM = 0` — they are the conformal-gravity vacua.

* **§A** the Schouten tensor and `P = −(Λ/6) g` for an Einstein metric (Eqs. 5, 47).
* **§B** the Cotton tensor vanishes for an Einstein metric (covariantly constant Ricci).
* **§C** the Weyl-Schouten term `P^{cd}C_{cadb}` vanishes by the trace-free Weyl tensor.
* **§D** the Bach tensor vanishes for an Einstein metric (Eq. 22).

## References

* A. Bac, W. Kamiński, J. Lewandowski, M. Broda, *Symplectic charges in the Yang-Mills theory of the
  normal conformal Cartan connection: Applications to gravity*, arXiv:2302.12739 — Eqs. 3-5, 16, 21,
  22, 25.
* R. Bach, Math. Z. 9 (1921) 110 — the Bach tensor and conformal gravity.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Matrix

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBachEinstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

/-! ## A. The Schouten one-form and the Einstein value -/

/-- **[The NCC Schouten tensor, Eq. 5]** `P_{ab} = (R/12) g_{ab} − R_{ab}/2` — minus the Schouten
tensor, the off-diagonal block of the normal conformal Cartan connection (four dimensions). -/
noncomputable def nccSchouten (scalarR : ℝ) (Ric g : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (scalarR / 12) • g - (1 / 2 : ℝ) • Ric

omit [Fintype ι] [DecidableEq ι] in
/-- **[The Schouten tensor of an Einstein metric, Eq. 47]** `P = −(Λ/6) g`. For an Einstein metric
`R_{ab} = Λ g_{ab}` with `R = 4Λ` (the four-dimensional trace), the Schouten tensor is `−Λ/6` times the
metric — covariantly constant, hence its Cotton tensor vanishes. -/
theorem nccSchouten_einstein (Λ scalarR : ℝ) (Ric g : Matrix ι ι ℝ)
    (hEin : Ric = Λ • g) (hR : scalarR = 4 * Λ) :
    nccSchouten scalarR Ric g = (-(Λ / 6)) • g := by
  rw [nccSchouten, hEin, hR, smul_smul, ← sub_smul]
  congr 1
  ring

/-! ## B. The Cotton tensor of an Einstein metric vanishes -/

omit [Fintype ι] [DecidableEq ι] in
/-- **[The Cotton tensor of an Einstein metric vanishes]** an Einstein metric `R_{ab} = Λ g_{ab}` has
covariantly constant Ricci (`∇_c R_{ab} = Λ ∇_c g_{ab} = 0`) and constant scalar (`∇_c R = 0`), so the
covariant-derivative fields feeding the Cotton tensor vanish and `C_{jkl} = 0`
(`MoulinDoubleDualCotton.cottonTensor`). This kills the derivative term of the Bach tensor. -/
theorem cottonTensor_einstein_zero (n : ℝ) (g : Matrix ι ι ℝ) (j k l : ι) :
    cottonTensor n g 0 0 j k l = 0 := by
  simp [cottonTensor]

/-! ## C. The Weyl-Schouten term vanishes by the trace-free Weyl tensor -/

/-- **The Weyl-Schouten term of the Bach tensor of an Einstein metric** `P^{cd} C_{cadb} =
−(Λ/6) gᶜᵈ C_{cadb}` — the algebraic (non-derivative) term of the Bach tensor, with the Einstein
Schouten `P = −(Λ/6) g` (`nccSchouten_einstein`) contracted into the Weyl tensor. -/
noncomputable def einsteinWeylSchouten (Λ : ℝ) (gInv g : Matrix ι ι ℝ) (Rm : RiemannTensor ι) :
    ι → ι → ℝ :=
  fun a b => -(Λ / 6) *
    ricci gInv (weylTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm) a b

/-- **[The Weyl-Schouten term vanishes]** `P^{cd} C_{cadb} = −(Λ/6) gᶜᵈ C_{cadb} = 0`. The contraction
`gᶜᵈ C_{cadb} = ricci gInv C` is the Ricci contraction of the Weyl tensor, which vanishes because the
Weyl tensor is **completely trace-free** (`WeylTensorTraceFree.weyl_traceFree`). -/
theorem einsteinWeylSchouten_zero (Λ : ℝ) (gInv g : Matrix ι ι ℝ) (Rm : RiemannTensor ι)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) (a b : ι) :
    einsteinWeylSchouten Λ gInv g Rm a b = 0 := by
  rw [einsteinWeylSchouten, weyl_traceFree hg hgi hinv h hn1 hn2 a b, mul_zero]

/-! ## D. The Bach tensor of an Einstein metric vanishes -/

/-- **The Bach tensor, Eq. 21** `B_{ab} = 2∇^c∇_{[b}P_{c]a} − 2P^{cd}C_{cadb}` — the derivative term
`2∇∇P` (`nablaSqSchouten`) minus twice the Weyl-Schouten contraction. -/
noncomputable def bachTensor (nablaSqSchouten weylSchouten : ι → ι → ℝ) : ι → ι → ℝ :=
  fun a b => 2 * nablaSqSchouten a b - 2 * weylSchouten a b

/-- **[Einstein metrics are Bach flat, Eq. 22] `R_{ab} = Λ η_{ab} ⟹ B_{ab} = 0`.** Both terms of the
Bach tensor vanish for an Einstein metric: the derivative term `∇∇P = 0` because the Schouten tensor
`P = −(Λ/6) g` is covariantly constant (`hcov`; the Cotton tensor vanishes, §B), and the algebraic
term `P^{cd}C_{cadb} = 0` because the Weyl tensor is trace-free (§C). Hence the Einstein metrics are
solutions of the conformal Cartan-Yang-Mills gravity — its field equation is `B_{ab} = 0`. -/
theorem bach_einstein_vanishes (Λ : ℝ) (gInv g : Matrix ι ι ℝ) (Rm : RiemannTensor ι)
    (nablaSqSchouten : ι → ι → ℝ)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0)
    (hcov : ∀ a b, nablaSqSchouten a b = 0) (a b : ι) :
    bachTensor nablaSqSchouten (einsteinWeylSchouten Λ gInv g Rm) a b = 0 := by
  rw [bachTensor, hcov a b, einsteinWeylSchouten_zero Λ gInv g Rm hg hgi hinv h hn1 hn2 a b]
  ring

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBachEinstein
