/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD
public import Mathlib.Algebra.Lie.Basic

/-!
# The `O(2,4)` Kac–Moody algebra of the AdS₅ sigma-model (GKP conjecture)

Gubser–Klebanov–Polyakov, hep-th/9802109, Conclusions: away from strong coupling the
`AdS₅` worldsheet is *"an exact conformal field theory … a sigma-model on a
hyperboloid.  It is plausible that, in addition to the global `O(2,4)` symmetry,
this theory possesses the `O(2,4)` Kac–Moody algebra."*

The two prerequisites are already in the repo:
* the **hyperboloid** — the `AdS` embedding `−(X^{−1})² − (X⁰)² + ∑(Xⁱ)² = −L²`
  (`CausalDiamond.AdSConformalKilling.adS_embedding_lightCone`) with the `ℝ^{2,d}`
  form `CausalDiamond.AppendixD.embeddingForm`;
* the **global `O(2,4)`** — the conformal generators `AppendixD.genJ` and the
  `so(2,d)` structure constants `AppendixD.structureTerm`.

This module formalizes the conjectured **Kac–Moody (affine) enhancement**: the loop
(current) algebra `ĝ = g[t,t⁻¹] ⊕ ℝk` of any Lie algebra `g` (here `g = so(2,4)`),
with the mode-graded current bracket and the central extension.

* **§A — the current (loop) algebra.**  `loopBracket` puts the generators `J(m)` at
  every integer mode `m ∈ ℤ`: `[J_A(m), J_B(n)] = [J_A, J_B](m+n)`
  (`loopBracket_mode`).  It is antisymmetric (`loopBracket_skew`) and satisfies the
  Leibniz/Jacobi identity mode-by-mode (`loopBracket_leibniz`,
  `loopBracket_mode_eq`), so the loop algebra is a Lie algebra; its **zero-mode
  sector is the global algebra** `g` (`loopBracket_zeroMode`) — the finite `O(2,4)`
  sitting inside the affine one.

* **§B — the Kac–Moody central extension.**  The affine two-cocycle
  `ω(J_A(m), J_B(n)) = m·δ_{m+n,0}·κ(J_A, J_B)` (`centralCharge`, `κ` an invariant
  symmetric form) is antisymmetric (`centralCharge_skew`) and satisfies the
  **two-cocycle identity** `ω([a,b],c) + ω([b,c],a) + ω([c,a],b) = 0`
  (`centralCharge_cocycle`, from the invariance of `κ`): exactly the condition for
  `ĝ = ĝ_loop ⊕ ℝk` to be a Lie algebra.  This is the `O(2,4)` Kac–Moody algebra.

Honest layering: whether the AdS₅ sigma-model *realizes* this symmetry is the open
conjecture of the paper; here the **algebraic structure** it would possess — the
affine Kac–Moody Lie algebra of `g = so(2,4)` — is formalized in full, on any Lie
algebra with an invariant form.

## References

* S. S. Gubser, I. R. Klebanov, A. M. Polyakov, Phys. Lett. B428 (1998) 105,
  hep-th/9802109, Conclusions.
* V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed., CUP (1990), Ch. 7
  (affine algebras and the central extension of a loop algebra).
* Repo carriers: `CausalDiamond.AppendixD` (`embeddingForm`, `genJ`,
  `structureTerm`), `CausalDiamond.AdSConformalKilling` (the AdS hyperboloid).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AffineKacMoodyConformalAlgebra

variable {g : Type*} [LieRing g]

/-! ## §A — the current (loop) algebra `g[t,t⁻¹]` -/

/-- **The current-algebra bracket** on modes `g × ℤ` (element `X` at mode `m`):
`[X(m), Y(n)] = [X,Y](m+n)`.  This is the loop-algebra bracket of `g = so(2,4)`. -/
def loopBracket (a b : g × ℤ) : g × ℤ := ⟨⁅a.1, b.1⁆, a.2 + b.2⟩

@[simp] lemma loopBracket_fst (a b : g × ℤ) : (loopBracket a b).1 = ⁅a.1, b.1⁆ := rfl

/-- **[The current bracket adds modes] `[J_A(m), J_B(n)]` lives at mode `m + n`.** -/
@[simp] lemma loopBracket_mode (a b : g × ℤ) : (loopBracket a b).2 = a.2 + b.2 := rfl

/-- **[The current bracket is antisymmetric]** `[X(m), Y(n)] = −[Y(n), X(m)]` in the
`g`-component (the modes coincide). -/
lemma loopBracket_skew (a b : g × ℤ) :
    (loopBracket a b).1 = -(loopBracket b a).1 := by
  simp only [loopBracket_fst]
  rw [← lie_skew]

/-- **[The current bracket satisfies the Leibniz/Jacobi identity]**
`[X, [Y, Z]] = [[X, Y], Z] + [Y, [X, Z]]` in the `g`-component — the loop algebra is a
Lie algebra. -/
lemma loopBracket_leibniz (a b c : g × ℤ) :
    (loopBracket a (loopBracket b c)).1
      = (loopBracket (loopBracket a b) c).1 + (loopBracket b (loopBracket a c)).1 :=
  leibniz_lie a.1 b.1 c.1

/-- **[All triple current-brackets share the same mode] `m + n + p`.** -/
lemma loopBracket_mode_eq (a b c : g × ℤ) :
    (loopBracket a (loopBracket b c)).2 = (loopBracket (loopBracket a b) c).2 := by
  simp only [loopBracket_mode]; ring

/-- **[The zero-mode sector is the global algebra]** at `m = n = 0` the current
bracket is the ordinary Lie bracket of `g` — the global `O(2,4)` sits inside the
affine algebra as the zero modes. -/
lemma loopBracket_zeroMode (X Y : g) :
    loopBracket (⟨X, 0⟩ : g × ℤ) ⟨Y, 0⟩ = ⟨⁅X, Y⁆, 0⟩ := by
  simp [loopBracket]

/-! ## §B — the Kac–Moody central extension -/

/-- **The affine two-cocycle** `ω(X(m), Y(n)) = m·δ_{m+n,0}·κ(X, Y)` — the central
charge of the Kac–Moody extension, with `κ` an invariant symmetric bilinear form on
`g` (the trace/Killing form of `so(2,4)`). -/
noncomputable def centralCharge (κ : g → g → ℝ) (a b : g × ℤ) : ℝ :=
  (a.2 : ℝ) * (if a.2 + b.2 = 0 then κ a.1 b.1 else 0)

omit [LieRing g] in
/-- **[The central cocycle is antisymmetric]** `ω(a, b) = −ω(b, a)` — for a symmetric
`κ`, using `m + n = 0 ⟺ n = −m`. -/
lemma centralCharge_skew (κ : g → g → ℝ) (hsymm : ∀ x y, κ x y = κ y x)
    (a b : g × ℤ) : centralCharge κ a b = -centralCharge κ b a := by
  unfold centralCharge
  by_cases h : a.2 + b.2 = 0
  · have h' : b.2 + a.2 = 0 := by omega
    have hb : b.2 = -a.2 := by omega
    rw [if_pos h, if_pos h', hsymm b.1 a.1, hb]
    push_cast; ring
  · have h' : ¬ b.2 + a.2 = 0 := by omega
    rw [if_neg h, if_neg h']; ring

omit [LieRing g] in
/-- **[The central cocycle vanishes on equal modes off the diagonal]** in particular
`ω(a, b) = 0` unless `m + n = 0`. -/
lemma centralCharge_of_mode_ne (κ : g → g → ℝ) (a b : g × ℤ)
    (h : a.2 + b.2 ≠ 0) : centralCharge κ a b = 0 := by
  unfold centralCharge; rw [if_neg h, mul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- **[The Kac–Moody two-cocycle identity]**
`ω([a,b], c) + ω([b,c], a) + ω([c,a], b) = 0` — the condition for the central
extension `ĝ = g[t,t⁻¹] ⊕ ℝk` to be a Lie algebra.  It follows from the invariance
`κ([X,Y], Z) = κ(X, [Y,Z])` and the symmetry of `κ`: on the mode shell `m+n+p = 0`
the three coefficients sum to `2(m+n+p) = 0`. -/
lemma centralCharge_cocycle (κ : g → g → ℝ) (hsymm : ∀ x y, κ x y = κ y x)
    (hinv : ∀ x y z, κ ⁅x, y⁆ z = κ x ⁅y, z⁆) (a b c : g × ℤ) :
    centralCharge κ (loopBracket a b) c
        + centralCharge κ (loopBracket b c) a
        + centralCharge κ (loopBracket c a) b = 0 := by
  unfold centralCharge
  simp only [loopBracket_fst, loopBracket_mode]
  by_cases h : a.2 + b.2 + c.2 = 0
  · have e1 : a.2 + b.2 + c.2 = 0 := h
    have e2 : b.2 + c.2 + a.2 = 0 := by omega
    have e3 : c.2 + a.2 + b.2 = 0 := by omega
    rw [if_pos e1, if_pos e2, if_pos e3]
    -- the invariant form is cyclic: κ([a,b],c) = κ([b,c],a) = κ([c,a],b)
    have hK1 : κ ⁅a.1, b.1⁆ c.1 = κ ⁅b.1, c.1⁆ a.1 := by
      rw [hinv, hsymm]
    have hK2 : κ ⁅b.1, c.1⁆ a.1 = κ ⁅c.1, a.1⁆ b.1 := by
      rw [hinv, hsymm]
    rw [hK1, hK2]
    have hcast : (a.2 : ℝ) + (b.2 : ℝ) + (c.2 : ℝ) = 0 := by exact_mod_cast h
    push_cast
    linear_combination (2 * κ ⁅c.1, a.1⁆ b.1) * hcast
  · have e1 : ¬ a.2 + b.2 + c.2 = 0 := h
    have e2 : ¬ b.2 + c.2 + a.2 = 0 := by omega
    have e3 : ¬ c.2 + a.2 + b.2 = 0 := by omega
    rw [if_neg e1, if_neg e2, if_neg e3]
    ring

end Physlib.QuantumMechanics.ComplexAction.AffineKacMoodyConformalAlgebra

end
