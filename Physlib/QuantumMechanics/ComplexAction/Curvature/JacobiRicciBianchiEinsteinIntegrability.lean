/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Einstein field equations as integrability conditions of the JRB system (Van den Bergh's theorems)

The central theorems of:

> N. Van den Bergh, *On the relation between the Einstein field equations and the Jacobi–Ricci–Bianchi
> system*, Class. Quantum Grav. **31** (2014) 145007; doi:10.1088/0264-9381/31/14/145007;
> preprint **arXiv:1302.6448v3** [gr-qc] (10 June 2013); PACS 04.20.Jb. (Dept. of Mathematical Analysis EA16,
> Ghent University; norbert.vandenbergh@ugent.be.)

The field equations `𝒴_αβ = 0` (Eqs (53)–(54), p. 10) arise as **integrability conditions** of the
Jacobi–Ricci–Bianchi (JRB) system, provided the congruence is *generic*. The bulk of the paper (the 1+3 /
Newman–Penrose component equations (33)–(65), pp. 7–13, computed with Maple) is the frame-derivative calculus;
this file isolates the *decisive logic* of each theorem (Theorems 1–3, pp. 11–13, and the uniqueness argument
Eqs (62)–(63), p. 11).

* **§A — Theorem 1 (timelike generic congruence; Theorem 1, p. 11).** Aligning `∂₃` with the acceleration `u̇`
 (magnitude `a ≠ 0`), the acceleration equations (Eqs (58)–(60), pp. 10–11) force `𝒴₁₂=𝒴₂₃=𝒴₃₁=𝒴₁₁=𝒴₂₂=0`,
 and the vorticity equation (Eq (61), p. 11) gives `(σ₃₁−ω₂)𝒴₃₃ = (σ₂₃+ω₁)𝒴₃₃ = 0`, so `𝒴₃₃=0` **unless `u̇`
 is an eigenvector of `σ+ω`** (`einstein_integrability_timelike`).
* **§B — the covariant uniqueness argument (Eqs (62)–(63), p. 11).** The curvature tensor of a metric
 connection is the *unique* tensor with the Riemann symmetries (Eq (18), p. 4), both Bianchi identities
 (Eqs (14), p. 3 and (17), p. 3), and the Ricci equations (Eq (26), p. 5). The difference `A` of two
 candidates has the Riemann symmetries and (by contracting the second Bianchi with `u` and `u̇`, `u=e₀`,
 `u̇=e₃` — Eq (62), p. 11) vanishes whenever any index is `0` or `3` — it is confined to the `{e₁,e₂}` plane,
 where its single component `A₁₂₁₂` is killed by Eq (63), p. 11, so `A = 0` (`riemann_difference_unique`).
* **§C — Theorems 2 & 3 (the homogeneous-system principle).** The second-Bianchi case (`[I,H]=0`, `I`
 non-degenerate, `q` generic — **Theorem 2, p. 12**, systems Eqs (64)–(65), p. 12) and the null Newman–Penrose
 case (`κ = −k_{a;b}mᵃkᵇ ≠ 0` — **Theorem 3, p. 13**, NP equations Eqs (66)–(68), p. 13) reduce the field
 equations to a homogeneous system `M·Y = 0` whose coefficient matrix is invertible under the genericity
 condition; an invertible matrix has trivial kernel, so `Y = 0` (`einstein_integrability_of_invertible`,
 `einstein_integrability_secondBianchi`, `einstein_integrability_null`).

Proven: (§A) the decisive linear reduction of Theorem 1 from the acceleration/vorticity
integrability equations plus the non-eigenvector genericity; (§B) the curvature-uniqueness reduction to a
single planar component and its vanishing, on the `IsRiemannCurvature` symmetries; (§C) the homogeneous-system
principle (invertible coefficient matrix ⟹ trivial field-equation solution), with the paper's genericity
conditions identified with that invertibility. The Maple-computed component equations 33–65 and the
contraction `2nd Bianchi · u → A_{ab[cd}u^b_{;e]}=0` themselves use frame-derivative machinery not in physlib
and are taken as the (faithful) structural inputs.

## References

* **Primary source.** N. Van den Bergh, *On the relation between the Einstein field equations and the
 Jacobi–Ricci–Bianchi system*, Class. Quantum Grav. **31** (2014) 145007,
 doi:10.1088/0264-9381/31/14/145007; arXiv:1302.6448v3 [gr-qc] (10 June 2013); PACS 04.20.Jb.
 — Theorem 1 (p. 11), Theorem 2 (p. 12), Theorem 3 (p. 13); uniqueness Eqs (62)–(63) (p. 11);
 field equations `𝒴_αβ` Eqs (53)–(54) (p. 10); reduction systems Eqs (58)–(61) (pp. 10–11);
 NP equations Eqs (66)–(68) (p. 13).
* `Physlib` (`Curvature.RiemannCurvatureTensor.IsRiemannCurvature`, `Curvature.JacobiRicciBianchiTetrad`,
 `Curvature.SecondBianchiCyclicFamily`); Mathlib (`Matrix.mulVec_injective_of_invertible`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiEinsteinIntegrability

/-! ## §A — Theorem 1: the timelike generic congruence -/

/-- **[Theorem 1 — Van den Bergh, CQG 31 (2014) 145007 / arXiv:1302.6448v3, p. 11]** the Einstein field
equations are the integrability conditions of the JRB system for a generic timelike congruence. With `∂₃`
aligned to the acceleration (magnitude `a ≠ 0`), the acceleration integrability equations (Eqs (58)–(60),
pp. 10–11) force `𝒴₁₂=𝒴₂₃=𝒴₃₁=𝒴₁₁=𝒴₂₂=0`; the vorticity equation (Eq (61), p. 11) gives
`(σ₃₁−ω₂)𝒴₃₃ = (σ₂₃+ω₁)𝒴₃₃ = 0`; hence all `𝒴` vanish unless `u̇` is an eigenvector of `σ+ω` (i.e. unless
`σ₃₁=ω₂` and `σ₂₃=−ω₁`). The `𝒴_αβ` are the trace-free Einstein field-equation components (Eqs (53)–(54),
p. 10). -/
theorem einstein_integrability_timelike
    (a Y12 Y23 Y31 Y11 Y22 Y33 s31 w2 s23 w1 : ℝ) (ha : a ≠ 0)
    (e12 : a * Y12 = 0) (e23 : a * Y23 = 0) (e31 : a * Y31 = 0)
    (e11 : a * Y11 = 0) (e22 : a * Y22 = 0)
    (e33a : (s31 - w2) * Y33 = 0) (e33b : (s23 + w1) * Y33 = 0)
    (hgen : ¬ (s31 - w2 = 0 ∧ s23 + w1 = 0)) :
    Y12 = 0 ∧ Y23 = 0 ∧ Y31 = 0 ∧ Y11 = 0 ∧ Y22 = 0 ∧ Y33 = 0 := by
  refine ⟨(mul_eq_zero.mp e12).resolve_left ha, (mul_eq_zero.mp e23).resolve_left ha,
    (mul_eq_zero.mp e31).resolve_left ha, (mul_eq_zero.mp e11).resolve_left ha,
    (mul_eq_zero.mp e22).resolve_left ha, ?_⟩
  rcases not_and_or.mp hgen with h | h
  · exact (mul_eq_zero.mp e33a).resolve_left h
  · exact (mul_eq_zero.mp e33b).resolve_left h

/-! ## §B — the covariant uniqueness of the curvature tensor (Eqs 62–63) -/

/-- **[The curvature tensor is unique — Van den Bergh arXiv:1302.6448v3, Eqs (62)–(63), p. 11]** a tensor `A`
with the Riemann symmetries (`IsRiemannCurvature`; Eq (18), p. 4) that vanishes on the last index at `0` and
`3` (the contraction of the second Bianchi Eq (17) with `u = e₀` and then `u̇ = e₃`, giving
`A_{ab[cd}u^b_{;e]}=0`, Eq (62), p. 11) is confined to the `{e₁,e₂}` plane; if in addition its single planar
component `A₁₂₁₂` vanishes (Eq (63), p. 11, the non-eigenvector condition), then `A = 0`. Hence the difference
of two curvature tensors with the same symmetries / Bianchi / Ricci (Eq (26), p. 5) data vanishes — the
curvature tensor is the unique such tensor (the basis of Theorem 1). -/
theorem riemann_difference_unique
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (h : IsRiemannCurvature A)
    (hu : ∀ a b c, A a b c 0 = 0) (hud : ∀ a b c, A a b c 3 = 0)
    (h1212 : A 1 2 1 2 = 0) :
    A = 0 := by
  have v_c0 : ∀ a b d, A a b 0 d = 0 := fun a b d => by
    rw [h.antisymm_right a b 0 d, hu a b d, neg_zero]
  have v_c3 : ∀ a b d, A a b 3 d = 0 := fun a b d => by
    rw [h.antisymm_right a b 3 d, hud a b d, neg_zero]
  have v_b0 : ∀ a c d, A a 0 c d = 0 := fun a c d => by
    rw [h.pair_symm a 0 c d]; exact hu c d a
  have v_b3 : ∀ a c d, A a 3 c d = 0 := fun a c d => by
    rw [h.pair_symm a 3 c d]; exact hud c d a
  have v_a0 : ∀ b c d, A 0 b c d = 0 := fun b c d => by
    rw [h.pair_symm 0 b c d]; exact v_c0 c d b
  have v_a3 : ∀ b c d, A 3 b c d = 0 := fun b c d => by
    rw [h.pair_symm 3 b c d]; exact v_c3 c d b
  have diagL : ∀ a c d, A a a c d = 0 := fun a c d => by
    have := h.antisymm_left a a c d; linarith
  have diagR : ∀ a b c, A a b c c = 0 := fun a b c => by
    have := h.antisymm_right a b c c; linarith
  -- the three off-diagonal `{1,2}`-plane components, killed by `h1212` (Eq 63)
  have h1221 : A 1 2 2 1 = 0 := by have := h.antisymm_right 1 2 1 2; linarith
  have h2112 : A 2 1 1 2 = 0 := by have := h.antisymm_left 1 2 1 2; linarith
  have h2121 : A 2 1 2 1 = 0 := by have := h.antisymm_left 1 2 2 1; linarith [h1221]
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
      | exact hu _ _ _
      | exact hud _ _ _
      | exact v_c0 _ _ _
      | exact v_c3 _ _ _
      | exact v_b0 _ _ _
      | exact v_b3 _ _ _
      | exact v_a0 _ _ _
      | exact v_a3 _ _ _
      | exact diagL _ _ _
      | exact diagR _ _ _
      | exact h1212
      | exact h1221
      | exact h2112
      | exact h2121

/-! ## §C — Theorems 2 & 3: the homogeneous-system principle -/

/-- **[The homogeneous-system principle]** if the field-equation vector `Y` lies in the kernel of an
**invertible** coefficient matrix `M` (`M·Y = 0`), then `Y = 0`. This is the linear-algebraic core of
Theorems 2 and 3: the genericity condition makes the system's determinant non-vanishing. -/
theorem einstein_integrability_of_invertible {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) [Invertible M]
    (Y : Fin n → ℝ) (hMY : M.mulVec Y = 0) : Y = 0 :=
  Matrix.mulVec_injective_of_invertible M (by rw [hMY, Matrix.mulVec_zero])

/-- **[Theorem 2 — Van den Bergh arXiv:1302.6448v3, p. 12]** (second-Bianchi / `[I,H]=0` case) when `[I,H]=0`,
`I_αβ` is non-degenerate and `q` is not parallel to an eigenblade of `H`, the `6×6` coefficient matrix of the
system Eqs (64)–(65) (p. 12) is invertible, so the field-equation vector vanishes — the Einstein equations are
integrability conditions of the JRB system. (`I_ab = E_ab − ½π_ab`, `J_ab = H_ab − ½η_{abcd}qᶜuᵈ`.) -/
theorem einstein_integrability_secondBianchi (M : Matrix (Fin 6) (Fin 6) ℝ) [Invertible M]
    (Y : Fin 6 → ℝ) (hMY : M.mulVec Y = 0) : Y = 0 :=
  einstein_integrability_of_invertible M Y hMY

/-- **[Theorem 3 — Van den Bergh arXiv:1302.6448v3, p. 13]** (null / Newman–Penrose case) when
`κ = −k_{a;b}mᵃkᵇ ≠ 0`, the Newman–Penrose coefficient matrix is invertible, so the remaining NP equations
`NP₁₀, NP₁₃, NP₁₂+\overline{NP₁₂}, NP₁₄+\overline{NP₁₄}` (Eq (68), p. 13) are the integrability conditions of
the remaining NP and Bianchi equations (the NP set Eqs (66)–(67), pp. 12–13). -/
theorem einstein_integrability_null (M : Matrix (Fin 6) (Fin 6) ℝ) [Invertible M]
    (NP : Fin 6 → ℝ) (hM : M.mulVec NP = 0) : NP = 0 :=
  einstein_integrability_of_invertible M NP hM

end Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiEinsteinIntegrability

end
