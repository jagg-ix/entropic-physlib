/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Kuratowski

/-!
# Johnson–Lindenstrauss Lipschitz-extension constants (`L(X,n) ≤ C √log n`, `L(X,n) ≤ 6D/ε`)

The companion of `AdSCFT.JohnsonLindenstraussHolographicReduction` (which formalized the *reduction* face — the
`JLBound` distance distortion, the logarithmic target dimension, and holography as the exact `ε = 0` case). This
module formalizes the exact-algebra cores of the paper's actual subject: the **Lipschitz extension constant**
`L(X, n)`, the smallest `L` so that every `f : A → ℓ₂` from every `n`-element `A ⊂ X` extends to `f̃ : X → ℓ₂`
with `‖f̃‖_Lip ≤ L ‖f‖_Lip` (Johnson–Lindenstrauss, *Extensions of Lipschitz mappings into a Hilbert space*,
Contemp. Math. 26 (1984)).

The two upper bounds are built from three ingredients each — a `k`-dimensional Johnson–Lindenstrauss reduction, the
**formal identity** `I : ℓ₂ᵏ → ℓ∞ᵏ`, and a non-linear extension (Kirszbraun / non-linear Hahn–Banach) — and the
constant is the *product of their Lipschitz bounds*:

* **Theorem 1** `L(X, n) ≤ C √(log n)`: the formal identity `I : ℓ₂ᵏ → ℓ∞ᵏ` has `‖I‖ = 1` and `‖I⁻¹‖ = √k`, so a
 bi-Lipschitz reduction into `ℓ₂ᵏ` (`‖g̃‖ ≤ 3`) followed by `I⁻¹` and a Hahn–Banach extension (`‖h‖ ≤ 1`) gives
 `‖f̃‖ ≤ 3√k`, and with `k = ⌈K log n⌉` (`jlTargetDim`) this is `3K √(log n)`;
* **Theorem 2 / Benyamini** `L(X, n) ≤ 6D/ε` (resp. `4D/ε`) for an `ε`-separated `A` of diameter `D`: the map
 `b ↦ δ_b` into `ℓ₁` is `2/ε`-Lipschitz (distinct unit vectors are `2` apart, points ≥ `ε` apart), composed with a
 `D`-bounded `G : ℓ₁ → ℓ₂` and a Grothendieck factorization of constant `3` (resp. Benyamini's retraction of
 constant `2`).

* **§A — the formal identity `ℓ₂ᵏ → ℓ∞ᵏ` norms** (`coord_sq_le_euclideanNormSq` = `‖I‖ ≤ 1`,
 `euclideanNormSq_le_card_mul_sup` = `‖I⁻¹‖ ≤ √k`).
* **§B — Theorem 1, the `√log n` extension constant** (`extension_constant_le` composition `≤ 3√k`;
 `extension_constant_sqrt_log` `3√k ≤ 3K√(log n)` for `k ≤ K log n`).
* **§C — Theorem 2 / Benyamini, the `D/ε` extension constant** (`separated_map_lipschitz_le` `2/d ≤ 2/ε`;
 `theorem2_composite` `‖f̃‖ ≤ 6D/ε`; `theorem2_extension_constant`, `benyamini_extension_constant`).
* **§D — the Benyamini retraction Lipschitz cores** (`positivePart_nonexpansive` `|x⁺ − y⁺| ≤ |x − y|`;
 `benyamini_positivePart_two_lipschitz` `|(2a−1)⁺ − (2b−1)⁺| ≤ 2|a − b|`).
* **§E — Lemma 2, the positively homogeneous extension** (`homogExtend` `f̃(y) = ‖y‖ f(y/‖y‖)`;
 `norm_scaled_sub_le` `‖(‖y₂‖/‖y₁‖)•y₁ − y₂‖ ≤ 2‖y₁ − y₂‖`; `homogExtend_lipschitz_bound`
 `‖f̃‖_Lip ≤ ‖f‖_∞ + 2‖f‖_Lip`).
* **§F — the non-linear Hahn–Banach (McShane) extension** (`hahnBanach_extend_linfty` — constant-preserving into
 `ℓ∞ᵏ`, Theorem 1; `hahnBanach_extend_lInfty` — constant-preserving into `ℓ∞(Γ)`, Theorem 2 / Benyamini;
 `hahnBanach_extend_finiteDim` — the finite-dimensional case), sourced from Mathlib's `LipschitzOnWith.extend_pi`
 / `extend_lp_infty` / `extend_finite_dimension`.

The formal-identity norm bounds, the constant compositions, the `√log n` arithmetic, the
`ε`-separation ratio, the positive-part Lipschitz cores, and the positively homogeneous extension (§E) are exact
algebra / exact normed-space inequalities, reusing `jlTargetDim` and elementary `Finset`/`Real.sqrt`/normed-space
lemmas. The **non-linear Hahn–Banach extension** (§F) — the step supplying `‖h̃‖_Lip ≤ ‖f‖_Lip` into `ℓ∞ᵏ` in
Theorem 1 — is now *derived*, sourced from Mathlib's McShane extension `LipschitzOnWith.extend_pi` (the same
theorem Mathlib itself labels "the nonlinear Hahn–Banach theorem"). The remaining analytic inputs are the
*referenced* content, not re-derived here: Kirszbraun's theorem (the reduction's extension into `ℓ₂`),
Grothendieck's inequality (the `ℓ₁ → ℓ₂` factorization), the Lévy isoperimetric / Khintchine concentration behind
Lemma 1's random projection, the volume packing of Lemma 3's `ε`-net `(1 + 4/ε)ⁿ`, the projection constants of
Lemma 4, the smoothing of Lemma 5, the lower bound of Theorem 3, and the linearization of Proposition 1. No new
axioms.

## References

* W.B. Johnson, J. Lindenstrauss, *Extensions of Lipschitz mappings into a Hilbert space*, Contemp. Math. 26
 (1984) 189 (Theorems 1–2, Lemmas 1–6). Repo companion:
 `AdSCFT.JohnsonLindenstraussHolographicReduction` (`JLBound`, `jlTargetDim`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussLipschitzExtension

/-! ## §A — the formal identity `ℓ₂ᵏ → ℓ∞ᵏ` norms (`‖I‖ = 1`, `‖I⁻¹‖ = √k`) -/

/-- The squared Euclidean (`ℓ₂ᵏ`) norm `‖x‖² = ∑ᵢ x(i)²` of a `k`-vector — the norm on the reduced space that a
Johnson–Lindenstrauss reduction lands in. -/
def euclideanNormSq {k : ℕ} (x : Fin k → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- **[The formal identity `I : ℓ₂ᵏ → ℓ∞ᵏ` has `‖I‖ ≤ 1`] `x(i)² ≤ ‖x‖₂²`.** Each coordinate (the `ℓ∞` sup) is
bounded by the Euclidean norm: the identity `ℓ₂ᵏ → ℓ∞ᵏ` is a contraction, `‖I‖ = 1` (Johnson–Lindenstrauss,
Theorem 1). -/
theorem coord_sq_le_euclideanNormSq {k : ℕ} (x : Fin k → ℝ) (i : Fin k) :
    (x i) ^ 2 ≤ euclideanNormSq x := by
  unfold euclideanNormSq
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- **[The formal identity inverse `I⁻¹ : ℓ∞ᵏ → ℓ₂ᵏ` has `‖I⁻¹‖ ≤ √k`] `‖x‖₂² ≤ k · sup²`.** If every coordinate
square is bounded by `M` (the squared `ℓ∞` norm), the Euclidean norm square is at most `k · M`, so `‖x‖₂ ≤ √k · ‖x‖∞`:
the inverse identity `ℓ∞ᵏ → ℓ₂ᵏ` has norm `√k`. This `√k` is the factor turning a bi-Lipschitz `ℓ₂`-reduction into
an `ℓ∞` one and, with `k = ⌈K log n⌉`, produces the `√log n` extension constant of Theorem 1. -/
theorem euclideanNormSq_le_card_mul_sup {k : ℕ} (x : Fin k → ℝ) (M : ℝ)
    (h : ∀ i, (x i) ^ 2 ≤ M) : euclideanNormSq x ≤ (k : ℝ) * M := by
  unfold euclideanNormSq
  calc ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin k, M := Finset.sum_le_sum (fun i _ => h i)
    _ = (k : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## §B — Theorem 1: the `√log n` extension constant -/

/-- **[The Theorem 1 extension constant is `3√k`] `‖g̃‖ · ‖I⁻¹‖ · ‖h‖ ≤ 3√k`.** The Lipschitz extension `f̃` is the
composite of a Kirszbraun extension of the reduction (`‖g̃‖ ≤ 3`), the formal identity inverse `I⁻¹`
(`‖I⁻¹‖ ≤ √k`, §A), and a non-linear Hahn–Banach extension (`‖h‖ ≤ 1`); its Lipschitz constant is the product of
these, `≤ 3√k` (Johnson–Lindenstrauss, Theorem 1). -/
theorem extension_constant_le (Lg LI Lh k : ℝ) (hLI0 : 0 ≤ LI) (hLh0 : 0 ≤ Lh)
    (hg : Lg ≤ 3) (hI : LI ≤ Real.sqrt k) (hh : Lh ≤ 1) :
    Lg * LI * Lh ≤ 3 * Real.sqrt k := by
  have h1 : Lg * LI ≤ 3 * Real.sqrt k := mul_le_mul hg hI hLI0 (by norm_num)
  calc Lg * LI * Lh ≤ (3 * Real.sqrt k) * 1 := mul_le_mul h1 hh hLh0 (by positivity)
    _ = 3 * Real.sqrt k := by ring

/-- **[The extension constant is `3K√(log n)`] `3√k ≤ 3K√(log n)` for `k ≤ K log n`, `K ≥ 1`.** With the reduced
dimension `k = ⌈K log n⌉ ≤ K log n` (`jlTargetDim`), the `3√k` extension constant becomes `3K√(log n)`: this is the
`L(X, n) ≤ C√(log n)` upper bound of Theorem 1 — every metric space's Lipschitz extension constant into a Hilbert
space grows at most like `√(log n)`. -/
theorem extension_constant_sqrt_log (K logn k : ℝ) (hk : k ≤ K * logn)
    (hK : 1 ≤ K) : 3 * Real.sqrt k ≤ 3 * K * Real.sqrt logn := by
  have h1 : Real.sqrt k ≤ Real.sqrt (K * logn) := Real.sqrt_le_sqrt hk
  have h2 : Real.sqrt (K * logn) = Real.sqrt K * Real.sqrt logn :=
    Real.sqrt_mul (by linarith) logn
  have h3 : Real.sqrt K ≤ K := by
    have hle : Real.sqrt K ≤ Real.sqrt (K ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at hle
  have h4 : Real.sqrt K * Real.sqrt logn ≤ K * Real.sqrt logn :=
    mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg logn)
  calc 3 * Real.sqrt k ≤ 3 * Real.sqrt (K * logn) := by linarith
    _ = 3 * (Real.sqrt K * Real.sqrt logn) := by rw [h2]
    _ ≤ 3 * (K * Real.sqrt logn) := by linarith
    _ = 3 * K * Real.sqrt logn := by ring

/-! ## §C — Theorem 2 / Benyamini: the `D/ε` extension constant -/

/-- **[The `ε`-separated embedding `b ↦ δ_b` is `2/ε`-Lipschitz] `2/d ≤ 2/ε` for `ε ≤ d`.** Distinct unit vectors
`δ_b, δ_{b'}` are `2` apart in `ℓ₁`, and in an `ε`-separated set the points are `≥ ε` apart, so the Lipschitz ratio
`2/d ≤ 2/ε` (Johnson–Lindenstrauss, Theorem 2: `‖F‖ ≤ 2/ε`). -/
theorem separated_map_lipschitz_le (ε d : ℝ) (hε : 0 < ε) (hd : ε ≤ d) :
    (2 : ℝ) / d ≤ 2 / ε := by
  have h := one_div_le_one_div_of_le hε hd
  calc (2 : ℝ) / d = 2 * (1 / d) := by ring
    _ ≤ 2 * (1 / ε) := by linarith
    _ = 2 / ε := by ring

/-- **[The Grothendieck factorization constant] `3 · D · (2/ε) = 6D/ε`.** The extension `f̃ = H E` composes the
`D`-bounded `G : ℓ₁ → ℓ₂`, its Grothendieck factorization through `ℓ∞` of constant `3`, and the `2/ε`-Lipschitz
separation embedding — the extension constant `6D/ε` of Theorem 2. -/
theorem theorem2_extension_constant (D ε : ℝ) : 3 * D * (2 / ε) = 6 * D / ε := by ring

/-- **[The Benyamini retraction constant] `2 · D · (2/ε) = 4D/ε`.** Benyamini's appendix replaces Grothendieck's
factorization (constant `3`) with a Lipschitz retraction of `ℓ∞(Γ)` (constant `2`, `positivePart_nonexpansive`),
sharpening the extension constant to `4D/ε` and generalizing Theorem 2 from `ℓ₂` to any Banach target. -/
theorem benyamini_extension_constant (D ε : ℝ) : 2 * D * (2 / ε) = 4 * D / ε := by ring

/-- **[The Theorem 2 extension is `6D/ε`-Lipschitz] `‖H‖ · ‖E‖ ≤ 6D/ε`.** Composing the factorization bound
`‖H‖ ≤ 3D` and the separation bound `‖E‖ ≤ 2/ε` gives the full Lipschitz extension constant `6D/ε` — every
Lipschitz `f` on an `ε`-separated `A` of diameter `D` extends to `X → ℓ₂` with `‖f̃‖ ≤ (6D/ε)‖f‖`. -/
theorem theorem2_composite (D ε LH LE : ℝ) (hD : 0 ≤ D) (hLE0 : 0 ≤ LE)
    (hH : LH ≤ 3 * D) (hE : LE ≤ 2 / ε) : LH * LE ≤ 6 * D / ε := by
  have h3D : 0 ≤ 3 * D := by linarith
  calc LH * LE ≤ (3 * D) * (2 / ε) := mul_le_mul hH hE hLE0 h3D
    _ = 6 * D / ε := by ring

/-! ## §D — the Benyamini retraction Lipschitz cores -/

/-- **[The positive part is non-expansive] `|x⁺ − y⁺| ≤ |x − y|`.** The positive-part map `x ↦ max x 0` is
`1`-Lipschitz — the Lipschitz core of Benyamini's contractive retraction of `ℓ∞(Γ)` onto its positive cone (`‖G‖ ≤ 2`,
Lemma 6(i)). -/
theorem positivePart_nonexpansive (x y : ℝ) : |max x 0 - max y 0| ≤ |x - y| :=
  abs_max_sub_max_le_abs x y 0

/-- **[The Benyamini gauge map `(2·−1)⁺` is `2`-Lipschitz] `|(2a−1)⁺ − (2b−1)⁺| ≤ 2|a − b|`.** The map
`H y (γ) = (2 y(γ) − 1)⁺` sending `ℓ∞(Γ)` into the cone (Lemma 6(ii), `‖H‖ ≤ 4`) is `2`-Lipschitz: the non-expansive
positive part precomposed with the affine `2·−1`. It sends the unit-vector `e_γ` to `e_γ` (`(2·1−1)⁺ = 1`,
`(2·0−1)⁺ = 0`), the retraction property behind the general (Benyamini) Theorem 2. -/
theorem benyamini_positivePart_two_lipschitz (a b : ℝ) :
    |max (2 * a - 1) 0 - max (2 * b - 1) 0| ≤ 2 * |a - b| := by
  calc |max (2 * a - 1) 0 - max (2 * b - 1) 0|
      ≤ |(2 * a - 1) - (2 * b - 1)| := abs_max_sub_max_le_abs _ _ _
    _ = 2 * |a - b| := by
        rw [show (2 * a - 1) - (2 * b - 1) = 2 * (a - b) by ring, abs_mul]
        norm_num

/-! ## §E — Lemma 2: the positively homogeneous extension `f̃(y) = ‖y‖ f(y/‖y‖)` -/

section HomogeneousExtension

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The **positively homogeneous extension** `f̃(y) = ‖y‖ • f(‖y‖⁻¹ • y)` of a map `f` defined on the unit sphere of
`Y` (Johnson–Lindenstrauss, Lemma 2). It agrees with `f` on the sphere and extends it to all of `Y` by radial
scaling; at `0` it is `0` (since `‖0‖ = 0`). -/
noncomputable def homogExtend (f : Y → Z) (y : Y) : Z := ‖y‖ • f (‖y‖⁻¹ • y)

/-- **[The radial-scaling difference is `2`-controlled] `‖(‖y₂‖/‖y₁‖) • y₁ − y₂‖ ≤ 2‖y₁ − y₂‖`.** For
`0 < ‖y₁‖ ≤ ‖y₂‖`, rescaling `y₁` to the length of `y₂` moves it by at most twice `‖y₁ − y₂‖`, via the
decomposition `(‖y₂‖/‖y₁‖) • y₁ − y₂ = ((‖y₂‖−‖y₁‖)/‖y₁‖) • y₁ + (y₁ − y₂)` and the reverse triangle inequality
`‖y₂‖ − ‖y₁‖ ≤ ‖y₁ − y₂‖`. This is the geometric core of Lemma 2. -/
theorem norm_scaled_sub_le {y₁ y₂ : Y} (h₁ : 0 < ‖y₁‖) (h₁₂ : ‖y₁‖ ≤ ‖y₂‖) :
    ‖(‖y₂‖ / ‖y₁‖) • y₁ - y₂‖ ≤ 2 * ‖y₁ - y₂‖ := by
  have ha0 : ‖y₁‖ ≠ 0 := ne_of_gt h₁
  have hnn : 0 ≤ (‖y₂‖ - ‖y₁‖) / ‖y₁‖ := div_nonneg (by linarith) (le_of_lt h₁)
  have hba : ‖y₂‖ - ‖y₁‖ ≤ ‖y₁ - y₂‖ := by
    have h := norm_sub_norm_le y₂ y₁
    rwa [norm_sub_rev] at h
  have hcancel : (‖y₂‖ - ‖y₁‖) / ‖y₁‖ * ‖y₁‖ = ‖y₂‖ - ‖y₁‖ := by field_simp
  have hdecomp : (‖y₂‖ / ‖y₁‖) • y₁ - y₂
      = ((‖y₂‖ - ‖y₁‖) / ‖y₁‖) • y₁ + (y₁ - y₂) := by
    have hscal : (‖y₂‖ - ‖y₁‖) / ‖y₁‖ + 1 = ‖y₂‖ / ‖y₁‖ := by field_simp; ring
    have hstep : (‖y₂‖ / ‖y₁‖) • y₁ = ((‖y₂‖ - ‖y₁‖) / ‖y₁‖) • y₁ + y₁ := by
      rw [← hscal, add_smul, one_smul]
    rw [hstep]; abel
  rw [hdecomp]
  calc ‖((‖y₂‖ - ‖y₁‖) / ‖y₁‖) • y₁ + (y₁ - y₂)‖
      ≤ ‖((‖y₂‖ - ‖y₁‖) / ‖y₁‖) • y₁‖ + ‖y₁ - y₂‖ := norm_add_le _ _
    _ = (‖y₂‖ - ‖y₁‖) + ‖y₁ - y₂‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, hcancel]
    _ ≤ 2 * ‖y₁ - y₂‖ := by linarith

/-- **[Lemma 2 — the positively homogeneous extension is Lipschitz] `‖f̃‖_Lip ≤ ‖f‖_∞ + 2‖f‖_Lip`.** If `f` on the
unit sphere is `L`-Lipschitz (`hLip`) and bounded by `M` (`hSup`), its positively homogeneous extension `f̃`
satisfies, for `0 < ‖y₁‖ ≤ ‖y₂‖`, `‖f̃ y₁ − f̃ y₂‖ ≤ (M + 2L)‖y₁ − y₂‖` (Johnson–Lindenstrauss, Lemma 2). This is
the radial smoothing used to pass a sphere map through to all of `Y` (feeding Theorems 1 and 3); proved here as an
exact normed-space inequality via the length decomposition `a•f u₁ − b•f u₂ = (a−b)•f u₁ + b•(f u₁ − f u₂)` and
`norm_scaled_sub_le`. -/
theorem homogExtend_lipschitz_bound (f : Y → Z) (L M : ℝ)
    (hLip : ∀ u v : Y, ‖u‖ = 1 → ‖v‖ = 1 → ‖f u - f v‖ ≤ L * ‖u - v‖)
    (hSup : ∀ u : Y, ‖u‖ = 1 → ‖f u‖ ≤ M)
    {y₁ y₂ : Y} (h₁ : 0 < ‖y₁‖) (h₁₂ : ‖y₁‖ ≤ ‖y₂‖) (hL : 0 ≤ L) :
    ‖homogExtend f y₁ - homogExtend f y₂‖ ≤ (M + 2 * L) * ‖y₁ - y₂‖ := by
  have hb : 0 < ‖y₂‖ := lt_of_lt_of_le h₁ h₁₂
  have ha0 : ‖y₁‖ ≠ 0 := ne_of_gt h₁
  have hb0 : ‖y₂‖ ≠ 0 := ne_of_gt hb
  have hnu₁ : ‖‖y₁‖⁻¹ • y₁‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h₁, inv_mul_cancel₀ ha0]
  have hnu₂ : ‖‖y₂‖⁻¹ • y₂‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb, inv_mul_cancel₀ hb0]
  have hxe : homogExtend f y₁ - homogExtend f y₂
      = (‖y₁‖ - ‖y₂‖) • f (‖y₁‖⁻¹ • y₁)
        + ‖y₂‖ • (f (‖y₁‖⁻¹ • y₁) - f (‖y₂‖⁻¹ • y₂)) := by
    unfold homogExtend
    rw [sub_smul, smul_sub]; abel
  have hscale : ‖y₂‖ • ((‖y₁‖⁻¹ • y₁) - (‖y₂‖⁻¹ • y₂)) = (‖y₂‖ / ‖y₁‖) • y₁ - y₂ := by
    rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hb0, one_smul, ← div_eq_mul_inv]
  have hbound1 : ‖(‖y₁‖ - ‖y₂‖) • f (‖y₁‖⁻¹ • y₁)‖ ≤ ‖y₁ - y₂‖ * M := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_norm_sub_norm_le y₁ y₂) (hSup _ hnu₁) (norm_nonneg _) (norm_nonneg _)
  have hbound2 : ‖‖y₂‖ • (f (‖y₁‖⁻¹ • y₁) - f (‖y₂‖⁻¹ • y₂))‖ ≤ 2 * L * ‖y₁ - y₂‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    have hkey : ‖y₂‖ * ‖(‖y₁‖⁻¹ • y₁) - (‖y₂‖⁻¹ • y₂)‖ = ‖(‖y₂‖ / ‖y₁‖) • y₁ - y₂‖ := by
      rw [← hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    calc ‖y₂‖ * ‖f (‖y₁‖⁻¹ • y₁) - f (‖y₂‖⁻¹ • y₂)‖
        ≤ ‖y₂‖ * (L * ‖(‖y₁‖⁻¹ • y₁) - (‖y₂‖⁻¹ • y₂)‖) :=
          mul_le_mul_of_nonneg_left (hLip _ _ hnu₁ hnu₂) (le_of_lt hb)
      _ = L * (‖y₂‖ * ‖(‖y₁‖⁻¹ • y₁) - (‖y₂‖⁻¹ • y₂)‖) := by ring
      _ = L * ‖(‖y₂‖ / ‖y₁‖) • y₁ - y₂‖ := by rw [hkey]
      _ ≤ L * (2 * ‖y₁ - y₂‖) := mul_le_mul_of_nonneg_left (norm_scaled_sub_le h₁ h₁₂) hL
      _ = 2 * L * ‖y₁ - y₂‖ := by ring
  rw [hxe]
  calc ‖(‖y₁‖ - ‖y₂‖) • f (‖y₁‖⁻¹ • y₁) + ‖y₂‖ • (f (‖y₁‖⁻¹ • y₁) - f (‖y₂‖⁻¹ • y₂))‖
      ≤ ‖(‖y₁‖ - ‖y₂‖) • f (‖y₁‖⁻¹ • y₁)‖
        + ‖‖y₂‖ • (f (‖y₁‖⁻¹ • y₁) - f (‖y₂‖⁻¹ • y₂))‖ := norm_add_le _ _
    _ ≤ ‖y₁ - y₂‖ * M + 2 * L * ‖y₁ - y₂‖ := by linarith [hbound1, hbound2]
    _ = (M + 2 * L) * ‖y₁ - y₂‖ := by ring

end HomogeneousExtension

/-! ## §F — the non-linear Hahn–Banach (McShane) extension -/

section NonlinearHahnBanach

open scoped NNReal lp ENNReal

variable {α : Type*} [PseudoMetricSpace α]

/-- **[Non-linear Hahn–Banach extension into `ℓ∞ᵏ`, constant preserved] `∃ H, LipschitzWith K H ∧ H|_s = h`.** A
`K`-Lipschitz map `h : s → ℓ∞ᵏ` (`ℓ∞ᵏ = Fin k → ℝ` with the sup metric) extends to a `K`-Lipschitz map on the whole
space, agreeing with `h` on `s` — with the **same** Lipschitz constant `K` (no blow-up). This is the paper's
non-linear Hahn–Banach step (Johnson–Lindenstrauss, Theorem 1: `‖h̃‖_Lip ≤ ‖f‖_Lip`), and it is exactly why the
only cost in Theorem 1 is the formal-identity `√k` factor (§A) and not the extension. Sourced from Mathlib's
McShane extension `LipschitzOnWith.extend_pi` (the coordinatewise `inf` construction Mathlib itself labels the
non-linear Hahn–Banach theorem). -/
theorem hahnBanach_extend_linfty {k : ℕ} {s : Set α} {h : α → (Fin k → ℝ)} {K : ℝ≥0}
    (hh : LipschitzOnWith K h s) :
    ∃ H : α → (Fin k → ℝ), LipschitzWith K H ∧ Set.EqOn h H s :=
  hh.extend_pi

/-- **[Non-linear Hahn–Banach extension into a finite-dimensional target] `∃ H, LipschitzWith (C·K) H ∧ H|_s = h`.**
A `K`-Lipschitz map into any finite-dimensional real normed space `E'` extends to the whole space, agreeing on `s`,
with constant `lipschitzExtensionConstant E' · K`. The general (basis-dependent) form of the non-linear
Hahn–Banach extension the paper invokes across Theorems 1–3; the `ℓ∞ᵏ` special case (`hahnBanach_extend_linfty`)
keeps the constant. Sourced from Mathlib's `LipschitzOnWith.extend_finite_dimension`. -/
theorem hahnBanach_extend_finiteDim {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {s : Set α} {h : α → E'} {K : ℝ≥0} (hh : LipschitzOnWith K h s) :
    ∃ H : α → E', LipschitzWith (lipschitzExtensionConstant E' * K) H ∧ Set.EqOn h H s :=
  hh.extend_finite_dimension

/-- **[Non-linear Hahn–Banach extension into `ℓ∞(Γ)`, constant preserved] `∃ H, LipschitzWith K H ∧ H|_s = h`.** The
same constant-preserving extension for the sup-normed space `ℓ^∞(ι, ℝ)` over an arbitrary (possibly infinite) index
`ι` — the step Theorem 2 and Benyamini's appendix use to extend into `ℓ∞(ℵ)` / `ℓ∞(Γ)`. Sourced from Mathlib's
`LipschitzOnWith.extend_lp_infty`. -/
theorem hahnBanach_extend_lInfty {ι : Type*} {s : Set α} {h : α → ℓ^∞(ι, ℝ)} {K : ℝ≥0}
    (hh : LipschitzOnWith K h s) :
    ∃ H : α → ℓ^∞(ι, ℝ), LipschitzWith K H ∧ Set.EqOn h H s :=
  hh.extend_lp_infty

end NonlinearHahnBanach

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussLipschitzExtension

end
