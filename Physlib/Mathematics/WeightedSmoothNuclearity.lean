/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Weight conditions for the nuclearity of weighted smooth-function spaces

Formalizes the algebraic core of K. Kruse, *On the nuclearity of weighted spaces of smooth
functions* (arXiv:1809.06457v4): the sufficient conditions `(ω.1)–(ω.3)` on a family of
weights `ν_n` under which the weighted space `𝓔𝓥(Ω)` of smooth functions is nuclear
(Theorem 3.1 there) — the property that makes the **Schwartz kernel theorem** hold, so that
multilinear functionals on test-function products extend to distributions on the product
space.  This is the analytic backbone the Osterwalder–Schrader product tensors need: the
Schwinger `n`-point functionals live on `𝓢(ℝ)⊗⋯⊗𝓢(ℝ)` and extend to kernels in
`𝓢'(ℝⁿ)` precisely because the Schwartz weights satisfy these conditions and their
products satisfy them on the product space.

* `BallComparable` — **condition (ω.1)** in pointwise-pair form: on the `r(x)`-ball the
  weight at level `n` is dominated by `A₁` times the higher-level weight anywhere on the
  same ball (`sup ≤ A₁·inf` read as a two-point inequality).
* `RadiusDominated` — **condition (ω.3)**: `ν_n ≤ A₃·r_k·ν_{I₃(n)}`.
* `BallComparable.mul`, `RadiusDominated.mul` — **Remark 2.3 a)**: the conditions are
  closed under multiplication of weight families, with the minimum radius and the product
  constants.
* `BallComparable.prod`, `RadiusDominated.prod` — the same closure for the **tensor-product
  weight** `(x,y) ↦ ν(x)·μ(y)` on the product space with its sup norm — the mechanism by
  which nuclearity passes to products of test-function spaces, i.e. the kernel extension of
  OS product tensors.
* `radiusDominated_of_le_radius` — **Remark 2.3 b)**: a radius bounded below by `c > 0`
  fulfils (ω.3) with `A₃ = c⁻¹` at the same level.
* `radius_lower_bound` — **Remark 2.4**, pointwise: (ω.3) forces
  `r(x) ≥ ν_n(x)/(A₃·ν_{I₃}(x))`, so the radii are bounded away from zero wherever the
  weights are.
* `one_add_sq_norm_le`, `schwartzWeight_ballComparable` — **Example 2.8 (iv)**, the
  classical Schwartz family `ν_n(x) = (1+‖x‖²)ⁿ`: the exact comparison
  `1+‖x‖² ≤ (1+‖y‖²)(1+‖x−y‖)²` gives (ω.1) with the same level, constant radius `δ`, and
  constant `(1+2δ)^{2n}` — the verification that the classical Schwartz space falls under
  the nuclearity conditions.
* `schwartzWeight_ratio_integrable` — the Gelfand–Vilenkin integrability `(N.2)`: on `ℝ`
  the ratio `ν_n/ν_{n+1} = (1+x²)⁻¹` is integrable (the arctan integral), the second
  classical route to the nuclearity of `𝓢(ℝ)`.

**Honest layering.**  Exact pointwise inequalities and one Bochner integrability; the
locally convex machinery — partitions of unity (Lemma 2.11 there), the nuclearity Theorem
3.1 itself, and the kernel theorem it yields — is the analytic layer, recorded not
re-derived.  The Bolzano–Weierstraß cases (ii)/(iii) of Proposition 2.6 are likewise
recorded.

## References

* K. Kruse, *On the nuclearity of weighted spaces of smooth functions*,
  arXiv:1809.06457v4; I. M. Gelfand, N. Ya. Vilenkin, *Generalized Functions IV*, Ch. I
  §3.6.  Serves the OS arc: the Schwinger functionals on product tensors of
  `QFT.HamiltonianRenormalisation.FreeFieldMeasureReconstruction` and the paper-I
  reconstruction extend to kernels by this nuclearity.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Mathematics.WeightedSmoothNuclearity

variable {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

/-- **Condition (ω.1)** in pointwise-pair form: anywhere on the `r(x)`-ball around `x`, the
weight is dominated by `A` times the comparison weight anywhere on the same ball —
`sup_{‖ζ‖≤r} ν(x+ζ) ≤ A·inf_{‖η‖≤r} ν'(x+η)` read without suprema. -/
def BallComparable (ν νI : X → ℝ) (r : X → ℝ) (A : ℝ) : Prop :=
  ∀ x ζ η, ‖ζ‖ ≤ r x → ‖η‖ ≤ r x → ν (x + ζ) ≤ A * νI (x + η)

/-- **Condition (ω.3)**: the weight is dominated by `A` times the radius times the
higher-level weight, `ν ≤ A·r·ν'`. -/
def RadiusDominated (ν νI : X → ℝ) (r : X → ℝ) (A : ℝ) : Prop :=
  ∀ x, ν x ≤ A * r x * νI x

/-- **Remark 2.3 a) for (ω.1)**: ball comparability is closed under multiplication of
weight families, with the minimum radius and the product of the constants. -/
theorem BallComparable.mul {ν νI μ μI : X → ℝ} {r s : X → ℝ} {A B : ℝ}
    (hν : BallComparable ν νI r A) (hμ : BallComparable μ μI s B)
    (hν0 : ∀ x, 0 ≤ ν x) (hμ0 : ∀ x, 0 ≤ μ x) :
    BallComparable (fun x => ν x * μ x) (fun x => νI x * μI x)
      (fun x => min (r x) (s x)) (A * B) := by
  intro x ζ η hζ hη
  have h1 := hν x ζ η (hζ.trans (min_le_left _ _)) (hη.trans (min_le_left _ _))
  have h2 := hμ x ζ η (hζ.trans (min_le_right _ _)) (hη.trans (min_le_right _ _))
  calc ν (x + ζ) * μ (x + ζ)
      ≤ (A * νI (x + η)) * (B * μI (x + η)) :=
        mul_le_mul h1 h2 (hμ0 _) ((hν0 _).trans h1)
    _ = A * B * (νI (x + η) * μI (x + η)) := by ring

omit [SeminormedAddCommGroup X] in
/-- **Remark 2.3 a) for (ω.3)**: with radii in `[0,1]` (the paper's range `(0,1]`), radius
domination is closed under multiplication of weight families, with the minimum radius. -/
theorem RadiusDominated.mul {ν νI μ μI : X → ℝ} {r s : X → ℝ} {A B : ℝ}
    (hν : RadiusDominated ν νI r A) (hμ : RadiusDominated μ μI s B)
    (hμ0 : ∀ x, 0 ≤ μ x)
    (hνI0 : ∀ x, 0 ≤ νI x) (hμI0 : ∀ x, 0 ≤ μI x)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr0 : ∀ x, 0 ≤ r x) (hr1 : ∀ x, r x ≤ 1)
    (hs0 : ∀ x, 0 ≤ s x) (hs1 : ∀ x, s x ≤ 1) :
    RadiusDominated (fun x => ν x * μ x) (fun x => νI x * μI x)
      (fun x => min (r x) (s x)) (A * B) := by
  intro x
  have h1 := hν x
  have h2 := hμ x
  have hrs : r x * s x ≤ min (r x) (s x) := by
    rcases le_total (r x) (s x) with h | h
    · rw [min_eq_left h]
      calc r x * s x ≤ r x * 1 := mul_le_mul_of_nonneg_left (hs1 x) (hr0 x)
        _ = r x := mul_one _
    · rw [min_eq_right h]
      calc r x * s x ≤ 1 * s x := mul_le_mul_of_nonneg_right (hr1 x) (hs0 x)
        _ = s x := one_mul _
  have hR0 : 0 ≤ A * r x * νI x := mul_nonneg (mul_nonneg hA (hr0 x)) (hνI0 x)
  calc ν x * μ x
      ≤ (A * r x * νI x) * (B * s x * μI x) := mul_le_mul h1 h2 (hμ0 x) hR0
    _ = (r x * s x) * (A * B * (νI x * μI x)) := by ring
    _ ≤ min (r x) (s x) * (A * B * (νI x * μI x)) :=
        mul_le_mul_of_nonneg_right hrs
          (mul_nonneg (mul_nonneg hA hB) (mul_nonneg (hνI0 x) (hμI0 x)))
    _ = A * B * min (r x) (s x) * (νI x * μI x) := by ring

/-- **The tensor-product weight on the product space fulfils (ω.1)** — the kernel-extension
mechanism: if two weight families are ball comparable on `X` and `Y`, the product weight
`(x,y) ↦ ν(x)·μ(y)` is ball comparable on `X × Y` (sup norm) with the minimum radius —
nuclearity conditions pass to products of test-function spaces, so multilinear functionals
on OS product tensors extend to kernels on the product space. -/
theorem BallComparable.prod {ν νI : X → ℝ} {μ μI : Y → ℝ} {r : X → ℝ} {s : Y → ℝ}
    {A B : ℝ} (hν : BallComparable ν νI r A) (hμ : BallComparable μ μI s B)
    (hν0 : ∀ x, 0 ≤ ν x) (hμ0 : ∀ y, 0 ≤ μ y) :
    BallComparable (fun p : X × Y => ν p.1 * μ p.2) (fun p => νI p.1 * μI p.2)
      (fun p => min (r p.1) (s p.2)) (A * B) := by
  intro p ζ η hζ hη
  show ν (p.1 + ζ.1) * μ (p.2 + ζ.2) ≤ A * B * (νI (p.1 + η.1) * μI (p.2 + η.2))
  have hζ1 : ‖ζ.1‖ ≤ r p.1 := (norm_fst_le ζ).trans (hζ.trans (min_le_left _ _))
  have hζ2 : ‖ζ.2‖ ≤ s p.2 := (norm_snd_le ζ).trans (hζ.trans (min_le_right _ _))
  have hη1 : ‖η.1‖ ≤ r p.1 := (norm_fst_le η).trans (hη.trans (min_le_left _ _))
  have hη2 : ‖η.2‖ ≤ s p.2 := (norm_snd_le η).trans (hη.trans (min_le_right _ _))
  have h1 := hν p.1 ζ.1 η.1 hζ1 hη1
  have h2 := hμ p.2 ζ.2 η.2 hζ2 hη2
  calc ν (p.1 + ζ.1) * μ (p.2 + ζ.2)
      ≤ (A * νI (p.1 + η.1)) * (B * μI (p.2 + η.2)) :=
        mul_le_mul h1 h2 (hμ0 _) ((hν0 _).trans h1)
    _ = A * B * (νI (p.1 + η.1) * μI (p.2 + η.2)) := by ring

omit [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y] in
/-- **The tensor-product weight fulfils (ω.3)** on the product space, with radii in
`[0,1]` — the (ω.3) half of the kernel-extension mechanism. -/
theorem RadiusDominated.prod {ν νI : X → ℝ} {μ μI : Y → ℝ} {r : X → ℝ} {s : Y → ℝ}
    {A B : ℝ} (hν : RadiusDominated ν νI r A) (hμ : RadiusDominated μ μI s B)
    (hμ0 : ∀ y, 0 ≤ μ y)
    (hνI0 : ∀ x, 0 ≤ νI x) (hμI0 : ∀ y, 0 ≤ μI y)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr0 : ∀ x, 0 ≤ r x) (hr1 : ∀ x, r x ≤ 1)
    (hs0 : ∀ y, 0 ≤ s y) (hs1 : ∀ y, s y ≤ 1) :
    RadiusDominated (fun p : X × Y => ν p.1 * μ p.2) (fun p => νI p.1 * μI p.2)
      (fun p => min (r p.1) (s p.2)) (A * B) := by
  intro p
  have h1 := hν p.1
  have h2 := hμ p.2
  have hrs : r p.1 * s p.2 ≤ min (r p.1) (s p.2) := by
    rcases le_total (r p.1) (s p.2) with h | h
    · rw [min_eq_left h]
      calc r p.1 * s p.2 ≤ r p.1 * 1 := mul_le_mul_of_nonneg_left (hs1 p.2) (hr0 p.1)
        _ = r p.1 := mul_one _
    · rw [min_eq_right h]
      calc r p.1 * s p.2 ≤ 1 * s p.2 := mul_le_mul_of_nonneg_right (hr1 p.1) (hs0 p.2)
        _ = s p.2 := one_mul _
  have hR0 : 0 ≤ A * r p.1 * νI p.1 := mul_nonneg (mul_nonneg hA (hr0 p.1)) (hνI0 p.1)
  calc ν p.1 * μ p.2
      ≤ (A * r p.1 * νI p.1) * (B * s p.2 * μI p.2) := mul_le_mul h1 h2 (hμ0 p.2) hR0
    _ = (r p.1 * s p.2) * (A * B * (νI p.1 * μI p.2)) := by ring
    _ ≤ min (r p.1) (s p.2) * (A * B * (νI p.1 * μI p.2)) :=
        mul_le_mul_of_nonneg_right hrs
          (mul_nonneg (mul_nonneg hA hB) (mul_nonneg (hνI0 p.1) (hμI0 p.2)))
    _ = A * B * min (r p.1) (s p.2) * (νI p.1 * μI p.2) := by ring

omit [SeminormedAddCommGroup X] in
/-- **Remark 2.3 b)**: a radius bounded below by `c > 0` fulfils (ω.3) at the same level
with constant `c⁻¹`: `ν = c⁻¹·c·ν ≤ c⁻¹·r·ν`. -/
theorem radiusDominated_of_le_radius {ν : X → ℝ} {r : X → ℝ} {c : ℝ} (hc : 0 < c)
    (hcr : ∀ x, c ≤ r x) (hν0 : ∀ x, 0 ≤ ν x) :
    RadiusDominated ν ν r c⁻¹ := by
  intro x
  have h1 : 1 ≤ c⁻¹ * r x := by
    calc (1:ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ c⁻¹ * r x := mul_le_mul_of_nonneg_left (hcr x) (by positivity)
  calc ν x = 1 * ν x := (one_mul _).symm
    _ ≤ (c⁻¹ * r x) * ν x := mul_le_mul_of_nonneg_right h1 (hν0 x)

omit [SeminormedAddCommGroup X] in
/-- **Remark 2.4**, pointwise: condition (ω.3) forces the radius to be bounded below by the
weight ratio, `ν(x)/(A·ν'(x)) ≤ r(x)` — wherever the weights are positive the radii cannot
degenerate. -/
theorem radius_lower_bound {ν νI : X → ℝ} {r : X → ℝ} {A : ℝ}
    (h : RadiusDominated ν νI r A) (x : X) (hA : 0 < A) (hνI : 0 < νI x) :
    ν x / (A * νI x) ≤ r x := by
  have hx := h x
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ## The classical Schwartz family (Example 2.8 (iv)) -/

/-- **The exact ball comparison of the Schwartz weight**:
`1+‖x‖² ≤ (1+‖y‖²)·(1+‖x−y‖)²` — the elementary inequality from which the whole
(ω.1)-verification of the classical Schwartz family follows. -/
theorem one_add_sq_norm_le (x y : X) :
    1 + ‖x‖^2 ≤ (1 + ‖y‖^2) * (1 + ‖x - y‖)^2 := by
  have h : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    simpa using norm_add_le y (x - y)
  have h2 : ‖x‖^2 ≤ (‖y‖ + ‖x - y‖)^2 := by
    nlinarith [norm_nonneg x]
  nlinarith [norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖y‖ - 1),
    sq_nonneg (‖y‖ * ‖x - y‖)]

/-- **The classical Schwartz weights fulfil (ω.1)** (Example 2.8 (iv)): the family
`ν_n(x) = (1+‖x‖²)ⁿ` is ball comparable at the same level with any constant radius `δ` and
constant `A₁ = (1+2δ)^{2n}`. -/
theorem schwartzWeight_ballComparable (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    BallComparable (X := X) (fun x => (1 + ‖x‖^2)^n) (fun x => (1 + ‖x‖^2)^n)
      (fun _ => δ) ((1 + 2*δ)^(2*n)) := by
  intro x ζ η hζ hη
  have hcomp : 1 + ‖x + ζ‖^2 ≤ (1 + ‖x + η‖^2) * (1 + ‖(x + ζ) - (x + η)‖)^2 :=
    one_add_sq_norm_le (x + ζ) (x + η)
  have hd : ‖(x + ζ) - (x + η)‖ ≤ 2*δ := by
    have : (x + ζ) - (x + η) = ζ - η := by abel
    rw [this]
    calc ‖ζ - η‖ ≤ ‖ζ‖ + ‖η‖ := norm_sub_le ζ η
      _ ≤ 2*δ := by linarith
  have hstep : 1 + ‖x + ζ‖^2 ≤ (1 + ‖x + η‖^2) * (1 + 2*δ)^2 := by
    have hsq : (1 + ‖(x + ζ) - (x + η)‖)^2 ≤ (1 + 2*δ)^2 := by
      have h1 : (0:ℝ) ≤ 1 + ‖(x + ζ) - (x + η)‖ := by positivity
      nlinarith [norm_nonneg ((x + ζ) - (x + η))]
    nlinarith [sq_nonneg (1 + ‖x + η‖), norm_nonneg (x + η), hcomp,
      mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 1 + ‖x + η‖^2)]
  calc (1 + ‖x + ζ‖^2)^n
      ≤ ((1 + ‖x + η‖^2) * (1 + 2*δ)^2)^n :=
        pow_le_pow_left₀ (by positivity) hstep n
    _ = (1 + 2*δ)^(2*n) * (1 + ‖x + η‖^2)^n := by
        rw [mul_pow, ← pow_mul]
        ring

/-- **The Gelfand–Vilenkin integrability (N.2)** for the classical Schwartz family on `ℝ`:
the weight ratio `ν_n/ν_{n+1} = (1+x²)⁻¹` is integrable — the arctan integral, the second
classical route to the nuclearity of `𝓢(ℝ)`. -/
theorem schwartzWeight_ratio_integrable (n : ℕ) :
    MeasureTheory.Integrable
      (fun x : ℝ => (1 + ‖x‖^2)^n / (1 + ‖x‖^2)^(n+1)) := by
  have heq : (fun x : ℝ => (1 + ‖x‖^2)^n / (1 + ‖x‖^2)^(n+1))
      = fun x : ℝ => (1 + x^2)⁻¹ := by
    funext x
    have hpos : (0:ℝ) < 1 + x^2 := by positivity
    rw [Real.norm_eq_abs, sq_abs, pow_succ]
    field_simp
    ring
  rw [heq]
  exact integrable_inv_one_add_sq

/-- **Example 2.8 (i)/(iii) with `μ(x) = ‖x‖`**: exponential weights of the norm,
`ν(x) = e^{a‖x‖}` for either sign of `a`, are ball comparable at the same level with any
constant radius `δ` and constant `e^{2|a|δ}` — the family that covers the exponential
kernel weights of the OS reconstruction. -/
theorem expNormWeight_ballComparable (a δ : ℝ) (hδ : 0 ≤ δ) :
    BallComparable (X := X) (fun x => Real.exp (a * ‖x‖)) (fun x => Real.exp (a * ‖x‖))
      (fun _ => δ) (Real.exp (2 * |a| * δ)) := by
  intro x ζ η hζ hη
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnorm : |‖x + ζ‖ - ‖x + η‖| ≤ 2*δ := by
    have h1 := abs_norm_sub_norm_le (x + ζ) (x + η)
    have h2 : (x + ζ) - (x + η) = ζ - η := by abel
    rw [h2] at h1
    calc |‖x + ζ‖ - ‖x + η‖| ≤ ‖ζ - η‖ := h1
      _ ≤ ‖ζ‖ + ‖η‖ := norm_sub_le ζ η
      _ ≤ 2*δ := by linarith
  have key : a * ‖x + ζ‖ - a * ‖x + η‖ ≤ 2 * |a| * δ := by
    calc a * ‖x + ζ‖ - a * ‖x + η‖
        = a * (‖x + ζ‖ - ‖x + η‖) := by ring
      _ ≤ |a * (‖x + ζ‖ - ‖x + η‖)| := le_abs_self _
      _ = |a| * |‖x + ζ‖ - ‖x + η‖| := abs_mul a _
      _ ≤ |a| * (2*δ) := mul_le_mul_of_nonneg_left hnorm (abs_nonneg a)
      _ = 2 * |a| * δ := by ring
  linarith

/-- **The two-point (product-tensor) Schwartz weight is ball comparable** — the ready-made
instance for OS two-point functionals: `(1+‖x‖²)ⁿ·(1+‖y‖²)ᵐ` on the product space fulfils
(ω.1) with constant radius `δ` — the Schwartz instance composed with the product closure. -/
theorem schwartzWeight_prod_ballComparable (n m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    BallComparable (fun p : X × Y => (1 + ‖p.1‖^2)^n * (1 + ‖p.2‖^2)^m)
      (fun p => (1 + ‖p.1‖^2)^n * (1 + ‖p.2‖^2)^m)
      (fun _ => δ) ((1 + 2*δ)^(2*n) * (1 + 2*δ)^(2*m)) := by
  have h := (schwartzWeight_ballComparable (X := X) n δ hδ).prod
    (schwartzWeight_ballComparable (X := Y) m δ hδ)
    (fun x => by positivity) (fun y => by positivity)
  simpa [min_self] using h

end Physlib.Mathematics.WeightedSmoothNuclearity

end
