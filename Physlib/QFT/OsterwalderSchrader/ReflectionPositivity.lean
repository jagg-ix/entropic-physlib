/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Reflection positivity and the Osterwalder–Schrader contraction property

The abstract Hilbert-space core of the Osterwalder–Schrader reconstruction, following
Lang–Liegener–Thiemann, *Hamiltonian renormalisation I: derivation from
Osterwalder–Schrader reconstruction*, §2.2–2.3.  The input is a **reflection positive
flow**: a complex inner product space `E` (the history space `ℋ'`), a unitary involution
`reflect` (time reflection `R`, Eq. 2.20), a one-parameter unitary group `translate`
(Euclidian time translation `𝒰(s)`, Eq. 2.25) conjugated by `reflect` into the reversed
translation (Eq. 2.33), a `translate`-invariant positive-time subspace `posTime`
(the span `V` of the `W[F]` with positive time support), and **reflection positivity**
(Eq. 2.22): `0 ≤ ⟪ψ, R ψ⟫` on `posTime`.

From this input the paper's reconstruction chain is derived exactly:

* `form_conj_symm` — the reflection form `(ψ, φ) := ⟪ψ, R φ⟫` (Eq. 2.27) is Hermitian
  (Eq. 2.28), by unitarity and involutivity of `R`; its diagonal is real
  (`form_self_im`).
* `norm_form_le` — the Cauchy–Schwarz inequality for the positive semidefinite
  reflection form on `posTime`, obtained from Mathlib's `PreInnerProductSpace.Core`
  (the form is packaged as `rpCore`).
* `form_translate_left` — the translation semigroup is symmetric for the reflection
  form (Eq. 2.35), from `R 𝒰(s) = 𝒰(−s) R`.
* `rpSeminorm_translate_le_norm` — the ambient bound `q(𝒰(s)ψ) ≤ ‖ψ‖` (Eq. 2.37),
  where `q` is the seminorm of the reflection form (the norm of the class `[ψ]` in the
  Osterwalder–Schrader Hilbert space, Eq. 2.30).
* `rpSeminorm_translate_sq_le` — the halving recursion
  `q(𝒰(s)ψ)² ≤ q(ψ)·q(𝒰(2s)ψ)` (the inner step of Eq. 2.36).
* `rpSeminorm_translate_le_rpow` — the iterated Cauchy–Schwarz bound
  `q(𝒰(s)ψ) ≤ q(ψ)^(1−2⁻ⁿ)·‖ψ‖^(2⁻ⁿ)` (Eq. 2.38).
* `rpSeminorm_translate_le` — **the contraction property** `q(𝒰(s)ψ) ≤ q(ψ)`
  (Eq. 2.39): time translation is a contraction semigroup for the reflection form.
  This is the operator inequality that makes the Osterwalder–Schrader Hamiltonian
  positive.
* `form_eq_zero_of_null`, `form_add_null`, `translate_null` — the quotient data
  (Eqs. 2.29–2.31, 2.34): the reflection form is independent of null summands, and
  forward translation preserves the null space, so the class inner product
  (Eq. 2.30) and the transfer operator `K(s)[ψ] = [𝒰(s)ψ]` (Eq. 2.31) are well
  defined.
* `form_translate_self_re_nonneg` — positivity of the transfer semigroup for the
  reflection form (Eq. 2.35), by halving the time step.
* `rpSeminorm_translate_sub_sq_le`, `tendsto_rpSeminorm_translate_sub` — the
  continuity estimate `‖[K(s) − 1][ψ]‖² ≤ |⟨ψ,[𝒰(2s) − 1]Rψ⟩| + 2|⟨ψ,[𝒰(s) − 1]Rψ⟩|`
  and its consequence (Eq. 2.40): reflection continuity of `𝒰` makes the transfer
  semigroup strongly continuous on classes — the input to the Hille–Yosida theorem.
* `form_translate_eq_of_null_diff`, `null_of_clustering_fixed` — **uniqueness of the
  vacuum** (Eqs. 2.41–2.43): a class fixed by the transfer semigroup (Eq. 2.41,
  `K(s)Ω = Ω`) whose matrix elements cluster along the flow (Eq. 2.42) is the
  multiple `(1, ω)·[1]` of the vacuum class — the defect `(1, ω)•1 − ω` is null
  (Eq. 2.43), so the vacuum is unique up to a phase.

**Scope.**  This module stays at the level of the reflection form on the history
space; the seminorm and form statements proved here are exactly the corresponding
statements about the quotient classes `[ψ]`, since `‖[ψ]‖_ℋ = q(ψ)` and
`⟨[ψ],[φ]⟩ = (ψ,φ)` by definition (Eq. 2.30), and the well-definedness lemmas above
are what license the quotient.  The completion to the Osterwalder–Schrader Hilbert
space as a type, and the existence of the Hille–Yosida generator `H` from the
strong continuity proved here, are follow-up material.  The measure-theoretic
construction of the history space `ℋ' = L₂(Γ, dμ)` and the Wiener measure (§2.2,
Eq. 2.7) live in the companion module `OsterwalderSchrader.SchwingerConstruction`
at the level of the Schwinger data; the structure fields here record the properties
of `(R, 𝒰, V)` that §2.3 actually uses (see the remark on p. 14 of the paper: only
reflection invariance, reflection positivity, translation invariance and continuity
enter the reconstruction).

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation I: derivation from
  Osterwalder–Schrader reconstruction*, Class. Quantum Grav. **35** (2018) 245011,
  doi:10.1088/1361-6382/aaec56, §2.
-/

set_option autoImplicit false

open Complex Filter
open scoped ComplexInnerProductSpace Topology

@[expose] public section

namespace Physlib.QFT.OsterwalderSchrader

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Reflection positive flow** (Lang–Liegener–Thiemann §2.2–2.3): a history inner
product space together with a unitary time reflection `R` (Eq. 2.20), a one-parameter
unitary time-translation group `𝒰(s)` (Eq. 2.25) satisfying `R 𝒰(s) = 𝒰(−s) R`
(Eq. 2.33), a positive-time subspace `V` invariant under forward translation, and the
reflection positivity condition `0 ≤ ⟪ψ, R ψ⟫` on `V` (Eq. 2.22). -/
structure ReflectionPositiveFlow (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] where
  /-- Time reflection `R` (Eq. 2.20), a unitary map. -/
  reflect : E ≃ₗᵢ[ℂ] E
  /-- `R² = 1` (used in Eq. 2.21 and for Hermiticity of the reflection form). -/
  reflect_reflect : ∀ ψ : E, reflect (reflect ψ) = ψ
  /-- Euclidian time translation `𝒰(s)` (Eq. 2.25), a unitary map for each `s`. -/
  translate : ℝ → E ≃ₗᵢ[ℂ] E
  /-- `𝒰(0) = 1`. -/
  translate_zero : ∀ ψ : E, translate 0 ψ = ψ
  /-- The one-parameter group law `𝒰(s+t) = 𝒰(s)𝒰(t)`. -/
  translate_add : ∀ s t : ℝ, ∀ ψ : E, translate (s + t) ψ = translate s (translate t ψ)
  /-- Time reflection conjugates translation into the reversed translation,
  `R 𝒰(s) = 𝒰(−s) R` (Eqs. 2.32–2.33). -/
  reflect_translate : ∀ s : ℝ, ∀ ψ : E, reflect (translate s ψ) = translate (-s) (reflect ψ)
  /-- The positive-time subspace `V` (below Eq. 2.21). -/
  posTime : Submodule ℂ E
  /-- Forward translation preserves the positive-time subspace. -/
  translate_posTime : ∀ s : ℝ, 0 ≤ s → ∀ ψ ∈ posTime, translate s ψ ∈ posTime
  /-- **Reflection positivity** (Eq. 2.22): `0 ≤ ⟪ψ, R ψ⟫` for `ψ ∈ V`. -/
  reflection_positive : ∀ ψ ∈ posTime, 0 ≤ (⟪ψ, reflect ψ⟫ : ℂ).re

namespace ReflectionPositiveFlow

variable (D : ReflectionPositiveFlow E)

/-! ## A. The reflection form and its Hermiticity -/

/-- The **reflection form** `(ψ, φ) := ⟪ψ, R φ⟫` (Eq. 2.27), the sesquilinear form
whose restriction to the positive-time subspace becomes the Osterwalder–Schrader inner
product after passing to quotient classes (Eq. 2.30). -/
def form (ψ φ : E) : ℂ := ⟪ψ, D.reflect φ⟫

/-- **Hermiticity of the reflection form** (Eq. 2.28): `conj (φ, ψ) = (ψ, φ)`, by
unitarity and involutivity of the time reflection. -/
lemma form_conj_symm (ψ φ : E) : (starRingEnd ℂ) (D.form φ ψ) = D.form ψ φ := by
  rw [form, inner_conj_symm]
  calc (⟪D.reflect ψ, φ⟫ : ℂ) = ⟪D.reflect ψ, D.reflect (D.reflect φ)⟫ := by
        rw [D.reflect_reflect]
    _ = ⟪ψ, D.reflect φ⟫ := D.reflect.inner_map_map ψ (D.reflect φ)

/-- The diagonal of the reflection form is real. -/
lemma form_self_im (ψ : E) : (D.form ψ ψ).im = 0 := by
  have h := D.form_conj_symm ψ ψ
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

lemma form_add_left (ψ ψ' φ : E) : D.form (ψ + ψ') φ = D.form ψ φ + D.form ψ' φ :=
  inner_add_left _ _ _

lemma form_smul_left (c : ℂ) (ψ φ : E) : D.form (c • ψ) φ = (starRingEnd ℂ) c * D.form ψ φ :=
  inner_smul_left _ _ _

/-! ## B. Cauchy–Schwarz for the reflection form on the positive-time subspace

Reflection positivity makes the reflection form a positive **semi**definite Hermitian
form on `V`; Mathlib's `PreInnerProductSpace.Core` is exactly this package, and its
Cauchy–Schwarz inequality transfers. -/

/-- The reflection form restricted to the positive-time subspace, packaged as a
Mathlib positive semidefinite inner product core (not an instance: `↥posTime` keeps
its ambient inner product). -/
@[reducible] noncomputable def rpCore : PreInnerProductSpace.Core ℂ ↥D.posTime where
  inner ψ φ := D.form ψ φ
  conj_inner_symm ψ φ := D.form_conj_symm ψ φ
  re_inner_nonneg ψ := D.reflection_positive ψ ψ.2
  add_left ψ ψ' φ := D.form_add_left ψ ψ' φ
  smul_left ψ φ c := D.form_smul_left c ψ φ

/-- The seminorm of the reflection form, `q(ψ) := √(ψ, ψ)` — the norm of the class
`[ψ]` in the Osterwalder–Schrader Hilbert space (Eq. 2.30). -/
noncomputable def rpSeminorm (ψ : E) : ℝ := Real.sqrt (D.form ψ ψ).re

lemma rpSeminorm_nonneg (ψ : E) : 0 ≤ D.rpSeminorm ψ := Real.sqrt_nonneg _

/-- `q(ψ)² = (ψ, ψ)` on the positive-time subspace. -/
lemma sq_rpSeminorm {ψ : E} (hψ : ψ ∈ D.posTime) :
    D.rpSeminorm ψ ^ 2 = (D.form ψ ψ).re :=
  Real.sq_sqrt (D.reflection_positive ψ hψ)

/-- **Cauchy–Schwarz for the reflection form** (used in Eqs. 2.34–2.36):
`‖(ψ, φ)‖ ≤ q(ψ)·q(φ)` on the positive-time subspace. -/
lemma norm_form_le {ψ φ : E} (hψ : ψ ∈ D.posTime) (hφ : φ ∈ D.posTime) :
    ‖D.form ψ φ‖ ≤ D.rpSeminorm ψ * D.rpSeminorm φ := by
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ ↥D.posTime _ _ _ D.rpCore
    ⟨ψ, hψ⟩ ⟨φ, hφ⟩
  have hsymm : ‖D.form φ ψ‖ = ‖D.form ψ φ‖ := by
    rw [← D.form_conj_symm ψ φ, RCLike.norm_conj]
  have h' : ‖D.form ψ φ‖ * ‖D.form ψ φ‖ ≤ (D.form ψ ψ).re * (D.form φ φ).re := by
    calc ‖D.form ψ φ‖ * ‖D.form ψ φ‖ = ‖D.form ψ φ‖ * ‖D.form φ ψ‖ := by rw [hsymm]
      _ ≤ (D.form ψ ψ).re * (D.form φ φ).re := h
  calc ‖D.form ψ φ‖ = Real.sqrt (‖D.form ψ φ‖ * ‖D.form ψ φ‖) :=
        (Real.sqrt_mul_self (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((D.form ψ ψ).re * (D.form φ φ).re) := Real.sqrt_le_sqrt h'
    _ = D.rpSeminorm ψ * D.rpSeminorm φ :=
        Real.sqrt_mul (D.reflection_positive ψ hψ) _

/-! ## C. The translation semigroup is symmetric and contractive for the form -/

/-- `𝒰(−s)` inverts `𝒰(s)`. -/
lemma translate_neg_translate (s : ℝ) (ψ : E) :
    D.translate s (D.translate (-s) ψ) = ψ := by
  rw [← D.translate_add s (-s) ψ]
  simp [D.translate_zero]

/-- **The translation semigroup is symmetric for the reflection form** (Eq. 2.35):
`(𝒰(s)ψ, φ) = (ψ, 𝒰(s)φ)`, from `R 𝒰(s) = 𝒰(−s) R`. -/
lemma form_translate_left (s : ℝ) (ψ φ : E) :
    D.form (D.translate s ψ) φ = D.form ψ (D.translate s φ) := by
  calc D.form (D.translate s ψ) φ
      = ⟪D.translate s ψ, D.translate s (D.translate (-s) (D.reflect φ))⟫ := by
        rw [form, D.translate_neg_translate]
    _ = ⟪ψ, D.translate (-s) (D.reflect φ)⟫ :=
        (D.translate s).inner_map_map ψ (D.translate (-s) (D.reflect φ))
    _ = D.form ψ (D.translate s φ) := by rw [form, ← D.reflect_translate]

/-- **The ambient bound** (Eq. 2.37): `q(𝒰(s)ψ) ≤ ‖ψ‖` for every `s`, by the ambient
Cauchy–Schwarz inequality and unitarity of `R` and `𝒰(s)`. -/
lemma rpSeminorm_translate_le_norm (ψ : E) (s : ℝ) :
    D.rpSeminorm (D.translate s ψ) ≤ ‖ψ‖ := by
  have hre : (D.form (D.translate s ψ) (D.translate s ψ)).re ≤ ‖ψ‖ * ‖ψ‖ := by
    calc (D.form (D.translate s ψ) (D.translate s ψ)).re
        ≤ ‖D.form (D.translate s ψ) (D.translate s ψ)‖ := by
          simpa [RCLike.re_to_complex] using
            RCLike.re_le_norm (D.form (D.translate s ψ) (D.translate s ψ))
      _ ≤ ‖D.translate s ψ‖ * ‖D.reflect (D.translate s ψ)‖ := norm_inner_le_norm _ _
      _ = ‖ψ‖ * ‖ψ‖ := by rw [D.reflect.norm_map, (D.translate s).norm_map]
  calc D.rpSeminorm (D.translate s ψ) ≤ Real.sqrt (‖ψ‖ * ‖ψ‖) := Real.sqrt_le_sqrt hre
    _ = ‖ψ‖ := Real.sqrt_mul_self (norm_nonneg ψ)

/-- `q(ψ) ≤ ‖ψ‖`: the reflection-form seminorm is dominated by the ambient norm. -/
lemma rpSeminorm_le_norm (ψ : E) : D.rpSeminorm ψ ≤ ‖ψ‖ := by
  have h := D.rpSeminorm_translate_le_norm ψ 0
  rwa [show D.translate 0 ψ = ψ from D.translate_zero ψ] at h

/-- **The halving recursion** (the inner step of Eq. 2.36):
`q(𝒰(s)ψ)² ≤ q(ψ)·q(𝒰(2s)ψ)`, from the semigroup symmetry and Cauchy–Schwarz. -/
lemma rpSeminorm_translate_sq_le {ψ : E} (hψ : ψ ∈ D.posTime) {s : ℝ} (hs : 0 ≤ s) :
    D.rpSeminorm (D.translate s ψ) ^ 2
      ≤ D.rpSeminorm ψ * D.rpSeminorm (D.translate (2 * s) ψ) := by
  have h2s : D.translate (2 * s) ψ ∈ D.posTime :=
    D.translate_posTime (2 * s) (by linarith) ψ hψ
  have hform : D.form (D.translate s ψ) (D.translate s ψ)
      = D.form ψ (D.translate (2 * s) ψ) := by
    rw [D.form_translate_left, ← D.translate_add, two_mul]
  calc D.rpSeminorm (D.translate s ψ) ^ 2
      = (D.form (D.translate s ψ) (D.translate s ψ)).re :=
        D.sq_rpSeminorm (D.translate_posTime s hs ψ hψ)
    _ = (D.form ψ (D.translate (2 * s) ψ)).re := by rw [hform]
    _ ≤ ‖D.form ψ (D.translate (2 * s) ψ)‖ := by
        simpa [RCLike.re_to_complex] using
          RCLike.re_le_norm (D.form ψ (D.translate (2 * s) ψ))
    _ ≤ D.rpSeminorm ψ * D.rpSeminorm (D.translate (2 * s) ψ) := D.norm_form_le hψ h2s

/-- **The iterated Cauchy–Schwarz bound** (Eq. 2.38): for `0 < q(ψ)`,
`q(𝒰(s)ψ) ≤ q(ψ)^(1−2⁻ⁿ) · ‖ψ‖^(2⁻ⁿ)` for every `n`, by induction on the halving
recursion with the ambient bound as base case. -/
lemma rpSeminorm_translate_le_rpow {ψ : E} (hψ : ψ ∈ D.posTime)
    (hq : 0 < D.rpSeminorm ψ) (n : ℕ) :
    ∀ s : ℝ, 0 ≤ s →
      D.rpSeminorm (D.translate s ψ)
        ≤ D.rpSeminorm ψ ^ (1 - (2⁻¹ : ℝ) ^ n) * ‖ψ‖ ^ ((2⁻¹ : ℝ) ^ n) := by
  have hb : 0 < ‖ψ‖ := lt_of_lt_of_le hq (D.rpSeminorm_le_norm ψ)
  induction n with
  | zero =>
    intro s _
    simpa using D.rpSeminorm_translate_le_norm ψ s
  | succ n ih =>
    intro s hs
    set a := D.rpSeminorm ψ
    set t : ℝ := (2⁻¹ : ℝ) ^ n
    have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hsq : D.rpSeminorm (D.translate s ψ) ^ 2 ≤ a ^ (2 - t) * ‖ψ‖ ^ t := by
      calc D.rpSeminorm (D.translate s ψ) ^ 2
          ≤ a * D.rpSeminorm (D.translate (2 * s) ψ) := D.rpSeminorm_translate_sq_le hψ hs
        _ ≤ a * (a ^ (1 - t) * ‖ψ‖ ^ t) := by
            have h2s := ih (2 * s) (by linarith)
            exact mul_le_mul_of_nonneg_left h2s hq.le
        _ = a ^ (2 - t) * ‖ψ‖ ^ t := by
            rw [← mul_assoc,
              ← Real.rpow_one_add' hq.le (ne_of_gt (by linarith) : (1 : ℝ) + (1 - t) ≠ 0),
              show (1 : ℝ) + (1 - t) = 2 - t from by ring]
    have hstep : D.rpSeminorm (D.translate s ψ)
        ≤ Real.sqrt (a ^ (2 - t) * ‖ψ‖ ^ t) := by
      rw [show D.rpSeminorm (D.translate s ψ)
          = Real.sqrt (D.rpSeminorm (D.translate s ψ) ^ 2) from
          (Real.sqrt_sq (D.rpSeminorm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt hsq
    calc D.rpSeminorm (D.translate s ψ) ≤ Real.sqrt (a ^ (2 - t) * ‖ψ‖ ^ t) := hstep
      _ = a ^ ((2 - t) / 2) * ‖ψ‖ ^ (t / 2) := by
          rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul hq.le, ← Real.rpow_mul hb.le, mul_one_div, mul_one_div]
      _ = a ^ (1 - (2⁻¹ : ℝ) ^ (n + 1)) * ‖ψ‖ ^ ((2⁻¹ : ℝ) ^ (n + 1)) := by
          rw [show (2⁻¹ : ℝ) ^ (n + 1) = t / 2 from by rw [pow_succ]; ring,
            show (2 - t) / 2 = 1 - t / 2 from by ring]

/-- **The Osterwalder–Schrader contraction property** (Eq. 2.39):
`q(𝒰(s)ψ) ≤ q(ψ)` for `ψ` in the positive-time subspace and `s ≥ 0` — Euclidian time
translation is a contraction semigroup for the reflection form.  On quotient classes
this says `‖K(s)[ψ]‖ ≤ ‖[ψ]‖`, the contraction property of the Osterwalder–Schrader
transfer semigroup, and hence positivity of its generator.  Note the two norms
involved: unitarity of `𝒰(s)` for the ambient norm alone does not give this. -/
theorem rpSeminorm_translate_le {ψ : E} (hψ : ψ ∈ D.posTime) {s : ℝ} (hs : 0 ≤ s) :
    D.rpSeminorm (D.translate s ψ) ≤ D.rpSeminorm ψ := by
  rcases (D.rpSeminorm_nonneg ψ).eq_or_lt with hq | hq
  · -- null case: `q(ψ) = 0` forces `q(𝒰(s)ψ) = 0` by the halving recursion (Eq. 2.34)
    have hsq := D.rpSeminorm_translate_sq_le hψ hs
    rw [← hq, zero_mul] at hsq
    have h0 : D.rpSeminorm (D.translate s ψ) = 0 := by
      have := D.rpSeminorm_nonneg (D.translate s ψ)
      nlinarith
    rw [h0, ← hq]
  · -- positive case: take `n → ∞` in the iterated Cauchy–Schwarz bound (Eq. 2.38)
    have hb : 0 < ‖ψ‖ := lt_of_lt_of_le hq (D.rpSeminorm_le_norm ψ)
    have hbound := fun n => D.rpSeminorm_translate_le_rpow hψ hq n s hs
    have htend : Tendsto
        (fun n : ℕ => D.rpSeminorm ψ ^ (1 - (2⁻¹ : ℝ) ^ n) * ‖ψ‖ ^ ((2⁻¹ : ℝ) ^ n))
        atTop (𝓝 (D.rpSeminorm ψ)) := by
      have hhalf : Tendsto (fun n : ℕ => ((2⁻¹ : ℝ)) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hexp : Tendsto (fun n : ℕ => 1 - (2⁻¹ : ℝ) ^ n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub hhalf
      have h1 : Tendsto (fun n : ℕ => D.rpSeminorm ψ ^ (1 - (2⁻¹ : ℝ) ^ n)) atTop
          (𝓝 (D.rpSeminorm ψ)) := by
        have hc : ContinuousAt (fun x : ℝ => D.rpSeminorm ψ ^ x) 1 :=
          Real.continuousAt_const_rpow hq.ne'
        simpa [Function.comp_def, Real.rpow_one] using hc.tendsto.comp hexp
      have h2 : Tendsto (fun n : ℕ => ‖ψ‖ ^ ((2⁻¹ : ℝ) ^ n)) atTop (𝓝 1) := by
        have hc : ContinuousAt (fun x : ℝ => ‖ψ‖ ^ x) 0 :=
          Real.continuousAt_const_rpow hb.ne'
        simpa [Function.comp_def, Real.rpow_zero] using hc.tendsto.comp hhalf
      simpa [mul_one] using h1.mul h2
    exact ge_of_tendsto' htend hbound

/-! ## D. Null vectors: the quotient data of Eqs. 2.29–2.31 and 2.34

The Osterwalder–Schrader Hilbert space is the completion of `V/𝒩` (Eqs. 2.29–2.30);
the lemmas of this section are the well-definedness statements that license the
quotient: the reflection form does not see null summands (Eq. 2.30, "independent of
the representative by virtue of the Cauchy–Schwarz inequality"), and forward
translation preserves the null space (Eq. 2.34), so the transfer operator
`K(s)[ψ] := [𝒰(s)ψ]` of Eq. 2.31 is well defined on classes. -/

lemma form_add_right (ψ φ φ' : E) : D.form ψ (φ + φ') = D.form ψ φ + D.form ψ φ' := by
  rw [form, form, form, map_add, inner_add_right]

lemma form_smul_right (c : ℂ) (ψ φ : E) : D.form ψ (c • φ) = c * D.form ψ φ := by
  rw [form, form, map_smul, inner_smul_right]

lemma form_sub_right (ψ φ φ' : E) : D.form ψ (φ - φ') = D.form ψ φ - D.form ψ φ' := by
  rw [form, form, form, map_sub, inner_sub_right]

lemma form_sub_left (ψ ψ' φ : E) : D.form (ψ - ψ') φ = D.form ψ φ - D.form ψ' φ :=
  inner_sub_left _ _ _

/-- **Null vectors are invisible to the reflection form** (Eqs. 2.29–2.30): if
`(φ, φ) = 0` then `(ψ, φ) = 0` for every `ψ` in the positive-time subspace, by
Cauchy–Schwarz. -/
lemma form_eq_zero_of_null {ψ φ : E} (hψ : ψ ∈ D.posTime) (hφ : φ ∈ D.posTime)
    (hnull : (D.form φ φ).re = 0) : D.form ψ φ = 0 := by
  have h := D.norm_form_le hψ hφ
  rw [show D.rpSeminorm φ = 0 from by rw [rpSeminorm, hnull, Real.sqrt_zero],
    mul_zero] at h
  exact norm_le_zero_iff.mp h

/-- **Representative independence** (Eq. 2.30): adding a null vector to either slot
does not change the reflection form — the inner product on quotient classes is well
defined. -/
lemma form_add_null {ψ φ ψ' φ' : E} (hψ : ψ ∈ D.posTime) (hφ : φ ∈ D.posTime)
    (hψ' : ψ' ∈ D.posTime) (hφ' : φ' ∈ D.posTime)
    (hψnull : (D.form ψ' ψ').re = 0) (hφnull : (D.form φ' φ').re = 0) :
    D.form (ψ + ψ') (φ + φ') = D.form ψ φ := by
  have h1 : D.form ψ φ' = 0 := D.form_eq_zero_of_null hψ hφ' hφnull
  have h2 : D.form ψ' φ = 0 := by
    rw [← D.form_conj_symm, D.form_eq_zero_of_null hφ hψ' hψnull, map_zero]
  have h3 : D.form ψ' φ' = 0 := D.form_eq_zero_of_null hψ' hφ' hφnull
  rw [form_add_left, form_add_right, form_add_right, h1, h2, h3]
  ring

/-- **Forward translation preserves the null space** (Eq. 2.34): the transfer
operator `K(s)[ψ] := [𝒰(s)ψ]` of Eq. 2.31 is well defined on quotient classes. -/
lemma translate_null {ψ : E} (hψ : ψ ∈ D.posTime) {s : ℝ} (hs : 0 ≤ s)
    (hnull : (D.form ψ ψ).re = 0) :
    (D.form (D.translate s ψ) (D.translate s ψ)).re = 0 := by
  have hq : D.rpSeminorm (D.translate s ψ) = 0 := by
    have h := D.rpSeminorm_translate_le hψ hs
    rw [show D.rpSeminorm ψ = 0 from by rw [rpSeminorm, hnull, Real.sqrt_zero]] at h
    exact le_antisymm h (D.rpSeminorm_nonneg _)
  have := D.sq_rpSeminorm (D.translate_posTime s hs ψ hψ)
  rw [hq] at this
  simpa using this.symm

/-- **The transfer semigroup is positive for the reflection form** (Eq. 2.35):
`0 ≤ (ψ, 𝒰(s)ψ)` on the positive-time subspace, by halving the time step. -/
lemma form_translate_self_re_nonneg {ψ : E} (hψ : ψ ∈ D.posTime) {s : ℝ}
    (hs : 0 ≤ s) : 0 ≤ (D.form ψ (D.translate s ψ)).re := by
  have hhalf : D.form (D.translate (s / 2) ψ) (D.translate (s / 2) ψ)
      = D.form ψ (D.translate s ψ) := by
    rw [D.form_translate_left, ← D.translate_add,
      show s / 2 + s / 2 = s from by ring]
  rw [← hhalf]
  exact D.reflection_positive _ (D.translate_posTime (s / 2) (by linarith) ψ hψ)

/-! ## E. Reflection continuity of the transfer semigroup (Eq. 2.40) -/

/-- **The continuity estimate** (Eq. 2.40):
`q(𝒰(s)ψ − ψ)² ≤ ‖(ψ, 𝒰(2s)ψ) − (ψ,ψ)‖ + 2‖(ψ, 𝒰(s)ψ) − (ψ,ψ)‖` — the square of
the class distance `‖[K(s) − 1][ψ]‖` is estimated by matrix elements of
`𝒰(2s) − 1` and `𝒰(s) − 1` against the reflection form. -/
lemma rpSeminorm_translate_sub_sq_le {ψ : E} (hψ : ψ ∈ D.posTime) {s : ℝ}
    (hs : 0 ≤ s) :
    D.rpSeminorm (D.translate s ψ - ψ) ^ 2
      ≤ ‖D.form ψ (D.translate (2 * s) ψ) - D.form ψ ψ‖
        + 2 * ‖D.form ψ (D.translate s ψ) - D.form ψ ψ‖ := by
  have hmem : D.translate s ψ - ψ ∈ D.posTime :=
    Submodule.sub_mem _ (D.translate_posTime s hs ψ hψ) hψ
  have hdiag : D.form (D.translate s ψ) (D.translate s ψ)
      = D.form ψ (D.translate (2 * s) ψ) := by
    rw [D.form_translate_left, ← D.translate_add, two_mul]
  have hcross : (D.form (D.translate s ψ) ψ).re = (D.form ψ (D.translate s ψ)).re := by
    rw [← D.form_conj_symm ψ (D.translate s ψ)]
    exact Complex.conj_re _
  have hexpand : (D.form (D.translate s ψ - ψ) (D.translate s ψ - ψ)).re
      = (D.form ψ (D.translate (2 * s) ψ)).re
        - 2 * (D.form ψ (D.translate s ψ)).re + (D.form ψ ψ).re := by
    rw [form_sub_left, form_sub_right, form_sub_right, hdiag]
    simp only [Complex.sub_re]
    linarith [hcross]
  have h1 : (D.form ψ (D.translate (2 * s) ψ) - D.form ψ ψ).re
      ≤ ‖D.form ψ (D.translate (2 * s) ψ) - D.form ψ ψ‖ := by
    simpa [RCLike.re_to_complex] using
      RCLike.re_le_norm (D.form ψ (D.translate (2 * s) ψ) - D.form ψ ψ)
  have h2 : |(D.form ψ (D.translate s ψ) - D.form ψ ψ).re|
      ≤ ‖D.form ψ (D.translate s ψ) - D.form ψ ψ‖ := by
    simpa [RCLike.re_to_complex] using
      RCLike.abs_re_le_norm (D.form ψ (D.translate s ψ) - D.form ψ ψ)
  rw [D.sq_rpSeminorm hmem, hexpand]
  have h2' : -(D.form ψ (D.translate s ψ) - D.form ψ ψ).re
      ≤ ‖D.form ψ (D.translate s ψ) - D.form ψ ψ‖ := by
    calc -(D.form ψ (D.translate s ψ) - D.form ψ ψ).re
        ≤ |(D.form ψ (D.translate s ψ) - D.form ψ ψ).re| := neg_le_abs _
      _ ≤ _ := h2
  simp only [Complex.sub_re] at h1 h2'
  linarith

/-- **Reflection continuity transports to the transfer classes** (Eq. 2.40): if the
matrix element `(ψ, 𝒰(s)ψ)` is continuous at `s = 0⁺`, the class distance
`‖[K(s) − 1][ψ]‖ = q(𝒰(s)ψ − ψ)` tends to zero — the strong continuity that feeds
the Hille–Yosida theorem for the Osterwalder–Schrader Hamiltonian. -/
theorem tendsto_rpSeminorm_translate_sub {ψ : E} (hψ : ψ ∈ D.posTime)
    (hcont : Tendsto (fun s : ℝ => D.form ψ (D.translate s ψ)) (𝓝[≥] (0 : ℝ))
      (𝓝 (D.form ψ ψ))) :
    Tendsto (fun s : ℝ => D.rpSeminorm (D.translate s ψ - ψ)) (𝓝[≥] (0 : ℝ))
      (𝓝 0) := by
  have hdouble : Tendsto (fun s : ℝ => (2 : ℝ) * s) (𝓝[≥] (0 : ℝ)) (𝓝[≥] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hid : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_id
      have h2 : Tendsto (fun s : ℝ => (2 : ℝ) * s) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using hid.const_mul (2 : ℝ)
      exact h2.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_Ici.mpr (mul_nonneg (by norm_num) hs)
  have hbound : Tendsto
      (fun s : ℝ => ‖D.form ψ (D.translate (2 * s) ψ) - D.form ψ ψ‖
        + 2 * ‖D.form ψ (D.translate s ψ) - D.form ψ ψ‖) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    have t1 : Tendsto (fun s : ℝ => ‖D.form ψ (D.translate (2 * s) ψ) - D.form ψ ψ‖)
        (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
      have := ((hcont.comp hdouble).sub
        (tendsto_const_nhds (x := D.form ψ ψ))).norm
      simpa [Function.comp_def] using this
    have t2 : Tendsto (fun s : ℝ => 2 * ‖D.form ψ (D.translate s ψ) - D.form ψ ψ‖)
        (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
      have := ((hcont.sub (tendsto_const_nhds (x := D.form ψ ψ))).norm).const_mul (2 : ℝ)
      simpa using this
    simpa using t1.add t2
  have hsq : Tendsto (fun s : ℝ => Real.sqrt
      (‖D.form ψ (D.translate (2 * s) ψ) - D.form ψ ψ‖
        + 2 * ‖D.form ψ (D.translate s ψ) - D.form ψ ψ‖)) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hbound
    simpa [Function.comp_def] using this
  apply squeeze_zero' (Filter.Eventually.of_forall fun s => D.rpSeminorm_nonneg _) _ hsq
  filter_upwards [self_mem_nhdsWithin] with s hs
  have h := D.rpSeminorm_translate_sub_sq_le hψ (Set.mem_Ici.mp hs)
  calc D.rpSeminorm (D.translate s ψ - ψ)
      = Real.sqrt (D.rpSeminorm (D.translate s ψ - ψ) ^ 2) :=
        (Real.sqrt_sq (D.rpSeminorm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h

/-! ## F. Uniqueness of the vacuum under clustering (Eqs. 2.41–2.43) -/

/-- A vector whose forward translates differ from it by null vectors has constant
matrix elements along the flow (the content of `K(s)Ω = Ω`, Eqs. 2.41 and 2.43). -/
lemma form_translate_eq_of_null_diff {ω : E} (hω : ω ∈ D.posTime) {s : ℝ}
    (hs : 0 ≤ s)
    (hfix : (D.form (D.translate s ω - ω) (D.translate s ω - ω)).re = 0) :
    D.form ω (D.translate s ω) = D.form ω ω := by
  have hmem : D.translate s ω - ω ∈ D.posTime :=
    Submodule.sub_mem _ (D.translate_posTime s hs ω hω) hω
  have h0 : D.form ω (D.translate s ω - ω) = 0 :=
    D.form_eq_zero_of_null hω hmem hfix
  rw [form_sub_right] at h0
  linear_combination h0

/-- **The vacuum is unique up to a phase** (Eqs. 2.42–2.43): if the reflection form
clusters along the flow on `ω` — `(ω, 𝒰(s)ω) → (ω, 1)(1, ω)` as `s → ∞`
(Eq. 2.42) — and the class of `ω` is fixed by the transfer semigroup (Eq. 2.43),
then the class of `ω` is the multiple `(1, ω)·[1]` of the vacuum class: the defect
`(1, ω)•1 − ω` is a null vector. -/
theorem null_of_clustering_fixed {oneV ω : E}
    (hω : ω ∈ D.posTime) (hone : D.form oneV oneV = 1)
    (hclus : Tendsto (fun s : ℝ => D.form ω (D.translate s ω)) atTop
      (𝓝 (D.form ω oneV * D.form oneV ω)))
    (hfix : ∀ s : ℝ, 0 ≤ s →
      (D.form (D.translate s ω - ω) (D.translate s ω - ω)).re = 0) :
    (D.form (D.form oneV ω • oneV - ω) (D.form oneV ω • oneV - ω)).re = 0 := by
  set c : ℂ := D.form oneV ω with hc
  have hc' : D.form ω oneV = (starRingEnd ℂ) c := (D.form_conj_symm ω oneV).symm
  -- the matrix element is eventually constant along the flow, so its limit is `(ω,ω)`
  have hconst : Tendsto (fun s : ℝ => D.form ω (D.translate s ω)) atTop
      (𝓝 (D.form ω ω)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with s hs
    exact (D.form_translate_eq_of_null_diff hω hs (hfix s hs)).symm
  have hωω : D.form ω ω = (starRingEnd ℂ) c * c := by
    have := tendsto_nhds_unique hconst hclus
    rw [this, hc']
  -- expand the defect and cancel
  have hexpand : D.form (c • oneV - ω) (c • oneV - ω)
      = (starRingEnd ℂ) c * (c * D.form oneV oneV) - (starRingEnd ℂ) c * D.form oneV ω
        - c * D.form ω oneV + D.form ω ω := by
    rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left,
      form_smul_right, form_smul_right, form_smul_left]
    ring
  rw [hexpand, hone, ← hc, hc', hωω]
  ring_nf
  simp

end ReflectionPositiveFlow

end Physlib.QFT.OsterwalderSchrader

end
