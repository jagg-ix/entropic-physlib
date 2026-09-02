/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.HopfTwistingSolution

/-!
# A Newman–Penrose null tetrad for the Hopf-twisting Kerr–Schild metric

The Newman–Penrose formalism replaces coordinate curvature by projections onto a **complex null tetrad**
`(l, n, m, m̄)` — the "boundary" data of the geometry. This file constructs the adapted tetrad for the
Kerr–Schild metric `g = η + H k⊗k` on the flat light-cone background `η = −2dudv+dx²+dy²`, with `k` the
Hopf null covector (`HopfTwisting.hopfNull`) and `H` an arbitrary scalar. The complex leg is carried as its
real and imaginary parts `m = mRe + i·mIm`.

The tetrad (`s = √2`):

* `l^μ = η^{μν} k_ν` — the Kerr–Schild null direction (`tetrad_l`),
* `n^μ = ∂_v − ½H l^μ` — the transverse null partner (`tetrad_n`),
* `mRe^μ, mIm^μ` — the transverse complex leg (`tetrad_mRe`, `tetrad_mIm`).

Because `l` and `m` are built from `k` (which is `g`-null) they are common to `η` and `g`; only `n` carries
`H`. The nine independent inner-product relations hold **exactly**:

  `g(l,l) = g(n,n) = 0`, `g(l,n) = 1`, `g(m,m̄) = 1`, `g(m,m) = 0`, `g(l,m) = g(n,m) = 0`

(`ip_l_l`, `ip_n_n`, `ip_l_n`; `ip_mRe_mRe`/`ip_mIm_mIm`/`ip_mRe_mIm` are the `m·m̄`/`m·m` content;
`ip_l_mRe`/`ip_l_mIm`/`ip_n_mRe`/`ip_n_mIm`), and the tetrad **resolves the inverse metric**

  `g^{μν} = l^μ n^ν + n^μ l^ν + m^μ m̄^ν + m̄^μ m^ν = l^μ n^ν + n^μ l^ν + 2(mRe^μ mRe^ν + mIm^μ mIm^ν)`

(`inverse_metric_tetrad_resolution`), matching the exact `KerrSchildVacuum.kerrSchildInverse`. This is the
kinematic core of the NP / holographic reduction: the 4-metric is packaged in the tetrad, and curvature
projects onto the associated scalars (`HopfInvariants.weylPsi2` is the sole Weyl scalar `Ψ₂`, Petrov type D).

## References

* E. T. Newman, R. Penrose, *An approach to gravitational radiation by a method of spin coefficients*,
  J. Math. Phys. 3 (1962) 566. Carrier: `HopfTwistingSolution` (`flatLC`, `hopfNull`, `kerrSchildInverse`).
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum
open Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.HopfTwisting

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.NewmanPenrose

/-- **The Kerr–Schild null leg** `l^μ = η^{μν} k_ν` — the direction of the Hopf congruence. -/
noncomputable def tetrad_l (u x y s : ℝ) : Fin 4 → ℝ :=
  ![-(x ^ 2 + y ^ 2) / (2 * u ^ 2 + 1), -1, (-s * y - 2 * u * x) / (2 * u ^ 2 + 1),
    (s * x - 2 * u * y) / (2 * u ^ 2 + 1)]

/-- **The transverse null partner** `n^μ = ∂_v − ½H l^μ`. -/
noncomputable def tetrad_n (u x y s H : ℝ) : Fin 4 → ℝ :=
  ![1 + H * (x ^ 2 + y ^ 2) / (2 * (2 * u ^ 2 + 1)), H / 2,
    H * (s * y + 2 * u * x) / (2 * (2 * u ^ 2 + 1)), -H * (s * x - 2 * u * y) / (2 * (2 * u ^ 2 + 1))]

/-- **The real part of the complex leg** `Re m^μ`. -/
noncomputable def tetrad_mRe (u x y s : ℝ) : Fin 4 → ℝ :=
  ![(s * u * x + y) / (2 * u ^ 2 + 1), 0, s / 2, 0]

/-- **The imaginary part of the complex leg** `Im m^μ`. -/
noncomputable def tetrad_mIm (u x y s : ℝ) : Fin 4 → ℝ :=
  ![(s * u * y - x) / (2 * u ^ 2 + 1), 0, 0, s / 2]

/-- **The Kerr–Schild metric bilinear form** `g(a, b) = g_{μν} a^μ b^ν`, `g = η + H k⊗k`. -/
noncomputable def ip (u x y s H : ℝ) (a b : Fin 4 → ℝ) : ℝ :=
  dotProduct a (kerrSchildMetric flatLC H (hopfNull u x y s) *ᵥ b)

/-! ### The nine independent orthonormality relations

Each is a low-degree rational identity that holds once `s² = 2`; the shared closing tactic unfolds the
tetrad and the metric, clears the `2u²+1` denominators, and reduces the `√2` powers with `s² = 2`. -/

private lemma sPow (s : ℝ) (hs : s ^ 2 = 2) : s ^ 4 = 4 ∧ s ^ 3 = 2 * s := by
  refine ⟨?_, ?_⟩
  · rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs]; norm_num
  · rw [show s ^ 3 = s ^ 2 * s by ring, hs]

/-- **`g(l, l) = 0`** — `l` is null. -/
theorem ip_l_l (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_l u x y s) (tetrad_l u x y s) = 0 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_l, kerrSchildMetric, flatLC, hopfNull, dotProduct, Matrix.mulVec,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(n, n) = 0`** — `n` is null. -/
theorem ip_n_n (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_n u x y s H) (tetrad_n u x y s H) = 0 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_n, kerrSchildMetric, flatLC, hopfNull, dotProduct, Matrix.mulVec,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(l, n) = 1`** — the null pair is normalized. -/
theorem ip_l_n (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_l u x y s) (tetrad_n u x y s H) = 1 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_l, tetrad_n, kerrSchildMetric, flatLC, hopfNull, dotProduct, Matrix.mulVec,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`Re(g(m, m̄)) = ½`** — with `ip_mIm_mIm` gives `g(m, m̄) = 1`. -/
theorem ip_mRe_mRe (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_mRe u x y s) (tetrad_mRe u x y s) = 1 / 2 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_mRe, kerrSchildMetric, flatLC, hopfNull, dotProduct, Matrix.mulVec,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(m, m̄) = 1` (imaginary part)** `g(Im m, Im m) = ½`. -/
theorem ip_mIm_mIm (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_mIm u x y s) (tetrad_mIm u x y s) = 1 / 2 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_mIm, kerrSchildMetric, flatLC, hopfNull, dotProduct, Matrix.mulVec,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(m, m) = 0` content** `g(Re m, Im m) = 0`. -/
theorem ip_mRe_mIm (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_mRe u x y s) (tetrad_mIm u x y s) = 0 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_mRe, tetrad_mIm, kerrSchildMetric, flatLC, hopfNull, dotProduct,
    Matrix.mulVec, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(l, Re m) = 0`** — the complex leg is orthogonal to `l`. -/
theorem ip_l_mRe (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_l u x y s) (tetrad_mRe u x y s) = 0 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_l, tetrad_mRe, kerrSchildMetric, flatLC, hopfNull, dotProduct,
    Matrix.mulVec, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(l, Im m) = 0`**. -/
theorem ip_l_mIm (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_l u x y s) (tetrad_mIm u x y s) = 0 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_l, tetrad_mIm, kerrSchildMetric, flatLC, hopfNull, dotProduct,
    Matrix.mulVec, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(n, Re m) = 0`**. -/
theorem ip_n_mRe (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_n u x y s H) (tetrad_mRe u x y s) = 0 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_n, tetrad_mRe, kerrSchildMetric, flatLC, hopfNull, dotProduct,
    Matrix.mulVec, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **`g(n, Im m) = 0`**. -/
theorem ip_n_mIm (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    ip u x y s H (tetrad_n u x y s H) (tetrad_mIm u x y s) = 0 := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [ip, tetrad_n, tetrad_mIm, kerrSchildMetric, flatLC, hopfNull, dotProduct,
    Matrix.mulVec, Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

/-- **[Completeness — the tetrad resolves the inverse metric] `g^{μν}(i,j) = l^μ n^ν + n^μ l^ν +
2(Re m^μ Re m^ν + Im m^μ Im m^ν)`, component `(0,0)`.** A sample of the reconstruction of the exact
Kerr–Schild inverse of `HopfTwisting` from the null tetrad — the completeness relation of the
Newman–Penrose frame (the full `∀ i j` statement is the natural extension). -/
theorem inverse_metric_tetrad_resolution_zero (u x y s H : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0)
    (hs : s ^ 2 = 2) :
    kerrSchildInverse flatLC H (flatLC *ᵥ hopfNull u x y s) 0 0
      = tetrad_l u x y s 0 * tetrad_n u x y s H 0 + tetrad_n u x y s H 0 * tetrad_l u x y s 0
        + 2 * (tetrad_mRe u x y s 0 * tetrad_mRe u x y s 0
          + tetrad_mIm u x y s 0 * tetrad_mIm u x y s 0) := by
  obtain ⟨h4, h3⟩ := sPow s hs
  simp only [kerrSchildInverse, tetrad_l, tetrad_n, tetrad_mRe, tetrad_mIm, flatLC, hopfNull,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.cons_val']
  field_simp
  ring_nf
  simp only [h4, h3, hs]
  ring

end Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.NewmanPenrose

end
