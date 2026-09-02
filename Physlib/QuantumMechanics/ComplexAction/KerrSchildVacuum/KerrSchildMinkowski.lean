/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.KerrSchildInverse
public import Physlib.Relativity.MinkowskiMatrix

/-!
# The Kerr–Schild metric over physical Minkowski spacetime

Links the abstract Kerr–Schild inverse (`KerrSchildVacuum.KerrSchildInverse`) to physlib's relativity framework: the flat
metric `η` of the Kerr–Schild form `g = η + H k k` is physlib's `minkowskiMatrix` (the signature `(1,−1,…,−1)`
metric on `Fin 1 ⊕ Fin d`). Because `minkowskiMatrix` is its own inverse (`minkowskiMatrix.sq`) and symmetric
(`minkowskiMatrix.eq_transpose`), the Kerr–Schild inverse identity specializes to a concrete statement on
Minkowski spacetime.

* `kerrSchildMinkowski_mul_inverse` — `g · g⁻¹ = 1` for the Minkowski Kerr–Schild metric, given a covector `k`
  null with respect to `minkowskiMatrix` (the geodesic null congruence of Harada's solution).
* `kerrSchildMetric_isSymm` — the Kerr–Schild metric is symmetric.
* `kerrSchildMetric_zero` — at `H = 0` it is the flat metric (asymptotic flatness: Harada's `N → 0` limit).

## References

* J. Harada (2025), arXiv:2506.20878, §II; R. P. Kerr & A. Schild. Carrier: `Physlib`
  (`KerrSchildVacuum.KerrSchildInverse`, `Relativity.MinkowskiMatrix`).


-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **[The Kerr–Schild metric is symmetric] `gᵀ = g`** for a symmetric flat metric `η`. -/
lemma kerrSchildMetric_isSymm (η : Matrix ι ι ℝ) (H : ℝ) (k : ι → ℝ) (hη : ηᵀ = η) :
    (kerrSchildMetric η H k)ᵀ = kerrSchildMetric η H k := by
  ext i j
  have hηs : η j i = η i j := by
    have h := congrFun (congrFun hη i) j; rwa [Matrix.transpose_apply] at h
  simp only [Matrix.transpose_apply, kerrSchildMetric, Matrix.of_apply, hηs]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **[Flat limit — asymptotic flatness] `g = η` at `H = 0`.** As Harada's `H = Nu/(u²+b²) → 0` (e.g. `N → 0`
or `u → ±∞`), the Kerr–Schild metric approaches the flat metric. -/
lemma kerrSchildMetric_zero (η : Matrix ι ι ℝ) (k : ι → ℝ) :
    kerrSchildMetric η 0 k = η := by
  ext i j; simp [kerrSchildMetric]

/-- **[The Kerr–Schild inverse over Minkowski spacetime] `g · g⁻¹ = 1`.** For the flat metric
`η = minkowskiMatrix` and a covector `k` null with respect to it (the geodesic null congruence), the
Kerr–Schild metric `g = η + H k k` has exact inverse `η − H k^μ k^ν`, linear in `H`. -/
lemma kerrSchildMinkowski_mul_inverse {d : ℕ} (H : ℝ) (k : Fin 1 ⊕ Fin d → ℝ)
    (hnull : dotProduct k (minkowskiMatrix *ᵥ k) = 0) :
    kerrSchildMetric minkowskiMatrix H k
      * kerrSchildInverse minkowskiMatrix H (minkowskiMatrix *ᵥ k) = 1 :=
  kerrSchild_mul_inverse minkowskiMatrix minkowskiMatrix H k minkowskiMatrix.sq
    minkowskiMatrix.eq_transpose hnull

end Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum

end
