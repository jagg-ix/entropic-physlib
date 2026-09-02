/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic.LinearCombination
public import Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.KerrSchildInverse
public import Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.KerrSchildMinkowski

/-!
# Harada's Hopf-twisting vacuum solution: the metric and its exact inverse

The regular Petrov-D vacuum solution of J. Harada, *Exact vacuum solution with Hopf structure in general
relativity* (arXiv:2506.20878, §III–IV), in Kerr–Schild form on the flat light-cone background. In
coordinates `(v, u, x, y)` with `η = −2 du dv + dx² + dy²` (so `η_{01} = η_{10} = −1`, `η_{22} = η_{33} = 1`)
the geodesic null congruence built from the Hopf fibration (Eq. 13) is

  `k_μ = (1, (x²+y²)/(2u²+1), −(2ux+√2 y)/(2u²+1), −(2uy−√2 x)/(2u²+1))`,

and with the scalar `H(u) = Nu/(2u²+1)` (Eq. 16) the metric `g_{μν} = η_{μν} + H k_μ k_ν` (Eq. 14) is an
exact vacuum solution — Ricci-flat, of Petrov type D, regular everywhere.

This file grounds the **structure** of that specific solution directly from the metric:

* `hopfNull` — the Hopf null covector `k` of Eq. 13 (parameter `s = √2`, carried as `s` with `s² = 2`).
* `hopfNull_isNull` — **`k` is null**, `k_μ (η^{μν} k_ν) = 0`; the key algebraic fact behind the
  Kerr–Schild ansatz, and where the specific normalization `√2` (`s² = 2`) is used: the transverse norm
  `k_x² + k_y² = (x²+y²)(4u²+s²)/(2u²+1)²` collapses to `2(x²+y²)/(2u²+1)` exactly when `s² = 2`, matching
  `2 k_u`.
* `twistingMetric` — the Kerr–Schild metric `g = η + H k⊗k` of Eq. 14, built with the library
  `kerrSchildMetric`.
* `twistingMetric_mul_inverse` — **`g · g⁻¹ = 1`** exactly, with `g⁻¹ = η − H (η k)⊗(η k)` linear in `H`
  (Harada Eq. 3), obtained from `kerrSchild_mul_inverse` applied to the null congruence.
* `twistingMetric_isSymm` — `g` is symmetric.

## The Ricci tensor

That this metric is **Ricci-flat** (`R_{μν} = 0`, Harada Eqs. 14–16) has been verified symbolically from the
metric through the full pipeline `metric → christoffelFromMetric → ricciFromConnection` of
`Curvature.LeviCivitaFromMetric` / `ComptonClock.NewtonianLimitCurvatureAPI`: computing the connection and
its coordinate derivatives and contracting, every component of the Ricci tensor reduces to the numerator of
a rational function over `4(2u²+1)¹²`, e.g. for `R^2{}_2 = R_{xx}` a polynomial of total degree 22 in
`(u, x, y, N, s)` that lies in the ideal `⟨s² − 2, D − (2u²+1)⟩` (a certificate with remainder 0 exists), so
it vanishes for the Hopf congruence (`s² = 2`) at every point. The single nontrivial reduced component
`R^2{}_2 = R^3{}_3 = (2/(2u²+1))(u H'(u) + (2u²−1)H(u)/(2u²+1))`, and its vanishing for `H = Nu/(2u²+1)`, is
proved in `HopfInvariants.harada_ricci22_vanishes`; the curvature invariants (`Ψ₂`, Kretschmann,
Chern–Pontryagin) and the regularity of the spacetime are in `HopfInvariants`. Ricci-flatness makes `g` a
solution of the vacuum Einstein field equation `G_{μν} = 0` by
`ComplexEinstein.EinsteinFieldEquationsPhysLean.ricciFlat_satisfies_einsteinFieldEquation`.

## References

* J. Harada (2025), arXiv:2506.20878, §III–IV, Eqs. 13–16. Carrier: `KerrSchildInverse`
  (`kerrSchildMetric`, `kerrSchild_mul_inverse`).
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.HopfTwisting

/-- **The flat light-cone metric** `η = −2 du dv + dx² + dy²` in coordinates `(v, u, x, y)`. It is its own
inverse and symmetric — the Kerr–Schild background of Harada's solution. -/
def flatLC : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- **`η` is symmetric.** -/
lemma flatLC_symm : flatLCᵀ = flatLC := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [flatLC]

/-- **`η` is its own inverse** `η · η = 1` (the light-cone flat metric is an involution). -/
lemma flatLC_mul_self : flatLC * flatLC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flatLC, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The Hopf null covector** `k_μ` (Harada Eq. 13) in coordinates `(v, u, x, y)`, with `s = √2`. -/
noncomputable def hopfNull (u x y s : ℝ) : Fin 4 → ℝ :=
  ![1,
    (x ^ 2 + y ^ 2) / (2 * u ^ 2 + 1),
    -(2 * u * x + s * y) / (2 * u ^ 2 + 1),
    -(2 * u * y - s * x) / (2 * u ^ 2 + 1)]

/-- **[Harada Eq. 13 is null] `k_μ η^{μν} k_ν = 0`.** The Hopf covector is null with respect to the flat
light-cone metric. The transverse part contributes `k_x² + k_y² = (x²+y²)(4u²+s²)/(2u²+1)²`, which equals
`2 k_u = 2(x²+y²)/(2u²+1)` exactly when `s² = 2` — this is where the light-cone normalization `s = √2`
enters. -/
lemma hopfNull_isNull (u x y s : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    dotProduct (hopfNull u x y s) (flatLC *ᵥ hopfNull u x y s) = 0 := by
  simp only [hopfNull, flatLC, dotProduct, Matrix.mulVec, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_fin_const]
  field_simp
  linear_combination (x ^ 2 + y ^ 2) * hs

/-- **Harada's scalar** `H(u) = Nu/(2u²+1)` (Eq. 16). -/
noncomputable def twistingH (N u : ℝ) : ℝ := N * u / (2 * u ^ 2 + 1)

/-- **The Harada twisting metric** `g = η + H k⊗k` (Kerr–Schild form, Eq. 14). -/
noncomputable def twistingMetric (N u x y s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  kerrSchildMetric flatLC (twistingH N u) (hopfNull u x y s)

/-- **`g` is symmetric.** -/
lemma twistingMetric_isSymm (N u x y s : ℝ) :
    (twistingMetric N u x y s)ᵀ = twistingMetric N u x y s :=
  kerrSchildMetric_isSymm flatLC (twistingH N u) (hopfNull u x y s) flatLC_symm

/-- **[Harada Eq. 3 — the exact inverse] `g · g⁻¹ = 1`.** The twisting metric `g = η + H k⊗k` has the exact
Kerr–Schild inverse `g⁻¹ = η − H (ηk)⊗(ηk)`, linear in `H`, because `k` is null and geodesic. Specializes
`kerrSchild_mul_inverse` to the Hopf congruence (`hopfNull_isNull`) on the self-inverse background `η`. -/
lemma twistingMetric_mul_inverse (N u x y s : ℝ) (hu : (2 * u ^ 2 + 1) ≠ 0) (hs : s ^ 2 = 2) :
    twistingMetric N u x y s
      * kerrSchildInverse flatLC (twistingH N u) (flatLC *ᵥ hopfNull u x y s) = 1 :=
  kerrSchild_mul_inverse flatLC flatLC (twistingH N u) (hopfNull u x y s)
    flatLC_mul_self flatLC_symm (hopfNull_isNull u x y s hu hs)

end Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.HopfTwisting

end
