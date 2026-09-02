/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# The full Witt algebra as a genuine Lie algebra of derivations of `ℝ[T, T⁻¹]`

`WittAlgebraLieRing` realized only the finite `sl(2,ℝ)` subalgebra as a matrix Lie ring, and
`VirasoroCentralExtension` characterized the Virasoro algebra by its structure constants. This module
supplies the honest **infinite-dimensional** object: the entire Witt algebra as a genuine Lie algebra —
the Lie ring of derivations of the Laurent polynomials `ℝ[T, T⁻¹]` — so its Jacobi identity is *inherited*
from Mathlib's `LieRing (Derivation ℝ A A)` rather than re-proved.

The Witt algebra is the algebra of algebraic vector fields on the circle, `L_m = T^m · (T d/dT)`. We build
it through the **Euler derivation** `E` with `E(T^n) = n · T^n` — a derivation because the exponent is
additive under multiplication (`Derivation.mk' eulerLin`, Leibniz proved on the `C`/`T` monomial basis).
Setting `L_m := T^m · E` (`wittGen`, as a `Derivation.mk'` since the `A`-action on derivations has no ready
instance), the Witt bracket

  `⁅L_m, L_n⁆ = (n − m) L_{m+n}`   (`wittGen_bracket`)

holds inside `Derivation ℝ (ℝ[T,T⁻¹]) (ℝ[T,T⁻¹])`, and the Jacobi identity of that Lie ring is Mathlib's.
This is the genuine Lie-algebra object behind the structure constants `wittCoeff` of
`VirasoroCentralExtension` (the `(n − m)` here vs its `(m − n)` is the `L_m ↦ −L_m` sign of the two standard
conventions).

Construction note: `LaurentPolynomial ℝ = AddMonoidAlgebra ℝ ℤ` is an opaque `def`, so `Finsupp.lsum`'s
lemmas (`lsum_single`) do not fire on it under `rw`'s keyed matching. `eulerLin_single` therefore obtains
the fact at the raw `ℤ →₀ ℝ` type and closes by `exact` (default transparency bridges the type synonym),
and everything else stays in the `C`/`T` API.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WittAlgebraDerivation

open LaurentPolynomial

/-- The `ℝ`-linear "multiply by degree" map `T^n ↦ n · T^n` on `ℝ[T, T⁻¹]`. -/
noncomputable def eulerLin : LaurentPolynomial ℝ →ₗ[ℝ] LaurentPolynomial ℝ :=
  (AddMonoidAlgebra.basis ℤ ℝ).constr ℝ fun n => (n : ℝ) • T n

theorem eulerLin_single (n : ℤ) (r : ℝ) :
    eulerLin (AddMonoidAlgebra.single n r) =
      (n : ℝ) • AddMonoidAlgebra.single n r := by
  have hsingle : AddMonoidAlgebra.single n r = r • T n := by
    rw [single_eq_C_mul_T, C_eq_algebraMap]
    exact (Algebra.smul_def r (T n)).symm
  have heuler : eulerLin (T n) = (n : ℝ) • T n := by
    exact (AddMonoidAlgebra.basis ℤ ℝ).constr_basis ℝ
      (fun n => (n : ℝ) • T n) n
  rw [hsingle, map_smul, heuler]
  simp [smul_smul, mul_comm]

theorem eulerLin_C_mul_T (n : ℤ) (r : ℝ) :
    eulerLin (C r * T n) = (n : ℝ) • (C r * T n) := by
  rw [← single_eq_C_mul_T]; exact eulerLin_single n r

/-- Product of two Laurent monomials. -/
theorem C_T_mul (r s : ℝ) (m n : ℤ) :
    (C r * T m) * (C s * T n) = C (r * s) * T (m + n) := by
  rw [mul_mul_mul_comm, ← map_mul, ← T_add]

/-- **The Euler derivation** `E` of `ℝ[T, T⁻¹]` with `E(T^n) = n · T^n`. -/
noncomputable def eulerDeriv : Derivation ℝ (LaurentPolynomial ℝ) (LaurentPolynomial ℝ) :=
  Derivation.mk' eulerLin <| by
    intro a b
    induction a using LaurentPolynomial.induction_on' with
    | add p q hp hq => simp only [add_mul, map_add, hp, hq, smul_eq_mul]; ring
    | C_mul_T m r =>
        induction b using LaurentPolynomial.induction_on' with
        | add p q hp hq => simp only [mul_add, map_add, hp, hq, smul_eq_mul]; ring
        | C_mul_T n s =>
            rw [C_T_mul, eulerLin_C_mul_T, eulerLin_C_mul_T, eulerLin_C_mul_T,
              smul_comm (C r * T m) (n : ℝ), smul_comm (C s * T n) (m : ℝ),
              smul_eq_mul, smul_eq_mul, C_T_mul, C_T_mul,
              add_comm n m, mul_comm s r, ← add_smul]
            congr 1
            push_cast; ring

@[simp] theorem eulerDeriv_C_mul_T (n : ℤ) (r : ℝ) :
    eulerDeriv (C r * T n) = (n : ℝ) • (C r * T n) :=
  eulerLin_C_mul_T n r

@[simp] theorem eulerDeriv_T (n : ℤ) : eulerDeriv (T n) = (n : ℝ) • T n := by
  simpa using eulerDeriv_C_mul_T n 1

/-- **The Witt generator** `L_m = T^m · E` as a derivation of `ℝ[T, T⁻¹]`. -/
noncomputable def wittGen (m : ℤ) : Derivation ℝ (LaurentPolynomial ℝ) (LaurentPolynomial ℝ) :=
  Derivation.mk' ((LinearMap.mulLeft ℝ (T m)).comp eulerDeriv.toLinearMap) <| by
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
      Derivation.leibniz, smul_eq_mul]
    ring

theorem wittGen_apply (m : ℤ) (x : LaurentPolynomial ℝ) :
    wittGen m x = T m * eulerDeriv x := by
  simp only [wittGen, Derivation.coe_mk', LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe]

/-- **The Witt bracket** `⁅L_m, L_n⁆ = (n − m) L_{m+n}` — the defining relation of the Witt algebra, holding
in the genuine Lie ring of derivations of `ℝ[T, T⁻¹]`, with the Jacobi identity inherited from Mathlib's
`LieRing (Derivation ℝ A A)`. This is the honest infinite-dimensional realization of the structure constants
of `VirasoroCentralExtension` (the `(n − m)` vs `(m − n)` is the `L_m ↦ −L_m` sign of the two conventions). -/
theorem wittGen_bracket (m n : ℤ) :
    ⁅wittGen m, wittGen n⁆ = ((n : ℝ) - (m : ℝ)) • wittGen (m + n) := by
  refine Derivation.ext fun x => ?_
  rw [Derivation.commutator_apply, Derivation.smul_apply]
  simp only [wittGen_apply, Derivation.leibniz, eulerDeriv_T, smul_eq_mul]
  rw [T_add m n]
  simp only [Algebra.smul_def, map_sub]
  ring

end Physlib.QuantumMechanics.ComplexAction.WittAlgebraDerivation

end
