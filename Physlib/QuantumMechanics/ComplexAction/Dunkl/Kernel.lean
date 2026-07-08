/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator

/-!
# The Dunkl kernel (deformed exponential) `E_ν` (Junker Eqs. 11–28)

Formalizes the algebraic core of the Dunkl kernel and Dunkl transform section of Junker (arXiv:2312.12895,
§2.1–§2.2). The Dunkl kernel is the deformed exponential `E_ν(z) = ∑_{n} z^n/[n]_ν!` (Eq. 13), built from
the Dunkl factorial `[n]_ν! = [1]_ν[2]_ν⋯[n]_ν` (Eq. 11). We formalize the parts that are algebraic (the
factorial, the Taylor coefficients, the eigenfunction property, the normalisation `c_ν`); the analytic
identities (Bessel/hypergeometric forms Eqs. 14–17, the Dunkl-transform integrals Eqs. 22–28) are noted as
out of scope.

* **§A — the Dunkl factorial (Eq. 11).** `dunklFactorial ν n = ∏_{k=1}^n [k]_ν` (`dunklFactorial_succ`),
  with `[n]_0! = n!` (`dunklFactorial_zero_param`) — at `ν = 0` the deformed factorial is the ordinary
  factorial.
* **§B — the Dunkl-kernel coefficients (Eq. 13).** `dunklKernelCoeff ν n = 1/[n]_ν!`, with `E_ν(0) = 1`
  (`dunklKernel_at_zero`) and `E_0` coefficients `= 1/n!` (`dunklKernelCoeff_zero_param`) — the `ν = 0`
  kernel is the ordinary exponential `E_0 = exp`.
* **§C — the eigenfunction property (Eqs. 19–20).** `D_ν E_ν = E_ν`: the Dunkl operator shifts the kernel
  coefficients down by one — at the coefficient level `[n]_ν · (1/[n]_ν!) = 1/[n−1]_ν!`
  (`dunklKernel_eigen_coeff`), and on the monomials `D_ν(Xⁿ/[n]_ν!) = Xⁿ⁻¹/[n−1]_ν!`
  (`dunklOp_kernelMonomial`), using `dunklOp_Xpow` (Eq. 19).
* **§D — the normalisation `c_ν` (Eq. 18).** `c_ν = 2^{ν+½}Γ(ν+½)` (`cNu`).
* **§E — positivity** (`dunklNumber_pos`): `[n]_ν > 0` for `n ≥ 1`, `ν > −½`, so the Dunkl factorial is
  nonzero and the kernel/eigenfunction are well defined (the measure bound `ν > −½` of Eq. 6).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.Kernel

open Polynomial
open Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator

/-! ## §A — the Dunkl factorial `[n]_ν!` (Junker Eq. 11) -/

/-- **[Junker Eq. 11] The Dunkl factorial** `[n]_ν! = [1]_ν [2]_ν ⋯ [n]_ν` (with `[0]_ν! = 1`). -/
noncomputable def dunklFactorial (ν : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, dunklNumber ν (k + 1)

/-- `[0]_ν! = 1` (empty product). -/
theorem dunklFactorial_zero (ν : ℝ) : dunklFactorial ν 0 = 1 := by simp [dunklFactorial]

/-- **The Dunkl factorial recursion** `[n+1]_ν! = [n+1]_ν · [n]_ν!`. -/
theorem dunklFactorial_succ (ν : ℝ) (n : ℕ) :
    dunklFactorial ν (n + 1) = dunklFactorial ν n * dunklNumber ν (n + 1) := by
  simp [dunklFactorial, Finset.prod_range_succ]

/-- **At `ν = 0` the Dunkl factorial is the ordinary factorial** `[n]_0! = n!` — the deformation vanishes,
so the Dunkl kernel `E_0` becomes the ordinary exponential. -/
theorem dunklFactorial_zero_param (n : ℕ) : dunklFactorial 0 n = (n.factorial : ℝ) := by
  induction n with
  | zero => simp [dunklFactorial]
  | succ k ih =>
    rw [dunklFactorial_succ, ih, dunklNumber_zero_param, Nat.factorial_succ]; push_cast; ring

/-! ## §B — the Dunkl-kernel coefficients `1/[n]_ν!` (Junker Eq. 13) -/

/-- **[Junker Eq. 13] The `n`-th Taylor coefficient of the Dunkl kernel** `E_ν(z) = ∑_n z^n/[n]_ν!`. -/
noncomputable def dunklKernelCoeff (ν : ℝ) (n : ℕ) : ℝ := 1 / dunklFactorial ν n

/-- **`E_ν(0) = 1`**: the constant Taylor coefficient `1/[0]_ν! = 1`; the Dunkl kernel, like an exponential,
is `1` at the origin (`E_ν(0) = 1`, Junker after Eq. 16). -/
theorem dunklKernel_at_zero (ν : ℝ) : dunklKernelCoeff ν 0 = 1 := by
  simp [dunklKernelCoeff, dunklFactorial_zero]

/-- **At `ν = 0` the Dunkl-kernel coefficients are `1/n!`** — the Taylor coefficients of the ordinary
exponential, so `E_0(z) = ∑ z^n/n! = e^z` (Junker after Eq. 16). -/
theorem dunklKernelCoeff_zero_param (n : ℕ) : dunklKernelCoeff 0 n = 1 / (n.factorial : ℝ) := by
  rw [dunklKernelCoeff, dunklFactorial_zero_param]

/-! ## §C — the eigenfunction property `D_ν E_ν = E_ν` (Junker Eqs. 19–20) -/

/-- `R` commutes with real scalars (helper for `dunklOp` linearity). -/
theorem reflPoly_smul (c : ℝ) (p : ℝ[X]) : reflPoly (c • p) = c • reflPoly p := by
  simp [reflPoly, smul_comp]

/-- **The Dunkl operator is `ℝ`-linear under scalars** `D_ν(c·p) = c·D_ν p`. -/
theorem dunklOp_smul (ν c : ℝ) (p : ℝ[X]) : dunklOp ν (c • p) = c • dunklOp ν p := by
  unfold dunklOp dunklDeform
  rw [derivative_smul, reflPoly_smul, ← smul_sub, divX_smul, smul_comm ν c, smul_add]

/-- **[Junker Eqs. 19–20, coefficient form] The Dunkl operator shifts the kernel coefficients down by one**:
`[n]_ν · (1/[n]_ν!) = 1/[n−1]_ν!`. Applied termwise to `E_ν(z) = ∑ z^n/[n]_ν!` this is the eigenfunction
relation `D_x E_ν(ax) = a E_ν(ax)` (Eq. 20). -/
theorem dunklKernel_eigen_coeff (ν : ℝ) (n : ℕ) (hn : dunklNumber ν (n + 1) ≠ 0) :
    dunklNumber ν (n + 1) * dunklKernelCoeff ν (n + 1) = dunklKernelCoeff ν n := by
  rw [dunklKernelCoeff, dunklKernelCoeff, dunklFactorial_succ]; field_simp [hn]

/-- **[Junker Eqs. 19–20, monomial form] `D_ν(Xⁿ⁺¹/[n+1]_ν!) = Xⁿ/[n]_ν!`** — the Dunkl operator maps each
normalized Dunkl-kernel monomial to the previous one, exactly as `d/dx (xⁿ/n!) = xⁿ⁻¹/(n−1)!` does for the
ordinary exponential. Termwise this is `D_ν E_ν = E_ν` (the kernel is the eigenfunction of `D_ν`, Eq. 20).
Uses `dunklOp_Xpow` (Eq. 19). -/
theorem dunklOp_kernelMonomial (ν : ℝ) (n : ℕ) (hn : dunklNumber ν (n + 1) ≠ 0) :
    dunklOp ν ((1 / dunklFactorial ν (n + 1)) • X ^ (n + 1))
      = (1 / dunklFactorial ν n) • X ^ n := by
  rw [dunklOp_smul, dunklOp_Xpow ν (Nat.le_add_left 1 n), Nat.add_sub_cancel, smul_smul,
    dunklFactorial_succ]
  congr 1
  field_simp [hn]

/-! ## §D — the Dunkl normalisation `c_ν` (Junker Eq. 18) -/

/-- **[Junker Eq. 18] The Dunkl normalisation constant** `c_ν = 2^{ν+½} Γ(ν+½)` — the weight in the Dunkl
transform (Eqs. 22–23) and the plane-wave normalisation (Eq. 31). -/
noncomputable def cNu (ν : ℝ) : ℝ := 2 ^ (ν + 1 / 2) * Real.Gamma (ν + 1 / 2)

/-- `c_ν > 0` for `ν > −½` (the Gamma argument is positive). -/
theorem cNu_pos (ν : ℝ) (hν : -(1 / 2) < ν) : 0 < cNu ν := by
  unfold cNu
  have : 0 < ν + 1 / 2 := by linarith
  positivity

/-! ## §E — positivity of the Dunkl number (the measure bound `ν > −½`) -/

/-- **[Junker Eq. 6 bound] `[n]_ν > 0` for `n ≥ 1`, `ν > −½`.** Even Dunkl numbers are `2m > 0`; odd ones
are `2m+1+2ν > 0` since `2ν > −1`. Hence the Dunkl factorial is nonzero and the kernel coefficients /
eigenfunction are well defined; `ν > −½` is exactly the measure-existence bound of the weighted Hilbert
space `ℋ = L²(ℝ, |x|^{2ν}dx)` (Eq. 6). -/
theorem dunklNumber_pos (ν : ℝ) (n : ℕ) (hn : 1 ≤ n) (hν : -(1 / 2) < ν) : 0 < dunklNumber ν n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m by ring, dunklNumber_even]
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  · rw [dunklNumber_odd]
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith

/-- **The Dunkl factorial is nonzero for `ν > −½`** — every factor `[k]_ν > 0`. -/
theorem dunklFactorial_ne_zero (ν : ℝ) (n : ℕ) (hν : -(1 / 2) < ν) : dunklFactorial ν n ≠ 0 := by
  rw [dunklFactorial, Finset.prod_ne_zero_iff]
  intro k _
  exact (dunklNumber_pos ν (k + 1) (Nat.le_add_left 1 k) hν).ne'

end Physlib.QuantumMechanics.ComplexAction.Dunkl.Kernel

end
