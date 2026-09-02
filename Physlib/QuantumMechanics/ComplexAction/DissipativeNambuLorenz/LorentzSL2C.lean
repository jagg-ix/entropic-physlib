/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzLorentzSO3
public import Mathlib.Data.Complex.Basic

/-!
# A. `so(1,3)_ℂ ≅ sl(2,ℂ) ⊕ sl(2,ℂ)`: the two `3`-spaces joined by `i` as `ℂ`-matrices

`DissipativeNambuLorenz.LorenzLorentzSO3` showed the Lorenz/Euler induced `so(3)` is the rotation subalgebra of
`so(1,3)`, with the boost copy joined to it by the imaginary unit — recorded there only structurally (the `−`
sign of `[K,K] = −εJ`). This file makes that join concrete: complexifying the generators
(`Jc = J.map ℝ→ℂ`, `Kc = K.map ℝ→ℂ`) and forming the **self-dual / anti-self-dual** combinations

  `N±_i = ½(J_i ± i K_i)`,

the complexified Lorentz algebra splits as **two commuting copies of `sl(2,ℂ)`**:

* `Np_selfDual`: `[N⁺_i, N⁺_j] = Σₖ ε_{ijk} N⁺_k` — the first `sl(2,ℂ)`.
* `Nm_antiSelfDual`: `[N⁻_i, N⁻_j] = Σₖ ε_{ijk} N⁻_k` — the second `sl(2,ℂ)`.
* `Np_Nm_commute`: `[N⁺_i, N⁻_j] = 0` — the two copies commute.

So `so(1,3)_ℂ ≅ sl(2,ℂ) ⊕ sl(2,ℂ)`: the "two 3D slices" (rotation + boost 3-spaces) are exactly the two
`sl(2,ℂ)` factors, **joined by the contour's `i`** — the `i²=−1` of `[K,K]=−εJ` is what makes `N±` close.
This is the Lie-algebra heart of the spinor double cover `SL(2,ℂ) → SO(1,3)` (`Hopf.SL2CDoubleCover`).
`Np_add_Nm`/`Np_sub_Nm` recover the real generators: `N⁺ + N⁻ = Jc`, `N⁺ − N⁻ = i Kc`.

## A.1. References

* Weinberg, *QFT* Vol. 1 §2.4 (`J±iK`, `sl(2,ℂ)⊕sl(2,ℂ)`); group-like spinor double cover. `Physlib`
  (`DissipativeNambuLorenz.LorenzLorentzSO3`, `Hopf.SL2CDoubleCover`).


-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix
open lorentzAlgebra
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzLorentzSO3

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorentzSL2C

/-- **Complexified rotation generator** `Jc_i = J_i ⊗ ℂ`. -/
noncomputable def Jc (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (rotationGenerator i).map Complex.ofReal

/-- **Complexified boost generator** `Kc_i = K_i ⊗ ℂ`. -/
noncomputable def Kc (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (boostGenerator i).map Complex.ofReal

/-- **The self-dual generator** `N⁺_i = ½(J_i + i K_i)` — basis of the first `sl(2,ℂ)`. -/
noncomputable def Np (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (1 / 2 : ℂ) • (Jc i + Complex.I • Kc i)

/-- **The anti-self-dual generator** `N⁻_i = ½(J_i − i K_i)` — basis of the second `sl(2,ℂ)`. -/
noncomputable def Nm (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (1 / 2 : ℂ) • (Jc i - Complex.I • Kc i)

/-! ## A.2. The two commuting `sl(2,ℂ)` copies -/

/-- **[First `sl(2,ℂ)`]** `[N⁺_i, N⁺_j] = Σₖ ε_{ijk} N⁺_k`: the self-dual generators close into an `sl(2,ℂ)`
with the `so(3)` structure constants. -/
lemma Np_selfDual (i j : Fin 3) :
    Np i * Np j - Np j * Np i = ∑ k, (leviCivita3 i j k : ℂ) • Np k := by
  fin_cases i <;> fin_cases j <;>
    (ext μ ν; fin_cases μ <;> fin_cases ν <;>
      simp [Np, Jc, Kc, rotationGenerator, boostGenerator, Matrix.mul_apply, leviCivita3,
        Fin.sum_univ_three, Complex.ext_iff] <;> ring)

/-- **[Second `sl(2,ℂ)`]** `[N⁻_i, N⁻_j] = Σₖ ε_{ijk} N⁻_k`: the anti-self-dual generators close into the
second `sl(2,ℂ)` with the same structure constants. -/
lemma Nm_antiSelfDual (i j : Fin 3) :
    Nm i * Nm j - Nm j * Nm i = ∑ k, (leviCivita3 i j k : ℂ) • Nm k := by
  fin_cases i <;> fin_cases j <;>
    (ext μ ν; fin_cases μ <;> fin_cases ν <;>
      simp [Nm, Jc, Kc, rotationGenerator, boostGenerator, Matrix.mul_apply, leviCivita3,
        Fin.sum_univ_three, Complex.ext_iff] <;> ring)

/-- **[The two copies commute]** `[N⁺_i, N⁻_j] = 0`: the self-dual and anti-self-dual `sl(2,ℂ)` factors are
independent — `so(1,3)_ℂ` is their direct sum. -/
lemma Np_Nm_commute (i j : Fin 3) :
    Np i * Nm j - Nm j * Np i = 0 := by
  fin_cases i <;> fin_cases j <;>
    (ext μ ν; fin_cases μ <;> fin_cases ν <;>
      simp [Np, Nm, Jc, Kc, rotationGenerator, boostGenerator, Matrix.mul_apply,
        Fin.sum_univ_three, Complex.ext_iff])

/-! ## A.3. Recovering the real generators -/

/-- **[`N⁺ + N⁻ = Jc`]** the two `sl(2,ℂ)` halves sum to the (complexified) rotation generator. -/
lemma Np_add_Nm (i : Fin 3) : Np i + Nm i = Jc i := by
  ext μ ν
  simp [Np, Nm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
  ring

/-- **[`N⁺ − N⁻ = i·Kc`]** their difference is `i` times the (complexified) boost generator — the imaginary
unit that joins the two `3`-spaces. -/
lemma Np_sub_Nm (i : Fin 3) : Np i - Nm i = Complex.I • Kc i := by
  ext μ ν
  simp [Np, Nm, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply]
  ring

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorentzSL2C

end
