/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu
public import Physlib.Relativity.LorentzAlgebra.Basis

/-!
# The Lorenz/Euler-top induced `so(3)` is the rotation subalgebra of `so(1,3)`

A 4D Lorentzian spacetime has Lorentz algebra `so(1,3)`, six-dimensional, with the standard basis
(`Physlib.Relativity.LorentzAlgebra.Basis`) indexed `Fin 2 × Fin 3` — **three rotation generators `J_i`**
and **three boost generators `K_i`**. This file records the structural fact that the **rotation copy** is
exactly the `so(3)` encoded in the Axenides–Floratos / Euler-top induced Poisson algebra of the Nambu flow
(JHEP 04 (2010) 036, Eqs. 2.49–2.55), and that the **boost copy** is the second 3-space, joined to the first
by the imaginary unit of the complex-action contour (`J_i ± i K_i`).

The Euler free top (Eq. 2.49) has `H₂ = ½(l₁²+l₂²+l₃²)` (the angular-momentum Casimir), so `∇H₂ = l` (the
point itself), and the induced Poisson algebra (Eq. 2.54) is `{l_i, l_j}_{H₂} = ε_{ijk} l_k` — the `so(3)`
structure constants. That is the **undeformed** version of the Lorenz induced Poisson bracket
`{x,y}_{H₂}=σ, {y,z}=−x, {z,x}=0` (`DissipativeNambuLorenz.LorenzNambu`, Eq. 3.25): the Lorenz dissipation `∇D`
breaks the clean `so(3)`.

* **§A — Euler-top induced `so(3)`.** With `∇H₂ = l`, `{l_i, l_j}_{H₂} = nambuBracket eᵢ eⱼ l = Σₖ ε_{ijk} lₖ`
 (`euler_poisson_xy/yz/zx`) — the same `ε_{ijk}` as `so(3)`.
* **§B — the `so(1,3)` rotation subalgebra is `so(3)`.** `rotation_so3`: `[J_i, J_j] = Σₖ ε_{ijk} J_k`
 (matrix commutator). Same structure constants `ε_{ijk}` as §A: the rotation generators realize the
 Euler/Lorenz induced Poisson algebra.
* **§C — the boost copy and the `i` that joins the two 3-spaces.** `boost_close_rotation`:
 `[K_i, K_j] = −Σₖ ε_{ijk} J_k` (boosts are **not** a subalgebra — they close into rotations with a *minus*
 sign); `rotation_boost_vector`: `[J_i, K_j] = Σₖ ε_{ijk} K_k` (boosts transform as a 3-vector). The minus
 sign is exactly the `i² = −1` that makes the complex combinations `N±_i = ½(J_i ± i K_i)` close into two
 commuting `sl(2,ℂ)` copies — the spinor double cover `SL(2,ℂ) → SO(1,3)` (`Hopf.SL2CDoubleCover`). So the
 "two 3D slices connected by `i`" are the rotation and boost 3-spaces joined by the contour's imaginary unit.

What is proved: the Euler induced `so(3)` (§A), the matrix `so(1,3)` commutators
(§B, §C) sharing `ε_{ijk}`. What is *not* a theorem: the 4D `ℝ³` here is the angular-momentum / Fourier-mode
phase space, not a spacetime metric; the `N±` complexification is recorded structurally (the `−` sign of §C),
not built as `ℂ`-matrices; and the count "6 = 2×3" is the *generators* of `so(1,3)`, not the Lorenz fixed
points (which is a cardinality coincidence, not a map).

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, Eqs. 2.49–2.55 (Euler top, induced `so(3)`). Weinberg, *QFT*
 Vol. 1 §2.4 (`so(1,3)` commutators, `J±iK`). `Physlib` (`DissipativeNambuLorenz.DissipativeNambu`,
 `Relativity.LorentzAlgebra.Basis`, `Hopf.SL2CDoubleCover`).

No additional assumptions.
-/

set_option autoImplicit false

open Matrix
open lorentzAlgebra
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzLorentzSO3

/-- **The `Fin 3` Levi-Civita symbol** `ε_{ijk}` — the `so(3)` structure constants shared by the Euler-top
induced Poisson algebra (§A) and the `so(1,3)` rotation subalgebra (§B). -/
def leviCivita3 (i j k : Fin 3) : ℝ :=
  if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (2, 0, 1) then 1
  else if (i, j, k) = (0, 2, 1) ∨ (i, j, k) = (2, 1, 0) ∨ (i, j, k) = (1, 0, 2) then -1
  else 0

/-! ## §A — the Euler-top induced Poisson algebra is `so(3)` (Eqs. 2.49–2.55)

With the Casimir `H₂ = ½|l|²` the gradient `∇H₂ = l` is the point itself, and the induced Poisson bracket of
two coordinate functions is `{l_i, l_j}_{H₂} = nambuBracket eᵢ eⱼ l`. -/

/-- **[`{l₁,l₂}_{H₂} = ε₁₂ₖ lₖ = l₃`]** the `(x,y)` induced Poisson bracket of the Euler top. -/
theorem euler_poisson_xy (l : Fin 3 → ℝ) :
    nambuBracket ![1, 0, 0] ![0, 1, 0] l = ∑ k, leviCivita3 0 1 k * l k := by
  simp [nambuBracket, cross_apply, leviCivita3]

/-- **[`{l₂,l₃}_{H₂} = ε₂₃ₖ lₖ = l₁`]** the `(y,z)` induced Poisson bracket of the Euler top. -/
theorem euler_poisson_yz (l : Fin 3 → ℝ) :
    nambuBracket ![0, 1, 0] ![0, 0, 1] l = ∑ k, leviCivita3 1 2 k * l k := by
  simp [nambuBracket, cross_apply, leviCivita3]

/-- **[`{l₃,l₁}_{H₂} = ε₃₁ₖ lₖ = l₂`]** the `(z,x)` induced Poisson bracket of the Euler top. -/
theorem euler_poisson_zx (l : Fin 3 → ℝ) :
    nambuBracket ![0, 0, 1] ![1, 0, 0] l = ∑ k, leviCivita3 2 0 k * l k := by
  simp [nambuBracket, cross_apply, leviCivita3]

/-! ## §B — the `so(1,3)` rotation subalgebra realizes the same `so(3)` -/

/-- **[The rotation generators close into `so(3)`]** `[J_i, J_j] = Σₖ ε_{ijk} J_k` — the spatial rotation
generators of `so(1,3)` encode exactly the `ε_{ijk}` structure constants of the Euler/Lorenz induced Poisson
algebra (§A): the **rotation copy of `so(1,3)` is the Lorenz/Euler induced `so(3)`**. -/
theorem rotation_so3 (i j : Fin 3) :
    rotationGenerator i * rotationGenerator j - rotationGenerator j * rotationGenerator i
      = ∑ k, leviCivita3 i j k • rotationGenerator k := by
  fin_cases i <;> fin_cases j <;>
    (ext μ ν; fin_cases μ <;> fin_cases ν <;>
      simp [rotationGenerator, Matrix.mul_apply, leviCivita3])

/-! ## §C — the boost copy and the imaginary unit that joins the two 3-spaces -/

/-- **[Boosts close into rotations with a minus sign]** `[K_i, K_j] = −Σₖ ε_{ijk} J_k`: the three boost
generators are **not** a subalgebra — their commutator lands in the rotation 3-space with a *negative*
structure constant. This minus sign is the `i² = −1` that makes `N±_i = ½(J_i ± i K_i)` close into two
commuting `sl(2,ℂ)` copies (the spinor double cover). -/
theorem boost_close_rotation (i j : Fin 3) :
    boostGenerator i * boostGenerator j - boostGenerator j * boostGenerator i
      = ∑ k, (-leviCivita3 i j k) • rotationGenerator k := by
  fin_cases i <;> fin_cases j <;>
    (ext μ ν; fin_cases μ <;> fin_cases ν <;>
      simp [boostGenerator, rotationGenerator, Matrix.mul_apply, leviCivita3])

/-- **[Boosts transform as a 3-vector under rotations]** `[J_i, K_j] = Σₖ ε_{ijk} K_k`: the rotation
generators act on the boost 3-space exactly as `so(3)` acts on a vector — the boost copy is the spin-1
representation of the rotation `so(3)`, the second of the "two 3-spaces." -/
theorem rotation_boost_vector (i j : Fin 3) :
    rotationGenerator i * boostGenerator j - boostGenerator j * rotationGenerator i
      = ∑ k, leviCivita3 i j k • boostGenerator k := by
  fin_cases i <;> fin_cases j <;>
    (ext μ ν; fin_cases μ <;> fin_cases ν <;>
      simp [boostGenerator, rotationGenerator, Matrix.mul_apply, leviCivita3])

/-! ## §D — the bridge: same structure constants

`rotation_so3` (§B) and `euler_poisson_xy/yz/zx` (§A) both equal the `Σₖ ε_{ijk} (·)ₖ` contraction with the
*same* `leviCivita3`. The map `eᵢ ↦ J_i` therefore includes the Euler/Lorenz induced Poisson `so(3)` to the
`so(1,3)` rotation subalgebra. The following records the shared structure constants on the canonical cyclic
generator. -/

/-- **[Shared structure constant]** the `(0,1)` structure constant is `+1` on the third generator in *both*
the Euler induced Poisson algebra (`euler_poisson_xy`, coefficient of `l₃`) and the `so(1,3)` rotation
commutator (`rotation_so3`, coefficient of `J₃`): `ε₀₁₂ = 1`. The Lorenz/Euler induced `so(3)` and the
Lorentz rotation subalgebra are the same Lie algebra. -/
theorem shared_structure_constant : leviCivita3 0 1 2 = 1 := by
  simp [leviCivita3]

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzLorentzSO3

end
