/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh

/-!
# One character property: the Verlinde `S`-matrix and the Bogoliubov rapidity

The crux of the discrete convolution theorem `Ŝ(f ⋆ g) = √k · Ŝf · Ŝg`
(`ChernSimons.VerlindeConvolution`) is the **`S`-matrix character property**

  `S_{(a+b)x} = √k · S_{ax} · S_{bx}`   (`cswSMatrix_add_left`),

i.e. the `S`-matrix column `a ↦ S_{ax}` is a **group-like / Hopf character** of the charge lattice `ℤ/k` —
the exponential turns charge *addition* into *multiplication*. The Bogoliubov rapidity (the previous file's
`coth/tanh` arc) rests on the *same* structure: the boost character

  `e^{η₁ + η₂} = e^{η₁} · e^{η₂}`

turns rapidity *addition* (composition of boosts) into multiplication, and `tanh η` (the metric velocity =
fermion occupation factor) is its hyperbolic shadow.

This file makes the parallel a theorem. A **normalized character** is `χ(a+b) = c · χ(a) · χ(b)`:

* `verlinde_S_normalizedCharacter`: the Verlinde `S`-matrix column is a `√k`-normalized character of `ℤ/k`
  (the convolution-theorem crux).
* `rapidity_exp_normalizedCharacter`: the rapidity exponential `η ↦ e^η` is a `1`-normalized character of
  `(ℝ, +)` (the boost group).

So the convolution theorem (Verlinde `S` diagonalizes the charge convolution) and the Bogoliubov composition
(boosts add, velocities `tanh`-compose) are two faces of one group-like/character property — a compact
`ℤ/k` character with `√k` normalization on the Verlinde side, a non-compact `(ℝ,+)` character with `1`
normalization on the rapidity side. The same `e^{·}` that gives the Bose/Fermi `coth`/`tanh`
(`Bogoliubov.RapidityBoseFermiCothTanh`) gives the Verlinde Gauss-sum kernel.

## References

* E. Verlinde (1988); group-like elements / Hopf characters. `Physlib`
  (`ChernSimons.VerlindeConvolution.cswSMatrix_add_left`, `Bogoliubov.RapidityBoseFermiCothTanh`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Rapidity.Basic

/-- **A normalized character** of an additive group: `χ(a + b) = c · χ(a) · χ(b)` — a group-like / Hopf
character with normalization constant `c` (`c = 1` is an honest character; `c ≠ 1` is the cocycle twist). -/
def NormalizedCharacter {G : Type*} [Add G] (c : ℂ) (χ : G → ℂ) : Prop :=
  ∀ a b, χ (a + b) = c * χ a * χ b

/-- **[The Verlinde `S`-matrix column is a `√k`-normalized character]** `S_{(a+b)x} = √k · S_{ax} · S_{bx}`:
the convolution-theorem crux is exactly the group-like / Hopf character property of `ℤ/k`. -/
lemma verlinde_S_normalizedCharacter {k : ℕ} [NeZero k] (x : Fin k) :
    NormalizedCharacter (Real.sqrt k : ℂ) (fun a : Fin k => cswSMatrix k a x) :=
  fun a b => cswSMatrix_add_left (Nat.pos_of_ne_zero (NeZero.ne k)) a b x

/-- **[The rapidity exponential is a `1`-normalized character]** `e^{η₁+η₂} = e^{η₁}·e^{η₂}`: the Bogoliubov
boost character turns rapidity addition (composition of boosts) into multiplication — the same group-like
structure as the Verlinde `S`-matrix, on the non-compact group `(ℝ, +)`. -/
lemma rapidity_exp_normalizedCharacter :
    NormalizedCharacter (1 : ℂ) (fun η : ℝ => Complex.exp (η : ℂ)) := by
  intro a b
  push_cast
  rw [Complex.exp_add]
  ring

end Physlib.QuantumMechanics.ComplexAction.Rapidity.Basic

end
