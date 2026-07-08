/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
public import Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover

/-!
# Spin-statistics: the 2π-rotation sign is the fermionic parity

Bridges the **spin-½ SU(2) double cover** (`Hopf.SpinHalfDoubleCover`, a spinor picks up `−1` under a `2π`
rotation, `spinRotation_two_pi`) to the **fermionic parity** of the Kálnay composite fermion
(`BoseFermiOperatorAlgebra.CompositeFermionCAR`). The spin-statistics theorem identifies the two minus signs: the `−1` a
half-integer-spin object acquires under a `2π` rotation is the `−1` of fermionic exchange.

The fermionic **parity operator** `P = (−1)^N = 1 − 2n` (`fermionParity`, `n = f† f`) is the ℤ₂ grading of
the fermion algebra: it is an **involution** `P² = 1` (`fermionParity_involution`, from `n² = n`), and it
**anticommutes** with the annihilation operator `P f = −f P` (`fermionParity_anticommutes`) — because `f`
flips the occupation parity. This `−1` (the grading sign) is the same involutive `−1` as the spin-½ `2π`
rotation `R(2π) = −1`:

  `spinRotation G (2π) = −1`   and   `P² = 1`, `P f = −f P`   (`spin_statistics_connection`).

So a half-integer-spin object's double-cover sign (the spinor `−1` under `2π`) and the fermion's
exchange/grading sign (the parity `−1`) are one and the same — the algebraic content of the spin-statistics
connection: half-integer spin ⟺ Fermi statistics.

* **§A — the fermionic parity operator** (`fermionParity`, `fermionParity_involution`,
  `fermionParity_anticommutes`).
* **§B — the spin-statistics connection** (`spin_statistics_connection`).

## References

* The spin-statistics theorem; the fermion parity `(−1)^F` / ℤ₂ grading. structures:
  `Hopf.SpinHalfDoubleCover` (`spinRotation`, `spinRotation_two_pi`), `BoseFermiOperatorAlgebra.CompositeFermionCAR`
  (`IsFermionMode`, `fermionNumber`, `fermionNumber_idempotent`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover

variable {A : Type*} [Ring A] [StarRing A]

/-! ## §A — the fermionic parity operator `P = (−1)^N = 1 − 2n` -/

/-- **The fermionic parity operator** `P = (−1)^N = 1 − 2n` (`n = f† f`) — the ℤ₂ grading of the fermion
algebra: `+1` on the empty mode, `−1` on the occupied mode. -/
def fermionParity (f : A) : A := 1 - (2 : A) * fermionNumber f

/-- **[Parity is an involution] `P² = 1`.** From `n² = n` (Pauli idempotence), `(1 − 2n)² = 1 − 4n + 4n² =
1`. The grading squares to the identity. -/
theorem fermionParity_involution (f : A) (h : IsFermionMode f) :
    fermionParity f * fermionParity f = 1 := by
  have hn : fermionNumber f * fermionNumber f = fermionNumber f := fermionNumber_idempotent f h
  unfold fermionParity
  calc (1 - (2 : A) * fermionNumber f) * (1 - (2 : A) * fermionNumber f)
      = 1 - 4 * fermionNumber f + 4 * (fermionNumber f * fermionNumber f) := by noncomm_ring
    _ = 1 - 4 * fermionNumber f + 4 * fermionNumber f := by rw [hn]
    _ = 1 := by noncomm_ring

/-- **[Parity anticommutes with the field] `P f = −f P`.** The annihilation operator flips the occupation
parity, so it anticommutes with the grading `P` — the fermionic `−1` of exchange. -/
theorem fermionParity_anticommutes (f : A) (h : IsFermionMode f) :
    fermionParity f * f = -(f * fermionParity f) := by
  have hnf : fermionNumber f * f = 0 := by
    unfold fermionNumber; rw [mul_assoc, h.1, mul_zero]
  have hfn : f * fermionNumber f = f := by
    unfold fermionNumber
    rw [← mul_assoc, eq_sub_of_add_eq h.2]
    have e : (1 - star f * f) * f = f - star f * (f * f) := by noncomm_ring
    rw [e, h.1, mul_zero, sub_zero]
  unfold fermionParity
  have hL : (1 - (2 : A) * fermionNumber f) * f = f := by
    rw [show (1 - (2 : A) * fermionNumber f) * f = f - 2 * (fermionNumber f * f) from by noncomm_ring,
      hnf]; noncomm_ring
  have hR : f * (1 - (2 : A) * fermionNumber f) = -f := by
    rw [show f * (1 - (2 : A) * fermionNumber f) = f - 2 * (f * fermionNumber f) from by noncomm_ring,
      hfn]; noncomm_ring
  rw [hL, hR, neg_neg]

/-! ## §B — the spin-statistics connection -/

/-- **[Spin-statistics: the 2π-rotation sign is the fermionic parity].** For a spin-½ generator `G` and a
fermion mode `f`:

* a `2π` rotation of the spinor is `−1` (the SU(2) double cover), `spinRotation G (2π) = −1`;
* the fermionic parity `P = (−1)^N` is an involution `P² = 1` that anticommutes with the field,
  `P f = −f P`.

These two `−1`'s are the same involutive grading sign: the spinor `−1` under a `2π` rotation and the
fermionic exchange/parity `−1` coincide — half-integer spin ⟺ Fermi statistics. -/
theorem spin_statistics_connection (G : Matrix (Fin 2) (Fin 2) ℂ) (f : A) (h : IsFermionMode f) :
    spinRotation G (2 * Real.pi) = -1
      ∧ fermionParity f * fermionParity f = 1
      ∧ fermionParity f * f = -(f * fermionParity f) :=
  ⟨spinRotation_two_pi G, fermionParity_involution f h, fermionParity_anticommutes f h⟩

end Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity

end
