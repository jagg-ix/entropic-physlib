/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard

/-!
# The Kálnay composite fermion: the CAR algebra and Pauli exclusion

Constructs the algebraic content of **A. J. Kálnay's composite fermion** ("On Fermi quantum fields
constructed from Bose quantum fields"): a Fermi field `f` built bilinear in Bose operators, `f ∝ ∫ F(z,x,x′)
b†(x) b(x′)`, with the kernel `F` chosen so that `f` satisfies the **canonical anticommutation relations**
(CAR). The bilinear-in-Bose *construction* (the integral kernel) is the physical origin; this file
formalizes its exact algebraic *destination* — the CAR fermion-mode algebra and its consequences — on a
`*`-ring (`AlgebraicQFT.GNSVonNeumannHadamard`'s `StarRing` of observables).

A **fermion mode** is an element `f` with the CAR

  `{f, f} = 0`  (`f² = 0`),   `{f, f†} = f f† + f† f = 1`   (`IsFermionMode`),

from which the fermion algebra follows exactly:

* the conjugate also squares to zero, `f†² = 0` (`fermionMode_star_sq`);
* the **number operator** `n = f† f` (`fermionNumber`) is self-adjoint `n† = n`
  (`fermionNumber_selfAdjoint`) and **idempotent** `n² = n` (`fermionNumber_idempotent`) — a projection,
  so its spectrum is `{0, 1}`: **Pauli exclusion**;
* `f` **lowers** the number, `[n, f] = −f` (`fermionNumber_lowering`).

So Kálnay's bilinear-in-Bose composite, once it satisfies the CAR, *is* a genuine fermion: a single
occupation `n ∈ {0,1}`, the algebraic core of "a fermion on a region." The composite-from-Bose construction
is the origin (the kernel `F`); the Pauli/number structure here is its exact algebraic content.

* **§A — the fermion mode (CAR)** (`IsFermionMode`, `fermionNumber`, `fermionMode_star_sq`,
  `fermionNumber_selfAdjoint`).
* **§B — Pauli exclusion and lowering** (`fermionNumber_idempotent`, `fermionNumber_lowering`,
  `kalnay_composite_fermion`).

## References

* A. J. Kálnay, "On Fermi quantum fields constructed from Bose quantum fields"; the canonical
  anticommutation relations / Pauli exclusion. structures: `AlgebraicQFT.GNSVonNeumannHadamard` (the `StarRing` of
  observables); cf. `Bogoliubov.FermionicBogoliubovCAR`, `Bogoliubov.ContinuumCAR`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR

variable {A : Type*} [Ring A] [StarRing A]

/-! ## §A — the fermion mode (CAR) -/

/-- **A fermion mode** — an element `f` satisfying the canonical anticommutation relations `{f, f} = 0`
(`f² = 0`) and `{f, f†} = f f† + f† f = 1`. (Kálnay's composite, bilinear in Bose operators, with the kernel
fixed so these hold.) -/
def IsFermionMode (f : A) : Prop :=
  f * f = 0 ∧ f * star f + star f * f = 1

/-- **The fermion number operator** `n = f† f`. -/
def fermionNumber (f : A) : A := star f * f

/-- **[The conjugate squares to zero] `f†² = 0`.** From `f² = 0` and `star(f f) = f† f†`. -/
theorem fermionMode_star_sq (f : A) (h : IsFermionMode f) : star f * star f = 0 := by
  rw [← star_mul, h.1, star_zero]

/-- **[The number operator is self-adjoint] `n† = n`.** `(f† f)† = f† f†† = f† f`. -/
theorem fermionNumber_selfAdjoint (f : A) : star (fermionNumber f) = fermionNumber f := by
  unfold fermionNumber; rw [star_mul, star_star]

/-! ## §B — Pauli exclusion and lowering -/

/-- **[Pauli exclusion: the number operator is idempotent] `n² = n`.** With `f f† = 1 − f† f` (from the CAR)
and `f² = 0`, the fermion number `n = f† f` is a projection — its eigenvalues are `0` and `1`, so a mode is
occupied at most once. -/
theorem fermionNumber_idempotent (f : A) (h : IsFermionMode f) :
    fermionNumber f * fermionNumber f = fermionNumber f := by
  have hff : f * star f = 1 - star f * f := eq_sub_of_add_eq h.2
  unfold fermionNumber
  calc star f * f * (star f * f)
      = star f * (f * star f) * f := by noncomm_ring
    _ = star f * (1 - star f * f) * f := by rw [hff]
    _ = star f * f - star f * star f * (f * f) := by noncomm_ring
    _ = star f * f - star f * star f * 0 := by rw [h.1]
    _ = star f * f := by noncomm_ring

/-- **[The fermion lowers the number] `[n, f] = n f − f n = −f`.** The annihilation operator `f` decreases
the occupation by one. -/
theorem fermionNumber_lowering (f : A) (h : IsFermionMode f) :
    fermionNumber f * f - f * fermionNumber f = -f := by
  have h1 : star f * f * f = 0 := by rw [mul_assoc, h.1, mul_zero]
  have h2 : f * (star f * f) = f := by
    rw [← mul_assoc, eq_sub_of_add_eq h.2]
    have e : (1 - star f * f) * f = f - star f * (f * f) := by noncomm_ring
    rw [e, h.1, mul_zero, sub_zero]
  unfold fermionNumber
  rw [h1, h2, zero_sub]

/-- **[The Kálnay composite fermion, assembled].** A composite mode `f` satisfying the CAR (`f² = 0`,
`{f, f†} = 1`) is a genuine fermion:

* `f†² = 0`;
* the number operator `n = f† f` is self-adjoint and idempotent (`n² = n`) — a projection with spectrum
  `{0, 1}`, **Pauli exclusion**;
* `f` lowers the number, `[n, f] = −f`.

Kálnay's bilinear-in-Bose composite, once it obeys the CAR, includes the full single-occupation fermion
algebra — the algebraic core of a fermion on a region. -/
theorem kalnay_composite_fermion (f : A) (h : IsFermionMode f) :
    star f * star f = 0
      ∧ star (fermionNumber f) = fermionNumber f
      ∧ fermionNumber f * fermionNumber f = fermionNumber f
      ∧ fermionNumber f * f - f * fermionNumber f = -f :=
  ⟨fermionMode_star_sq f h, fermionNumber_selfAdjoint f,
    fermionNumber_idempotent f h, fermionNumber_lowering f h⟩

end Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR

end
