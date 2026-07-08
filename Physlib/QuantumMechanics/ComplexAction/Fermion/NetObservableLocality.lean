/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity

/-!
# The observable (even) fermion net is bosonic-local

Completes the fermion-region picture: although the fermion *fields* in spacelike-separated regions
**anticommute** (`BoseFermiOperatorAlgebra.FermionNetLocality`, graded locality), their **even (gauge-invariant) observables**
— the number operator `n = f† f` and the parity `P = (−1)^N` (`Fermion.SpinStatisticsFermionParity`) — **commute**.
So the *observable* subalgebra of the fermion net satisfies ordinary (bosonic) Haag–Kastler locality, even
though the field net is only graded-local.

For two anticommuting modes `f`, `g` (spacelike-separated regions):

* the number operators commute, `[n_f, n_g] = 0` (`fermionNumbers_commute`, the even bilinears);
* the **parity operators commute**, `[P_f, P_g] = 0` (`fermionParity_commute`), since `[P_f, P_g] =
  4[n_f, n_g] = 0`.

So the even observables of disjoint regions are compatible: the observable net is a bosonic local net
(`fermion_observable_net_locality`), the Haag–Kastler observable algebra of the graded fermion field net.

This is the resolution of the spin-statistics tension at the net level: the fields are odd (anticommuting,
half-integer spin), but the physical observables built from them are even and locally commuting — a genuine
bosonic local net of observables.

* **§A — even observables commute** (`fermionParity_commute`).
* **§B — the observable net is bosonic-local** (`fermion_observable_net_locality`).

## References

* Graded (super-)nets and their even observable subnet (Doplicher–Haag–Roberts, Haag–Kastler). structures:
  `BoseFermiOperatorAlgebra.FermionNetLocality` (`AnticommutingFermionModes`, `fermionNumbers_commute`),
  `Fermion.SpinStatisticsFermionParity` (`fermionParity`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.NetObservableLocality

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality
open Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsFermionParity

variable {A : Type*} [Ring A] [StarRing A]

/-! ## §A — even observables commute -/

/-- **[Parity operators commute] `[P_f, P_g] = 0`.** The even observables `P = (−1)^N` of two
spacelike-separated (anticommuting) fermion modes commute, because `[P_f, P_g] = 4[n_f, n_g] = 0`. -/
theorem fermionParity_commute (f g : A) (h : AnticommutingFermionModes f g) :
    fermionParity f * fermionParity g = fermionParity g * fermionParity f := by
  have hnn : fermionNumber f * fermionNumber g = fermionNumber g * fermionNumber f :=
    fermionNumbers_commute f g h
  unfold fermionParity
  calc (1 - (2 : A) * fermionNumber f) * (1 - (2 : A) * fermionNumber g)
      = 1 - 2 * fermionNumber g - 2 * fermionNumber f
          + 4 * (fermionNumber f * fermionNumber g) := by noncomm_ring
    _ = 1 - 2 * fermionNumber g - 2 * fermionNumber f
          + 4 * (fermionNumber g * fermionNumber f) := by rw [hnn]
    _ = (1 - (2 : A) * fermionNumber g) * (1 - (2 : A) * fermionNumber f) := by noncomm_ring

/-! ## §B — the observable net is bosonic-local -/

/-- **[The observable fermion net is bosonic-local].** For two spacelike-separated fermion modes (whose
fields anticommute), the even observables — the number operators and the parities — all **commute**:

* `[n_f, n_g] = 0`;
* `[P_f, P_g] = 0`.

So the gauge-invariant observable subalgebra of the fermion field net satisfies ordinary (bosonic)
Haag–Kastler locality: the local observables of disjoint regions are compatible, even though the underlying
fermion fields anticommute. -/
theorem fermion_observable_net_locality (f g : A) (h : AnticommutingFermionModes f g) :
    fermionNumber f * fermionNumber g = fermionNumber g * fermionNumber f
      ∧ fermionParity f * fermionParity g = fermionParity g * fermionParity f :=
  ⟨fermionNumbers_commute f g h, fermionParity_commute f g h⟩

end Physlib.QuantumMechanics.ComplexAction.Fermion.NetObservableLocality

end
