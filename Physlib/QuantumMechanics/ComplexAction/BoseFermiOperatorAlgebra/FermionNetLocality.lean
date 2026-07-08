/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR

/-!
# Fermion-net locality: anticommuting modes have independent occupation

Completes the fermion-region picture of `BoseFermiOperatorAlgebra.CompositeFermionCAR` (a single Kálnay composite fermion mode
= Pauli exclusion) with the **two-mode / net locality**: two fermion modes localized in spacelike-separated
regions **anticommute**, and the algebraic consequence is that their **number operators commute** — the
occupations are independent. This is the algebraic core of the fermion net's (graded) locality: disjoint
regions encode independent fermionic degrees of freedom.

Two `AnticommutingFermionModes` `f`, `g` satisfy the cross-CAR

  `{f, g} = 0`,  `{f, g†} = 0`   (`AnticommutingFermionModes`),

from which (taking adjoints) `{f†, g} = 0` and `{f†, g†} = 0` (`fermionNet_cross_anticomm`), so the number
operator `n_f = f† f` commutes with `g` and `g†` (`fermionNumber_commute_field`,
`fermionNumber_commute_field_star`), hence with `n_g = g† g`:

  `[n_f, n_g] = 0`   (`fermionNumbers_commute`).

So spacelike-separated fermion modes have commuting occupation numbers: the local number observables of
disjoint regions are compatible — fermion-net locality at the algebraic level
(`kalnay_fermion_net_locality`). Together with the single-mode Pauli exclusion (`fermionNumber_idempotent`),
this is the full occupation structure of a fermion field on a region net: each mode occupied at most once,
disjoint modes independent.

* **§A — the anticommuting modes and the cross-anticommutators** (`AnticommutingFermionModes`,
  `fermionNet_cross_anticomm`).
* **§B — number operators commute (locality)** (`fermionNumber_commute_field`,
  `fermionNumber_commute_field_star`, `fermionNumbers_commute`, `kalnay_fermion_net_locality`).

## References

* Canonical anticommutation relations / fermion nets (Araki, Haag–Kastler graded locality). structure:
  `BoseFermiOperatorAlgebra.CompositeFermionCAR` (`IsFermionMode`, `fermionNumber`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR

variable {A : Type*} [Ring A] [StarRing A]

/-! ## §A — anticommuting modes and the cross-anticommutators -/

/-- **Two anticommuting fermion modes** — `f`, `g` are each fermion modes and anticommute,
`{f, g} = 0` and `{f, g†} = 0` (the cross-CAR of fields localized in spacelike-separated regions). -/
def AnticommutingFermionModes (f g : A) : Prop :=
  IsFermionMode f ∧ IsFermionMode g ∧ f * g + g * f = 0 ∧ f * star g + star g * f = 0

/-- **[The conjugate cross-anticommutator] `{f†, g} = 0`.** Taking the adjoint of `{f, g†} = 0`. -/
theorem fermionNet_starf_g (f g : A) (h : AnticommutingFermionModes f g) :
    star f * g + g * star f = 0 := by
  have hs := congrArg star h.2.2.2
  simp only [star_add, star_mul, star_star, star_zero] at hs
  rw [add_comm]; exact hs

/-- **[The conjugate cross-anticommutator] `{f†, g†} = 0`.** Taking the adjoint of `{f, g} = 0`. -/
theorem fermionNet_starf_starg (f g : A) (h : AnticommutingFermionModes f g) :
    star f * star g + star g * star f = 0 := by
  have hs := congrArg star h.2.2.1
  simp only [star_add, star_mul, star_star, star_zero] at hs
  rw [add_comm]; exact hs

/-! ## §B — number operators commute (locality) -/

/-- **[The number operator commutes with the other field] `n_f g = g n_f`.** Since `f`, `f†` anticommute
with `g`, the number operator `n_f = f† f` commutes with `g`. -/
theorem fermionNumber_commute_field (f g : A) (h : AnticommutingFermionModes f g) :
    fermionNumber f * g = g * fermionNumber f := by
  have hfg : f * g = -(g * f) := eq_neg_of_add_eq_zero_left h.2.2.1
  have hf'g : star f * g = -(g * star f) := eq_neg_of_add_eq_zero_left (fermionNet_starf_g f g h)
  unfold fermionNumber
  calc star f * f * g = star f * (f * g) := by noncomm_ring
    _ = star f * -(g * f) := by rw [hfg]
    _ = -(star f * g * f) := by noncomm_ring
    _ = -(-(g * star f) * f) := by rw [hf'g]
    _ = g * (star f * f) := by noncomm_ring

/-- **[The number operator commutes with the other field's adjoint] `n_f g† = g† n_f`.** -/
theorem fermionNumber_commute_field_star (f g : A) (h : AnticommutingFermionModes f g) :
    fermionNumber f * star g = star g * fermionNumber f := by
  have hfg' : f * star g = -(star g * f) := eq_neg_of_add_eq_zero_left h.2.2.2
  have hf'g' : star f * star g = -(star g * star f) :=
    eq_neg_of_add_eq_zero_left (fermionNet_starf_starg f g h)
  unfold fermionNumber
  calc star f * f * star g = star f * (f * star g) := by noncomm_ring
    _ = star f * -(star g * f) := by rw [hfg']
    _ = -(star f * star g * f) := by noncomm_ring
    _ = -(-(star g * star f) * f) := by rw [hf'g']
    _ = star g * (star f * f) := by noncomm_ring

/-- **[Fermion-net locality: number operators commute] `[n_f, n_g] = 0`.** The occupation numbers of two
spacelike-separated (anticommuting) fermion modes commute — the local number observables of disjoint regions
are compatible. -/
theorem fermionNumbers_commute (f g : A) (h : AnticommutingFermionModes f g) :
    fermionNumber f * fermionNumber g = fermionNumber g * fermionNumber f := by
  have hg : fermionNumber f * g = g * fermionNumber f := fermionNumber_commute_field f g h
  have hg' : fermionNumber f * star g = star g * fermionNumber f :=
    fermionNumber_commute_field_star f g h
  show fermionNumber f * (star g * g) = star g * g * fermionNumber f
  calc fermionNumber f * (star g * g) = (fermionNumber f * star g) * g := by noncomm_ring
    _ = (star g * fermionNumber f) * g := by rw [hg']
    _ = star g * (fermionNumber f * g) := by noncomm_ring
    _ = star g * (g * fermionNumber f) := by rw [hg]
    _ = star g * g * fermionNumber f := by noncomm_ring

/-- **[Fermion-net locality, assembled].** For two spacelike-separated fermion modes `f`, `g`
(`AnticommutingFermionModes`):

* the cross-anticommutators close, `{f†, g} = 0`, `{f†, g†} = 0`;
* the number operator `n_f` commutes with `g`, `g†`, and `n_g`;
* hence `[n_f, n_g] = 0` — the occupations are independent.

With single-mode Pauli exclusion (`fermionNumber_idempotent`), this is the full fermion-net occupation
structure: each mode occupied at most once, disjoint-region modes independent. -/
theorem kalnay_fermion_net_locality (f g : A) (h : AnticommutingFermionModes f g) :
    star f * g + g * star f = 0
      ∧ star f * star g + star g * star f = 0
      ∧ fermionNumber f * g = g * fermionNumber f
      ∧ fermionNumber f * fermionNumber g = fermionNumber g * fermionNumber f :=
  ⟨fermionNet_starf_g f g h, fermionNet_starf_starg f g h,
    fermionNumber_commute_field f g h, fermionNumbers_commute f g h⟩

end Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality

end
