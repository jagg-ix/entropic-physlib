/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection
public import Physlib.QFT.Lattice.LatticeTopologicalCharge

/-!
# The Levi-Civita dual of the cyclic Bianchi identities

The **cyclic identity** `cyclicSum f a b c = f a b c + f b c a + f c a b = 0` is the single operator
underlying *both* Bianchi identities of the BCJ double copy (`Curvature.SecondBianchiCyclicFamily`,
`Curvature.JacobiRicciBianchiTetrad`, `LeviCivita.BianchiDoubleCopy`): the **first (algebraic) Bianchi**
`R_{a[bcd]} = 0` (cyclic over the last three curvature indices) and the **second (differential) Bianchi**
`R^a_{b[cd;e]} = 0` (cyclic over the two curvature indices and the derivative index) are the two faces of
the same `cyclicSum`, the gravity-side of the kinematic Jacobi `n_s + n_t + n_u = 0`. This module gives
their common **Levi-Civita ε-dual**: contracting the cyclic identity with the 4D volume form annihilates it.

* `leviCivita_contraction_of_cyclic` — the core: for any `T : Fin 4 → … → ℝ` whose cyclic sum over its
  last three indices vanishes (`∀ a b c d, T a b c d + T a c d b + T a d b c = 0` — the `cyclicSum`),
  the totally-antisymmetric contraction `∑_{abcd} ε_{abcd} T_{abcd} = 0`. No antisymmetry is assumed: the
  mechanism is `S = −2S ⇒ 3S = 0` (each of the three cyclic terms reindexes to the same contraction, the
  Levi-Civita symbol being cyclic-even on the last three slots).
* `riemann_leviCivita_contraction_eq_zero` — the **first-Bianchi face**: `∑_{abcd} ε_{abcd} R_{abcd} = 0`
  for a Riemann tensor (`IsRiemannCurvature.bianchi` is exactly the required cyclic sum). The curvature
  2-form carries no totally-antisymmetric (top-form) component.
* `secondBianchi_leviCivita_contraction` — the **second-Bianchi face**, the leverage of the same lemma:
  for `D` satisfying `SecondBianchi` (`R^a_{b[cd;e]} = 0`), `∀ a, ∑_{bcde} ε_{bcde} D_{abcde} = 0` — the
  **Levi-Civita/dual second Bianchi** `ε^{bcde} ∇_e R^a_{bcd} = 0`, the divergence of the dual curvature.
  It is the second Bianchi read on the volume form, and (with the Einstein equation) the ε-dual route to
  the contracted-Bianchi conservation `∇^μ G_{μν} = 0` handled in `BCJDoubleCopy.SecondBianchiConservation`.

The linear ε-contraction here should not be confused with the *quadratic* Pontryagin density
`ε^{abcd} R_{ab}{}^{ef} R_{cdef}` (`Curvature.GaussBonnetPontryaginSelfDual`).

## Honest scope

This is the algebraic core of Sanchez's "by the cyclic identity" step (1984): the cyclic Bianchi identity
has no bulk ε-component. It is *not* the full `★R = R ⇒ R_{μν} = 0`: as a Ricci contraction alone that is
tautological, and the real proof runs through the `Λ²` curvature-**operator** `★`-eigenspace block
decomposition (self-duality killing the off-diagonal trace-free-Ricci and `∧²₋` scalar blocks), which
physlib does not yet carry — the abstract `★`-split/Bogomolny bound is in
`AlgebraicQFT.SelfDualQuaternionYangMills`, the Ricci **linear** operator in
`Curvature.RiemannCurvatureOperator`, the density Bogomolny bound in
`Curvature.GaussBonnetPontryaginSelfDual`. Cited, not formalized.

## References

* N. Sanchez, *Connection between the self-dual Yang–Mills and general relativity Einstein equations*,
  Phys. Lett. **144B** (1984) 217–220 (Introduction eq. (1)/(2): the cyclic-identity reduction of the
  self-dual Einstein equations).
* Carriers: `Curvature.RiemannCurvatureTensor` (`IsRiemannCurvature`), `Curvature.SecondBianchiCyclicFamily`
  (`SecondBianchi`, `cyclicSum`), `QFT.Lattice.LatticeTopologicalCharge` (`leviCivita4`, the 4D volume
  form `ε_{μνρσ}`).
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily
open Physlib.QFT.Lattice.LatticeTopologicalCharge

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannLeviCivitaContraction

set_option maxHeartbeats 8000000 in
/-- **The cyclic identity's Levi-Civita dual**: if the cyclic sum of `T` over its last three indices
vanishes (`∀ a b c d, T a b c d + T a c d b + T a d b c = 0`), then the totally-antisymmetric contraction
with the 4D volume form vanishes, `∑_{abcd} ε_{abcd} T_{abcd} = 0`. No antisymmetry of `T` is used: `ε` is
cyclic-even on the last three slots, so each of the three cyclic terms reindexes to the same contraction
(`S = −2S ⇒ 3S = 0`). Both Bianchi faces of the double copy are instances (`riemann_leviCivita_...`,
`secondBianchi_leviCivita_...`). -/
theorem leviCivita_contraction_of_cyclic (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ a b c d, T a b c d + T a c d b + T a d b c = 0) :
    ∑ a, ∑ b, ∑ c, ∑ d, ((leviCivita4 a b c d : ℤ) : ℝ) * T a b c d = 0 := by
  simp only [Fin.sum_univ_four, leviCivita4]
  push_cast
  linarith [h 0 1 2 3, h 0 1 3 2, h 0 2 1 3, h 0 3 1 2, h 0 2 3 1, h 0 3 2 1,
    h 1 0 2 3, h 1 0 3 2, h 1 2 0 3, h 1 3 0 2, h 1 2 3 0, h 1 3 2 0,
    h 2 0 1 3, h 2 0 3 1, h 2 1 0 3, h 2 3 0 1, h 2 1 3 0, h 2 3 1 0,
    h 3 0 1 2, h 3 0 2 1, h 3 1 0 2, h 3 2 0 1, h 3 1 2 0, h 3 2 1 0]

/-- **First-Bianchi face**: `∑_{abcd} ε_{abcd} R_{abcd} = 0` for a Riemann tensor. The algebraic Bianchi
identity (`IsRiemannCurvature.bianchi`, the gravity-side kinematic Jacobi) is exactly the cyclic sum this
requires — the curvature 2-form has no totally-antisymmetric (top-form) component. This is the algebraic
content of Sanchez's "by the cyclic identity" step. -/
theorem riemann_leviCivita_contraction_eq_zero {Rm : RiemannTensor (Fin 4)}
    (h : IsRiemannCurvature Rm) :
    ∑ a, ∑ b, ∑ c, ∑ d, ((leviCivita4 a b c d : ℤ) : ℝ) * Rm a b c d = 0 :=
  leviCivita_contraction_of_cyclic Rm h.bianchi

/-- **Second-Bianchi face** (the leverage of `leviCivita_contraction_of_cyclic` for the *second* Bianchi):
for `D` satisfying the differential Bianchi identity `SecondBianchi D` (`R^a_{b[cd;e]} = 0`, the cyclic sum
over the two curvature indices and the derivative index), the Levi-Civita contraction over those slots
vanishes for every `a`, `∑_{bcde} ε_{bcde} D_{abcde} = 0`. This is the **dual second Bianchi**
`ε^{bcde} ∇_e R^a_{bcd} = 0` — the second Bianchi identity read on the volume form; the `∇·(★R)` face of
the same cyclic operator whose contracted form gives `∇^μ G_{μν} = 0`
(`BCJDoubleCopy.SecondBianchiConservation`). -/
theorem secondBianchi_leviCivita_contraction
    {D : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ} (hSB : SecondBianchi D) (a : Fin 4) :
    ∑ b, ∑ c, ∑ d, ∑ e, ((leviCivita4 b c d e : ℤ) : ℝ) * D a b c d e = 0 :=
  leviCivita_contraction_of_cyclic (fun b c d e => D a b c d e) (fun b c d e => hSB a b c d e)

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannLeviCivitaContraction
