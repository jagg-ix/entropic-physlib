/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Algebra.AlmostCommutative
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ModularRepresentation
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenFermionPathIntegralsTopologicalPhases
public import Mathlib.Tactic

/-!
# Bott periodicity from almost commuting matrices

This module records the finite algebraic spine of Rufus Willett,
*Bott periodicity and almost commuting matrices* (2019), in the part that can be
connected to existing Physlib infrastructure without introducing a full
`C*`-algebraic `K`-theory API.

* **§A — Bott suspended projection formula.**  The class-level map
  `β_A([p]) = [z^{-1}p + (1-p)]` is represented algebraically by
  `bottSuspendedProjectionUnitary`; functoriality is the ordinary
  `AlgHom.map_*` identity.
* **§B — Loring element.**  The `2 × 2` Loring matrix
  `[[f, g+hv], [v*h+g, 1-f]]` is formalized directly.  Under the finite
  algebraic relations `f^2+g^2+h^2=f`, `gh=0`, and `v* v=1`, it is an
  idempotent.  This is the exact algebraic content behind the projection
  `χ(e(u,v))` when the two unitaries commute.
* **§C — almost commuting clock-shift pairs.**  The Weyl relation
  `UV = qVU` gives the exact commutator defect.  The ordinary commutator is
  not duplicated: it is the `ρ ≡ 1` specialization of
  `AlmostCommutative.rhoCommutator`.
* **§D — links into the existing topological-QFT spine.**  The finite Fourier
  kernel used by the rotation trick is identified with the existing
  Chern-Simons-Witten modular `S`-matrix, and the real/fermionic Bott-periodic
  shadow reuses the already formalized Witten Majorana-chain period-eight
  class.

## References

* R. Willett, *Bott periodicity and almost commuting matrices* (2019).
* M. Atiyah, *Bott periodicity and the index of elliptic operators*, Quart.
  J. Math. Oxford Ser. (2) 19 (1968), 113-140.
* T. Loring, *The torus and noncommutative topology*, PhD thesis, UC Berkeley
  (1985).
* D.-V. Voiculescu, *Asymptotically commuting finite rank unitary operators
  without commuting approximants*, Acta Sci. Math. (Szeged) 45 (1983), 429-431.
* G. Yu, *Localization algebras and the coarse Baum-Connes conjecture*,
  K-Theory 11 (1997), 307-318.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.BottPeriodicityAlmostCommuting

open Physlib.Mathematics.Algebra.AlmostCommutative
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## A. Suspended Bott projection formula -/

/-- The algebra-level representative of the Bott map
`β_A([p]) = [z^{-1}p + (1-p)]` for a projection `p`.  The variable `z` is the
suspension-circle unitary; the proof obligations that this defines a `K₁`
class live in the ambient `C*`-algebraic `K`-theory layer, not in this finite
algebraic module. -/
def bottSuspendedProjectionUnitary {A : Type*} [Ring A] (z p : A) : A :=
  z * p + (1 - p)

/-- At the base point `z=1`, the Bott suspended projection representative is
the identity. -/
lemma bottSuspendedProjectionUnitary_basepoint {A : Type*} [Ring A] (p : A) :
    bottSuspendedProjectionUnitary (1 : A) p = 1 := by
  rw [bottSuspendedProjectionUnitary, one_mul]
  abel

/-- For the full projection `p=1`, the Bott suspended projection representative
is the circle unitary `z`. -/
lemma bottSuspendedProjectionUnitary_top {A : Type*} [Ring A] (z : A) :
    bottSuspendedProjectionUnitary z (1 : A) = z := by
  simp [bottSuspendedProjectionUnitary]

/-- For the zero projection `p=0`, the Bott suspended projection representative
is the identity. -/
lemma bottSuspendedProjectionUnitary_bot {A : Type*} [Ring A] (z : A) :
    bottSuspendedProjectionUnitary z (0 : A) = 1 := by
  simp [bottSuspendedProjectionUnitary]

/-- The suspended Bott projection formula is natural for algebra morphisms. -/
lemma map_bottSuspendedProjectionUnitary {A B : Type*} [Ring A] [Ring B]
    [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (z p : A) :
    φ (bottSuspendedProjectionUnitary z p)
      = bottSuspendedProjectionUnitary (φ z) (φ p) := by
  simp [bottSuspendedProjectionUnitary]

/-! ## B. Loring's element -/

/-- The `2 × 2` Loring element associated to scalar functions `f,g,h` of one
unitary and a second unitary `v`.  The entry `vstar` represents `v*`. -/
def loringElement {A : Type*} [Ring A] (f g h vstar v : A) :
    Matrix (Fin 2) (Fin 2) A :=
  !![f, g + h * v; vstar * h + g, 1 - f]

/-- The trace of the Loring element is one. -/
lemma loringElement_trace {A : Type*} [CommRing A] (f g h vstar v : A) :
    Matrix.trace (loringElement f g h vstar v) = 1 := by
  simp [loringElement, Matrix.trace, Fin.sum_univ_two]

/-- If Loring's scalar functions satisfy `f^2+g^2+h^2=f`, `gh=0`, and the two
unitary entries multiply to one, then the Loring element is idempotent.  This
is the commuting-unitary case of Willett's Eq. (3). -/
lemma loringElement_mul_self_of_bott_relations {A : Type*} [CommRing A]
    {f g h vstar v : A} (hfg : f ^ 2 + g ^ 2 + h ^ 2 = f)
    (hgh : g * h = 0) (hv : vstar * v = 1) :
    loringElement f g h vstar v * loringElement f g h vstar v
      = loringElement f g h vstar v := by
  have hgh' : h * g = 0 := by rw [mul_comm, hgh]
  have hv' : v * vstar = 1 := by rw [mul_comm, hv]
  have hghv : g * h * v = 0 := by rw [hgh, zero_mul]
  have hghvstar : g * h * vstar = 0 := by rw [hgh, zero_mul]
  have hvstarhg : vstar * h * g = 0 := by
    calc vstar * h * g = vstar * (h * g) := by ring
      _ = 0 := by rw [hgh', mul_zero]
  have hhgv : h * g * v = 0 := by rw [hgh', zero_mul]
  have hsq_v_vstar : h ^ 2 * v * vstar = h ^ 2 := by
    calc h ^ 2 * v * vstar = h ^ 2 * (v * vstar) := by ring
      _ = h ^ 2 * 1 := by rw [hv']
      _ = h ^ 2 := by ring
  have hvstar_hsq_v : vstar * h ^ 2 * v = h ^ 2 := by
    calc vstar * h ^ 2 * v = h ^ 2 * (vstar * v) := by ring
      _ = h ^ 2 * 1 := by rw [hv]
      _ = h ^ 2 := by ring
  ext i j
  fin_cases i
  · fin_cases j
    · simp [loringElement, Matrix.mul_apply, Fin.sum_univ_two]
      calc
        f * f + (g + h * v) * (vstar * h + g) = f ^ 2 + g ^ 2 + h ^ 2 := by
          ring_nf
          rw [hghv, hghvstar, hsq_v_vstar]
          ring
        _ = f := hfg
    · simp [loringElement, Matrix.mul_apply, Fin.sum_univ_two]
      ring
  · fin_cases j
    · simp [loringElement, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [loringElement, Matrix.mul_apply, Fin.sum_univ_two]
      calc
        (vstar * h + g) * (g + h * v) + (1 - f) * (1 - f)
            = 1 - 2 * f + (f ^ 2 + g ^ 2 + h ^ 2) := by
          ring_nf
          rw [hvstarhg, hvstar_hsq_v, hhgv]
          ring
        _ = 1 - f := by rw [hfg]; ring

/-- The idempotent defect of Loring's element.  Willett's argument estimates
this defect when the two unitaries almost commute. -/
def loringIdempotentDefect {A : Type*} [Ring A] (f g h vstar v : A) :
    Matrix (Fin 2) (Fin 2) A :=
  loringElement f g h vstar v * loringElement f g h vstar v
    - loringElement f g h vstar v

/-- Under the commuting Bott relations, the Loring idempotent defect vanishes. -/
lemma loringIdempotentDefect_eq_zero_of_bott_relations {A : Type*} [CommRing A]
    {f g h vstar v : A} (hfg : f ^ 2 + g ^ 2 + h ^ 2 = f)
    (hgh : g * h = 0) (hv : vstar * v = 1) :
    loringIdempotentDefect f g h vstar v = 0 := by
  rw [loringIdempotentDefect, loringElement_mul_self_of_bott_relations hfg hgh hv]
  simp

/-! ## C. Clock-shift commutator defect -/

/-- The ordinary commutator as the `ρ≡1` specialization of the existing
almost-commutative `ρ`-commutator. -/
noncomputable def ordinaryCommutator {A : Type*} [Ring A] [Algebra ℂ A] (a b : A) : A :=
  rhoCommutator (trivialFactor (ZMod 1) ℂ) (0 : ZMod 1) (0 : ZMod 1) a b

/-- The ordinary commutator unfolds to `ab-ba`. -/
lemma ordinaryCommutator_eq {A : Type*} [Ring A] [Algebra ℂ A] (a b : A) :
    ordinaryCommutator a b = a * b - b * a := by
  exact rhoCommutator_trivial (G := ZMod 1) (k := ℂ) (A := A)
    (0 : ZMod 1) (0 : ZMod 1) a b

/-- A finite Weyl clock-shift pair satisfying `clock * shift = phase * shift * clock`. -/
structure BottWeylPair (A : Type*) [Ring A] where
  /-- The clock operator. -/
  clock : A
  /-- The shift operator. -/
  shift : A
  /-- The scalar phase of the finite Weyl relation. -/
  phase : A
  /-- The Weyl relation `clock * shift = phase * (shift * clock)`. -/
  relation : clock * shift = phase * (shift * clock)

/-- The clock-shift commutator is exactly the Weyl phase defect. -/
lemma bottWeylPair_commutator_eq_phase_defect {A : Type*} [Ring A] [Algebra ℂ A]
    (W : BottWeylPair A) :
    ordinaryCommutator W.clock W.shift = (W.phase - 1) * (W.shift * W.clock) := by
  rw [ordinaryCommutator_eq, W.relation]
  noncomm_ring

/-- When the Weyl phase is one, the clock and shift commute. -/
lemma bottWeylPair_commutator_eq_zero_of_phase_one {A : Type*} [Ring A] [Algebra ℂ A]
    (W : BottWeylPair A) (hphase : W.phase = 1) :
    ordinaryCommutator W.clock W.shift = 0 := by
  rw [bottWeylPair_commutator_eq_phase_defect, hphase]
  simp

/-! ## D. Links to the existing CSW and Witten periodicity spine -/

/-- The finite Fourier kernel used by the Bott rotation trick, represented by
the repository's level-`k` Chern-Simons-Witten modular `S`-matrix. -/
noncomputable def bottFourierKernel (k : ℕ) (a b : Fin k) : ℂ :=
  cswSMatrix k a b

/-- The Bott finite Fourier kernel is definitionally the CSW modular
`S`-matrix already used by the Verlinde and Wilson-loop files. -/
lemma bottFourierKernel_eq_cswSMatrix (k : ℕ) (a b : Fin k) :
    bottFourierKernel k a b = cswSMatrix k a b := rfl

/-- The finite Fourier kernel has orthonormal rows by the existing CSW
`S`-matrix unitarity theorem. -/
lemma bottFourierKernel_unitary (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    (∑ c : Fin k,
        bottFourierKernel k a c * (starRingEnd ℂ) (bottFourierKernel k b c))
      = if a = b then 1 else 0 := by
  simpa [bottFourierKernel] using cswSMatrix_unitary k hk a b

/-- The real/fermionic Bott-periodic shadow is the existing Witten Majorana
chain stacking class. -/
abbrev MajoranaBottClass :=
  WittenFermionPathIntegralsTopologicalPhases.MajoranaChainStackingClass

/-- The Bott-periodic Majorana class is the Witten Majorana-chain stacking
class under the existing constructor. -/
lemma majoranaBottClass_eq_wittenClass (nu : ℕ) :
    (nu : MajoranaBottClass) =
      WittenFermionPathIntegralsTopologicalPhases.majoranaChainStackingClass nu := rfl

/-- The Witten Majorana-chain class is eight-periodic, reusing the existing
topological-phase formalization rather than restating the calculation. -/
lemma majoranaBottClass_period_eight (nu : ℕ) :
    (nu + 8 : MajoranaBottClass) = (nu : MajoranaBottClass) :=
  by
    change (nu : ZMod 8) + (8 : ZMod 8) = (nu : ZMod 8)
    rw [show (8 : ZMod 8) = 0 from ZMod.natCast_self 8, add_zero]

/-- The same period-eight statement in the named Witten stacking-class API. -/
lemma majoranaBottClass_period_eight_wittenAPI (nu : ℕ) :
    WittenFermionPathIntegralsTopologicalPhases.majoranaChainStackingClass (nu + 8) =
      WittenFermionPathIntegralsTopologicalPhases.majoranaChainStackingClass nu :=
  WittenFermionPathIntegralsTopologicalPhases.majoranaChainStackingClass_period_eight nu

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.BottPeriodicityAlmostCommuting

end
