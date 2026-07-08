/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeSMatrix
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

/-!
# Wilson loops: braiding ↔ the Verlinde `S`-matrix, and topological spin ↔ the ribbon twist

The Chern–Simons–Witten Wilson loops are the link between the three structures already formalized — the modular
`S` transform (`ChernSimons.BraidModularTorus`, the half-twist `Δ·τ = −1/τ`), the Verlinde `S`-matrix
(`ChernSimons.VerlindeSMatrix.cswSMatrix`), and the ribbon twist / Yang–Baxter braiding
(`Hopf.ChargeConjugationRibbonTwist`, `ChernSimons.BraidRelationTrefoilTorus`). In the abelian `U(1)_k` theory a Wilson loop
of charge `a` is a line operator, and:

* **Braiding `↔` the modular `S`-matrix.** The mutual braiding (monodromy) phase of two Wilson lines of charges
  `a, b` is `e^{2πi ab/k}` (`wilsonBraidingPhase`); it equals `√k · conj(S_{ab})`
  (`wilsonBraidingPhase_eq_S`), i.e. it *is* the Verlinde `S`-matrix entry `S_{ab} = (1/√k)e^{−2πi ab/k}` up to
  conjugation and normalization. The `S`-matrix is exactly the modular `S` realized by the trefoil half-twist
  (`ChernSimons.BraidModularTorus.mobius_halfTwist`), under which the Wilson-loop / theta-character states transform
  (`ChernSimons.WilsonOperators.cswWilsonVerlinde_diagonalization`).
* **Topological spin `↔` the ribbon twist.** The self-braiding (framing) phase of a charge-`a` Wilson loop is
  its topological spin `θ_a = e^{2πi h_a}` at conformal weight `h_a = a²/2k` — exactly the ribbon twist
  `ribbonTwist h_a` (`wilsonTopologicalSpin_eq_ribbonTwist`). A Wilson line of half-integer weight (`a² = k`)
  is a fermion, spin `−1` (`wilsonTopologicalSpin_fermion`); the trivial Wilson line is a boson, spin `1`.

So the trefoil braid's half-twist (modular `S`), the Verlinde `S`-matrix, and the ribbon twist are three faces
of the same Chern–Simons structure read off the Wilson loops.

## References

* E. Witten, *Quantum field theory and the Jones polynomial*, Comm. Math. Phys. **121** (1989) (Wilson loops,
  braiding, framing). Verlinde `S`-matrix `S_{ab} = (1/√k)e^{−2πi ab/k}`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

/-! ## §A — Wilson-line braiding is the Verlinde `S`-matrix -/

/-- **The mutual braiding (monodromy) phase** of two `U(1)_k` Wilson lines of charges `a, b`:
`B_{ab} = e^{2πi ab/k}`. -/
noncomputable def wilsonBraidingPhase (k : ℕ) (a b : Fin k) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (b.val : ℂ) / (k : ℂ))

/-- **[Braiding = Verlinde `S`-matrix]** `B_{ab} = √k · conj(S_{ab})`: the Wilson-line braiding phase is the
Verlinde `S`-matrix entry `S_{ab} = (1/√k)e^{−2πi ab/k}` up to conjugation and the `√k` normalization — the
modular `S` realized by the trefoil half-twist. -/
theorem wilsonBraidingPhase_eq_S (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    wilsonBraidingPhase k a b = (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b) := by
  have hsk : (Real.sqrt k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  unfold wilsonBraidingPhase cswSMatrix
  rw [map_mul, map_div₀, map_one, Complex.conj_ofReal, ← Complex.exp_conj,
    show (starRingEnd ℂ) (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (b.val : ℂ)) / (k : ℂ))
        = 2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (b.val : ℂ) / (k : ℂ) from by
      simp only [map_div₀, map_neg, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
        Complex.conj_natCast]
      ring,
    ← mul_assoc, mul_one_div, div_self hsk, one_mul]

/-! ## §B — Wilson-loop topological spin is the ribbon twist -/

/-- **The conformal weight** `h_a = a²/2k` of a charge-`a` `U(1)_k` Wilson line. -/
noncomputable def wilsonConformalWeight (k : ℕ) (a : Fin k) : ℝ := (a.val : ℝ) ^ 2 / (2 * k)

/-- **The topological spin** (self-braiding / framing phase) of a charge-`a` Wilson loop,
`θ_a = ribbonTwist h_a = e^{2πi h_a}`. -/
noncomputable def wilsonTopologicalSpin (k : ℕ) (a : Fin k) : ℂ :=
  ribbonTwist (wilsonConformalWeight k a)

/-- **[Topological spin = ribbon twist]** the Wilson loop's framing phase `θ_a = e^{2πi·a²/2k}` is the ribbon
twist at the conformal weight `h_a = a²/2k`. -/
theorem wilsonTopologicalSpin_eq_ribbonTwist (k : ℕ) (a : Fin k) :
    wilsonTopologicalSpin k a = ribbonTwist ((a.val : ℝ) ^ 2 / (2 * k)) :=
  rfl

/-- **[Half-integer weight Wilson line is a fermion]** if `a² = k` (conformal weight `h_a = ½`) the Wilson
loop's topological spin is `−1` — the same `−1` ribbon/exchange sign as a spin-½ fermion. -/
theorem wilsonTopologicalSpin_fermion (k : ℕ) (hk : 0 < k) (a : Fin k) (h : (a.val : ℝ) ^ 2 = k) :
    wilsonTopologicalSpin k a = -1 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  unfold wilsonTopologicalSpin wilsonConformalWeight
  rw [show (a.val : ℝ) ^ 2 / (2 * k) = 1 / 2 from by
    rw [h, div_eq_div_iff (mul_ne_zero two_ne_zero hk') two_ne_zero]; ring]
  exact ribbonTwist_fermion

/-- **[Trivial Wilson line is a boson]** the charge-`0` (identity) Wilson loop has topological spin `1`. -/
theorem wilsonTopologicalSpin_vacuum (k : ℕ) (hk : 0 < k) :
    wilsonTopologicalSpin k ⟨0, hk⟩ = 1 := by
  unfold wilsonTopologicalSpin wilsonConformalWeight
  rw [show ((⟨0, hk⟩ : Fin k).val : ℝ) ^ 2 / (2 * k) = 0 from by simp]
  simpa using ribbonTwist_boson 0

/-! ## §C — Abelian anyon sector -/

/-- A compact capability predicate for abelian anyons in `U(1)_k`: every Wilson
line has a ribbon-twist topological spin, mutual braiding is the normalized
Verlinde `S`-matrix, and the vacuum line is bosonic. -/
def HasAbelianAnyonSector (k : ℕ) (hk : 0 < k) : Prop :=
  (∀ a : Fin k, wilsonTopologicalSpin k a = ribbonTwist (wilsonConformalWeight k a))
    ∧ (∀ a b : Fin k,
      wilsonBraidingPhase k a b =
        (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b))
    ∧ wilsonTopologicalSpin k ⟨0, hk⟩ = 1

/-- The abelian anyon sector is exactly the existing Wilson-loop/ribbon/Verlinde
infrastructure collected as one reusable capability. -/
theorem abelianAnyonSector_checked (k : ℕ) (hk : 0 < k) :
    HasAbelianAnyonSector k hk :=
  ⟨fun a => wilsonTopologicalSpin_eq_ribbonTwist k a,
    fun a b => wilsonBraidingPhase_eq_S k hk a b,
    wilsonTopologicalSpin_vacuum k hk⟩

/-- Charge-one line at level two: the semion line. -/
def semionCharge : Fin 2 := ⟨1, by norm_num⟩

/-- The `U(1)_2` charge-one Wilson line has conformal weight `1/4`. -/
theorem semionConformalWeight_quarter :
    wilsonConformalWeight 2 semionCharge = 1 / 4 := by
  norm_num [semionCharge, wilsonConformalWeight]

/-- Its conformal weight is neither the vacuum boson value `0` nor the fermion
half-integer value `1/2`; this is the formal anyon marker used here. -/
theorem semionConformalWeight_not_boson_or_fermion :
    wilsonConformalWeight 2 semionCharge ≠ 0
      ∧ wilsonConformalWeight 2 semionCharge ≠ 1 / 2 := by
  constructor <;> norm_num [semionCharge, wilsonConformalWeight]

/-- The semion topological spin is the quarter-weight ribbon twist. -/
theorem semionTopologicalSpin_eq_quarterRibbon :
    wilsonTopologicalSpin 2 semionCharge = ribbonTwist (1 / 4) := by
  norm_num [semionCharge, wilsonTopologicalSpin, wilsonConformalWeight]

/-- The semion braiding phase is still the normalized Verlinde `S`-matrix row. -/
theorem semionBraidingPhase_eq_S (b : Fin 2) :
    wilsonBraidingPhase 2 semionCharge b =
      (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (cswSMatrix 2 semionCharge b) :=
  wilsonBraidingPhase_eq_S 2 (by norm_num) semionCharge b

/-- Concrete anyon-predicate for the available `U(1)_2` semion:
quarter conformal weight, ribbon topological spin, Verlinde braiding, and not
the boson/fermion conformal weights. -/
def HasSemionAnyonCarrier : Prop :=
  wilsonConformalWeight 2 semionCharge = 1 / 4
    ∧ wilsonTopologicalSpin 2 semionCharge = ribbonTwist (1 / 4)
    ∧ (∀ b : Fin 2,
      wilsonBraidingPhase 2 semionCharge b =
        (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (cswSMatrix 2 semionCharge b))
    ∧ wilsonConformalWeight 2 semionCharge ≠ 0
    ∧ wilsonConformalWeight 2 semionCharge ≠ 1 / 2

/-- The concrete semion anyon structure is checked from existing Wilson-loop,
ribbon, and Verlinde theorems. -/
theorem semionAnyonCarrier_checked : HasSemionAnyonCarrier := by
  rcases semionConformalWeight_not_boson_or_fermion with ⟨h0, hhalf⟩
  exact ⟨semionConformalWeight_quarter, semionTopologicalSpin_eq_quarterRibbon,
    semionBraidingPhase_eq_S, h0, hhalf⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

end
