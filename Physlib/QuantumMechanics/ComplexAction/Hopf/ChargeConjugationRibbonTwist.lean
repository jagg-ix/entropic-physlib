/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Hopf antipode as charge conjugation, and the ribbon twist as spin-statistics

In the Hopf-algebra description of internal symmetry the **antipode** is the charge-conjugation / time-reversal
operation, and a **ribbon twist** `θ = e^{2πih}` encodes spin-statistics (the `−1` fermion exchange sign at
half-integer conformal weight). This file formalizes those standard algebraic facts; the trefoil-knot
*topology* is not formalized, because there is no knot-theoretic infrastructure to derive its invariants from
(stating them would be vacuous).

* **§A — antipode = charge conjugation.** In the Hopf algebra of integer charges `ℂ[t, t⁻¹] =
  MonoidAlgebra ℂ (Multiplicative ℤ)` the group-like state `chargeState q` with charge `q` has antipode
  `chargeState (−q)` (`antipode_chargeState`): the Hopf antipode is charge negation — an **involution**
  (`antipode_chargeState_involutive`), exactly the algebraic content of "antipode = charge conjugation".
* **§B — antipode = inverse.** `antipode_chargeState_mul_cancel` / `chargeState_mul_antipode_cancel`: the
  antipode is the two-sided inverse of the group-like charge state, `S(g)·g = g·S(g) = 1` — the Hopf-algebra
  fact that makes group-like elements a group (Mathlib's `IsGroupLikeElem.antipode_mul_cancel`).
* **§C — ribbon twist = spin-statistics.** `ribbonTwist h = e^{2πih}`: `ribbonTwist_boson` (`θ = 1` at
  integer spin), `ribbonTwist_fermion` (`θ = −1` at spin ½), and `ribbonTwist_spin_statistics`
  (`θ(h+½) = −θ(h)`). `ribbonTwist_half_eq_swap_sign`: the fermion twist `−1` **is** the sign of a
  transposition — the exchange sign of the free-fermion Slater determinant
  (`[[project_alexandrov_mqm_thesis]]`, `MatrixQuantumMechanics.MQMSlaterDeterminant.slaterDeterminant_perm`).

## References

* Standard Hopf-algebra theory (Mathlib `RingTheory.HopfAlgebra`); ribbon / quantum-group spin-statistics
  `θ = e^{2πih}` (Reshetikhin–Turaev ribbon categories).

No new axioms.
-/

set_option autoImplicit false

open scoped MonoidAlgebra

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

/-! ## §A–B — the antipode as charge conjugation / inverse -/

/-- **The integer-charge state** `chargeState q`: the group-like basis element of the Hopf algebra of charges
`ℂ[t, t⁻¹] = MonoidAlgebra ℂ (Multiplicative ℤ)` with charge `q` (`t^q`). -/
noncomputable def chargeState (q : ℤ) : MonoidAlgebra ℂ (Multiplicative ℤ) :=
  MonoidAlgebra.single (Multiplicative.ofAdd q) (1 : ℂ)

/-- **[Charges add]** `chargeState q · chargeState p = chargeState (q + p)`. -/
theorem chargeState_mul (q p : ℤ) : chargeState q * chargeState p = chargeState (q + p) := by
  unfold chargeState
  rw [MonoidAlgebra.single_mul_single, ← ofAdd_add, one_mul]

/-- **[Zero charge is the unit]** `chargeState 0 = 1`. -/
theorem chargeState_zero : chargeState 0 = 1 := by
  unfold chargeState
  rw [ofAdd_zero, ← MonoidAlgebra.one_def]

/-- **[Antipode = charge conjugation, Eq.]** `S(chargeState q) = chargeState (−q)`: the Hopf antipode negates
the charge. This is the algebraic content of identifying the antipode with charge conjugation. -/
theorem antipode_chargeState (q : ℤ) :
    HopfAlgebra.antipode ℂ (chargeState q) = chargeState (-q) := by
  unfold chargeState
  rw [MonoidAlgebra.antipode_single, HopfAlgebra.antipode_one, ← ofAdd_neg]

/-- **[Charge conjugation is an involution]** `S(S(chargeState q)) = chargeState q` — applying charge
conjugation twice returns the original charge (`C² = 1`). -/
theorem antipode_chargeState_involutive (q : ℤ) :
    HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ (chargeState q)) = chargeState q := by
  rw [antipode_chargeState, antipode_chargeState, neg_neg]

/-- **[Antipode is the inverse]** `S(chargeState q) · chargeState q = 1`: the antipode is the two-sided
inverse of the group-like charge state (the Hopf-algebra fact that group-like elements form a group). -/
theorem antipode_chargeState_mul_cancel (q : ℤ) :
    HopfAlgebra.antipode ℂ (chargeState q) * chargeState q = 1 := by
  rw [antipode_chargeState, chargeState_mul, neg_add_cancel, chargeState_zero]

theorem chargeState_mul_antipode_cancel (q : ℤ) :
    chargeState q * HopfAlgebra.antipode ℂ (chargeState q) = 1 := by
  rw [antipode_chargeState, chargeState_mul, add_neg_cancel, chargeState_zero]

/-! ## §C — the ribbon twist as spin-statistics -/

/-- **The ribbon twist** `θ(h) = e^{2πih}` — the eigenvalue of the ribbon element at conformal weight (spin)
`h`. -/
noncomputable def ribbonTwist (h : ℝ) : ℂ := Complex.exp ((2 * Real.pi * h : ℝ) * Complex.I)

/-- **[Integer spin → boson]** `θ(n) = 1` for integer `n`: a bosonic exchange phase. -/
theorem ribbonTwist_boson (n : ℤ) : ribbonTwist (n : ℝ) = 1 := by
  rw [ribbonTwist,
    show ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by
      push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I]

/-- **[Spin ½ → fermion]** `θ(½) = −1`: the `−1` fermion exchange sign. -/
theorem ribbonTwist_fermion : ribbonTwist (1 / 2) = -1 := by
  rw [ribbonTwist,
    show ((2 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I from by
      push_cast; ring,
    Complex.exp_pi_mul_I]

/-- **[Spin-statistics shift]** `θ(h + ½) = −θ(h)`: increasing the spin by ½ flips the exchange sign — the
spin-statistics connection. -/
theorem ribbonTwist_spin_statistics (h : ℝ) : ribbonTwist (h + 1 / 2) = -ribbonTwist h := by
  rw [ribbonTwist, ribbonTwist,
    show ((2 * Real.pi * (h + 1 / 2) : ℝ) : ℂ) * Complex.I
        = ((2 * Real.pi * h : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I from by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **[The fermion twist is the transposition sign]** `θ(½) = sign(swap i j)`: the spin-½ ribbon twist `−1`
**is** the sign of a transposition — i.e. the exchange sign that makes the free-fermion Slater determinant
antisymmetric. The ribbon/Hopf spin-statistics and the matrix-model Pauli antisymmetry are the same `−1`. -/
theorem ribbonTwist_half_eq_swap_sign {α : Type*} [DecidableEq α] [Fintype α] {i j : α} (h : i ≠ j) :
    ribbonTwist (1 / 2) = ((Equiv.Perm.sign (Equiv.swap i j) : ℤ) : ℂ) := by
  rw [ribbonTwist_fermion, Equiv.Perm.sign_swap h]
  norm_num

/-! ## §D — group-like grading and q-deformation -/

/-- **[The charge states are group-like]** `chargeState q` satisfies `ε(g) = 1` and `Δ(g) = g ⊗ g`: the basis
elements of the charge Hopf algebra are group-like, so the charges `q ∈ ℤ` index a **grouplike grading** of
`ℂ[t, t⁻¹]`. -/
theorem chargeState_isGroupLike (q : ℤ) : IsGroupLikeElem ℂ (chargeState q) where
  counit_eq_one := by
    rw [chargeState, MonoidAlgebra.counit_single]
    exact (isGroupLikeElem_self.mpr rfl).counit_eq_one
  comul_eq_tmul_self := by
    unfold chargeState
    rw [MonoidAlgebra.comul_single, (isGroupLikeElem_self.mpr rfl).comul_eq_tmul_self,
      TensorProduct.map_tmul]
    rfl

/-- **[The grouplike grading]** the monoid homomorphism `Multiplicative ℤ → ℂ[t, t⁻¹]`, `t^n ↦ chargeState n`:
the group-like charge states form a copy of the grading group `ℤ` inside the algebra (`map_one' =
chargeState_zero`, `map_mul' = chargeState_mul`). -/
noncomputable def chargeStateHom : Multiplicative ℤ →* MonoidAlgebra ℂ (Multiplicative ℤ) where
  toFun g := chargeState (Multiplicative.toAdd g)
  map_one' := chargeState_zero
  map_mul' g h := by rw [toAdd_mul, chargeState_mul]

/-- **The q-deformation character** `χ_Q(t^n) = Q^n` for a deformation parameter `Q ∈ ℂˣ` (e.g.
`Q = e^{iπγ/2}`): a one-dimensional representation grading the charge states by the `q`-weight. It is a
monoid homomorphism `Multiplicative ℤ → ℂˣ`. -/
noncomputable def qCharacter (Q : ℂˣ) : Multiplicative ℤ →* ℂˣ where
  toFun g := Q ^ (Multiplicative.toAdd g)
  map_one' := by simp
  map_mul' g h := by rw [toAdd_mul, zpow_add]

/-- **[The q-character is multiplicative]** `χ_Q(t^m · t^n) = χ_Q(t^m) · χ_Q(t^n)` — the `q`-deformation
weight respects the grouplike grading. -/
theorem qCharacter_mul (Q : ℂˣ) (m n : ℤ) :
    qCharacter Q (Multiplicative.ofAdd (m + n))
      = qCharacter Q (Multiplicative.ofAdd m) * qCharacter Q (Multiplicative.ofAdd n) := by
  simp [qCharacter, zpow_add]

end Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

end
