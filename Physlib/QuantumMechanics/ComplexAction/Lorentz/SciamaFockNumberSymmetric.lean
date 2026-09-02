/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberOperatorPMap
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# General-domain symmetry of the number operator

`SciamaFockAdjointness.numberOp_symmetric` established `⟨N m|n⟩ = ⟨m|N n⟩` on the number *basis*.  This
upgrades it to the full **symmetry on the whole dense domain**: `⟨N x, y⟩ = ⟨x, N y⟩` for all `x, y ∈ dom N`,
i.e. `numberPMap` is a formal adjoint of itself (`N ⊆ N†`).  Together with essential self-adjointness
(`SciamaFockEssentialSelfAdjoint`) this is the full statement that `N` is symmetric and essentially
self-adjoint.

* `numberOp_apply_coe` — the coordinate formula `(Na)_i = i·a_i` on the algebraic Fock space.
* `incl_numberOp_symmetric` — `⟨incl(Na), incl b⟩ = ⟨incl a, incl(Nb)⟩` for all `a, b` (via `inner_eq_tsum`).
* `numberPMap_isFormalAdjoint_self`, `numberPMap_le_adjoint` — `N` is symmetric: `N ⊆ N†`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberSymmetric

open RCLike
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberOperatorPMap

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The `k`-th ℓ² coordinate of a vector is its inner product with `|k⟩`. -/
theorem inner_fockKet (v : FockHilbert) (k : ℕ) : ⟪fockKet k, v⟫ = v k := by
  rw [fockKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

/-- **[Inclusion preserves coordinates] `(incl x)_i = x_i`.** -/
theorem incl_apply_coe (x : ℕ →₀ ℂ) (i : ℕ) : (incl x) i = x i := by
  rw [← inner_fockKet (incl x) i, incl, fockKet_orthonormal.inner_right_finsupp]

/-- `N(c|k⟩) = (k·c)|k⟩` on the algebraic Fock space. -/
theorem numberOp_single (k : ℕ) (c : ℂ) :
    numberOp (Finsupp.single k c) = Finsupp.single k ((k : ℂ) * c) := by
  have hsc : (Finsupp.single k c : ℕ →₀ ℂ) = c • numberKet k := by
    rw [numberKet, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsc, map_smul, numberOp_numberKet, smul_smul, numberKet, Finsupp.smul_single, smul_eq_mul]
  congr 1
  ring

/-- **[Coordinate formula] `(Na)_i = i·a_i`.**  The number operator multiplies the `i`-th coordinate by `i`. -/
theorem numberOp_apply_coe (a : ℕ →₀ ℂ) (i : ℕ) : (numberOp a) i = (i : ℂ) * a i := by
  induction a using Finsupp.induction with
  | zero => simp
  | single_add k c f hk hc ih =>
    rw [map_add, Finsupp.add_apply, numberOp_single, Finsupp.add_apply, mul_add, ih]
    congr 1
    rcases eq_or_ne i k with hik | hik
    · subst hik; simp
    · rw [Finsupp.single_eq_of_ne hik, Finsupp.single_eq_of_ne hik, mul_zero]

/-- **[General-domain symmetry] `⟨incl(Na), incl b⟩ = ⟨incl a, incl(Nb)⟩`** for all `a, b`. -/
theorem incl_numberOp_symmetric (a b : ℕ →₀ ℂ) :
    ⟪incl (numberOp a), incl b⟫ = ⟪incl a, incl (numberOp b)⟫ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun i => ?_)
  simp only [incl_apply_coe, numberOp_apply_coe]
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_natCast]
  ring

/-- **[Number operator is symmetric] `N ⊆ N†`.**  `numberPMap` is a formal adjoint of itself: `⟨N x, y⟩ =
⟨x, N y⟩` for all `x, y` in the dense domain. -/
theorem numberPMap_isFormalAdjoint_self : numberPMap.IsFormalAdjoint numberPMap := by
  intro x y
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  have hx : numberPMap x = incl (numberOp a) := by
    have hxe : x = ⟨incl a, LinearMap.mem_range_self incl a⟩ := Subtype.ext ha.symm
    rw [hxe]; exact numberPMap_toFun_incl a
  have hy : numberPMap y = incl (numberOp b) := by
    have hye : y = ⟨incl b, LinearMap.mem_range_self incl b⟩ := Subtype.ext hb.symm
    rw [hye]; exact numberPMap_toFun_incl b
  show ⟪numberPMap x, (↑y : FockHilbert)⟫ = ⟪(↑x : FockHilbert), numberPMap y⟫
  rw [hx, hy, ← ha, ← hb]
  exact incl_numberOp_symmetric a b

/-- **[Symmetric operator inclusion] `N ≤ N†`.** -/
theorem numberPMap_le_adjoint : numberPMap ≤ numberPMap.adjoint :=
  numberPMap_isFormalAdjoint_self.le_adjoint numberPMap_denseDefined

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberSymmetric

end
