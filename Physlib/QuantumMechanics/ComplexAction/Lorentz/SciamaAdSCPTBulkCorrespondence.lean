/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCorrespondence

/-!
# The holographic AdS/C-P-T dictionary: the bulk dual transformations (Gomis 2507.12467, §3, Eqs. 1.2, 1.4)

`SciamaAdSCPTCorrespondence` gave the `S`-duality action on the boundary `C, P, T`.  This module formalizes the
**explicit bulk dual** of Gomis's AdS/C-P-T Correspondence — the transformations of Type IIB string theory on
`AdS₅ × S⁵` dual to `C`, `P`, `T` of `𝒩 = 4` SYM (Eq. 1.2), each combining **worldsheet parity** `Ω`, spacetime
**fermion parity** `(−1)^{F_L}` (left-movers), and **coordinate reflections** `R_M` along `x^M`,
`M = 0, …, 9` of `AdS₅ × S⁵`:

`C ↔ Ω(−1)^{F_L} R_{456789},   P ↔ (−1)^{F_L} R_{3456},   T ↔ Ω R_{0789}`.

A bulk transformation is `(Ω, F_L, R)` with `Ω, F_L ∈ ℤ/2` and a reflected coordinate set `R ⊆ {0, …, 9}`;
transformations compose by adding the `ℤ/2` parities and taking the **symmetric difference** of the reflected
sets (two reflections of the same axis cancel).

* `bulkC`, `bulkP`, `bulkT` — the bulk duals of Eq. 1.2, with reflection sets `{4..9}`, `{3,4,5,6}`, `{0,7,8,9}`.
* `bulkC_involutive`, `bulkP_involutive`, `bulkT_involutive` — each bulk transformation is an involution
  (`Ω² = 1`, `(−1)^{2F_L} = 1`, `R Δ R = ∅`), matching `C² = P² = T² = 1`.
* `bulkCPT_reflection` — **`CPT_bulk` reflects exactly `x⁰` and `x³`**: `R_{456789} Δ R_{3456} Δ R_{0789} =
  {0, 3}`; the S⁵ reflections cancel, leaving the time axis `x⁰` and the parity axis `x³` (`R_3 : x³ ↦ −x³`).
* `bulkCPT_worldsheet_parity`, `bulkCPT_fermion_parity` — `CPT_bulk` has **trivial** worldsheet parity and
  fermion parity (the `Ω` and `(−1)^{F_L}` factors pair up), so `CPT_bulk = R_{03}` — the pure bulk `CPT`
  reflection realizing Eq. 1.4, `CPT ↔ CPT_bulk`.

Together with `SciamaAdSCPTCorrespondence` (`S`-duality `P ↦ CP`, `T ↦ CT`, `C, CPT` invariant), this gives the
holographic dictionary of the discrete `C, P, T` symmetries: the boundary `𝒩 = 4` charge-conjugation /
parity / time-reversal, their `S`-duality (BCJ) transformation, and their explicit bulk realization as
worldsheet + geometric symmetries of the AdS₅×S⁵ string.

Honest scope: the `ℤ/2 × ℤ/2 × 𝒫({0..9})` group structure of the bulk duals (Eq. 1.2) and the `CPT_bulk`
reflection (Eq. 1.4).  The supergravity/brane/bubbling-surface derivation of Eq. 1.2 and the monodromy surface
operator (§4) are the paper's content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBulkCorrespondence

/-- A bulk `AdS₅ × S⁵` discrete transformation: `(Ω, F_L, R)` — worldsheet parity `Ω ∈ ℤ/2`, spacetime
fermion parity `(−1)^{F_L}` with `F_L ∈ ℤ/2`, and a reflected coordinate set `R ⊆ {0, …, 9}`. -/
abbrev BulkTransform : Type := ZMod 2 × ZMod 2 × Finset (Fin 10)

/-- Composition of bulk transformations: add the `ℤ/2` parities, symmetric-difference the reflected sets. -/
def bulkCompose (a b : BulkTransform) : BulkTransform :=
  (a.1 + b.1, a.2.1 + b.2.1, symmDiff a.2.2 b.2.2)

/-- **`C ↔ Ω(−1)^{F_L} R_{456789}`** — charge conjugation reflects the `S⁵` coordinates `x⁴…x⁹`. -/
def bulkC : BulkTransform := (1, 1, {4, 5, 6, 7, 8, 9})

/-- **`P ↔ (−1)^{F_L} R_{3456}`** — parity reflects `x³` and the `S⁵` coordinates `x⁴, x⁵, x⁶`. -/
def bulkP : BulkTransform := (0, 1, {3, 4, 5, 6})

/-- **`T ↔ Ω R_{0789}`** — time reversal reflects `x⁰` and the `S⁵` coordinates `x⁷, x⁸, x⁹`. -/
def bulkT : BulkTransform := (1, 0, {0, 7, 8, 9})

/-- The bulk dual of `CPT`. -/
def bulkCPT : BulkTransform := bulkCompose (bulkCompose bulkC bulkP) bulkT

/-- **[`C` is an involution] `C_bulk² = 1`.** -/
theorem bulkC_involutive : bulkCompose bulkC bulkC = (0, 0, ∅) := by decide

/-- **[`P` is an involution] `P_bulk² = 1`.** -/
theorem bulkP_involutive : bulkCompose bulkP bulkP = (0, 0, ∅) := by decide

/-- **[`T` is an involution] `T_bulk² = 1`.** -/
theorem bulkT_involutive : bulkCompose bulkT bulkT = (0, 0, ∅) := by decide

/-- **[`CPT_bulk` reflects `x⁰` and `x³`] `R_{456789} Δ R_{3456} Δ R_{0789} = {0, 3}`.**  The `S⁵` reflections
cancel; the bulk `CPT` reflection is exactly the time axis `x⁰` and the parity axis `x³`. -/
theorem bulkCPT_reflection : bulkCPT.2.2 = {0, 3} := by decide

/-- **[`CPT_bulk` has trivial worldsheet parity].**  The two `Ω` factors (`C` and `T`) pair up. -/
theorem bulkCPT_worldsheet_parity : bulkCPT.1 = 0 := by decide

/-- **[`CPT_bulk` has trivial fermion parity].**  The two `(−1)^{F_L}` factors (`C` and `P`) pair up. -/
theorem bulkCPT_fermion_parity : bulkCPT.2.1 = 0 := by decide

/-- **[Eq. 1.4, `CPT ↔ CPT_bulk`] `CPT_bulk = (0, 0, {0,3}) = R_{03}`.**  The bulk `CPT` is the pure reflection
of `x⁰` and `x³` with trivial worldsheet and fermion parity — the holographic image of the boundary `CPT`
(`SciamaAdSCPTCorrespondence.sDuality_CPT_invariant`). -/
theorem bulkCPT_eq : bulkCPT = (0, 0, {0, 3}) := by decide

/-! ## Composite symmetries and the group structure -/

/-- **[`CP` bulk reflection] `R_{456789} Δ R_{3456} = {3,7,8,9}`.**  Charge-parity reflects `x³, x⁷, x⁸, x⁹`. -/
theorem bulkCP_reflection : (bulkCompose bulkC bulkP).2.2 = {3, 7, 8, 9} := by decide

/-- **[`CT` bulk reflection] `R_{456789} Δ R_{0789} = {0,4,5,6}`.**  Charge-time reflects `x⁰, x⁴, x⁵, x⁶`. -/
theorem bulkCT_reflection : (bulkCompose bulkC bulkT).2.2 = {0, 4, 5, 6} := by decide

/-- **[`PT` bulk reflection] `R_{3456} Δ R_{0789} = {0,3,4,5,6,7,8,9}`.**  Parity-time reflects all but `x¹, x²`. -/
theorem bulkPT_reflection :
    (bulkCompose bulkP bulkT).2.2 = {0, 3, 4, 5, 6, 7, 8, 9} := by decide

/-- **[The bulk symmetries form an abelian group] `A·B = B·A`.**  Bulk transformations commute — the `ℤ/2`
parities and the symmetric-difference of reflected sets are both commutative, so `C, P, T` generate an abelian
`(ℤ/2)`-group. -/
theorem bulkCompose_comm (a b : BulkTransform) : bulkCompose a b = bulkCompose b a := by
  unfold bulkCompose
  rw [add_comm a.1 b.1, add_comm a.2.1 b.2.1, symmDiff_comm a.2.2 b.2.2]

/-- **[§4: charge-conjugation monodromy is `ℤ/2`] `C² = 1` and `C ≠ 1`.**  A field transported around a
codimension-two charge-conjugation surface defect returns charge-conjugated; the monodromy is exactly order two
(`C² = 1`, `C ≠ 1`) — the defect is detectable from afar. -/
theorem chargeConjugation_monodromy_order_two :
    bulkCompose bulkC bulkC = (0, 0, ∅) ∧ bulkC ≠ (0, 0, ∅) :=
  ⟨bulkC_involutive, by decide⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTBulkCorrespondence

end
