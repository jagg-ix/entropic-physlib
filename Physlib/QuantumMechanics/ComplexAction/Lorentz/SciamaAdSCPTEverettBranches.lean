/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTChargeConjugationCondition
public import Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

/-!
# Charge conjugation as an Everettian relative-state branch structure (Gomis 2507.12467 × Kuypers–Deutsch)

The discrete `C` of `𝒩 = 4` SYM is a `ℤ₂` global symmetry acting on chiral primaries with parity
`C(𝒪_Δ) = (−1)^Δ 𝒪_Δ` (Gomis Eq. 2.25, `SciamaAdSCPTChargeConjugationCondition`).  A `ℤ₂` symmetry with a `±1`
eigenvalue is exactly a **two-outcome branch label** in the Everettian relative-state formalism of Kuypers &
Deutsch (`Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates`): `C`-even operators occupy one
branch, `C`-odd operators the other, and under `C`-symmetric (branch-preserving) Heisenberg evolution the two
sectors evolve autonomously — the `C`-even and `C`-odd **worlds**.

This module makes the identification precise:

* `chargeConjugationBranch_sign` — **the Everett branch sign *is* the `C`-parity `(−1)^Δ`** (Eq. 2.25): the
  chiral primary `𝒪_Δ` sits in the `+` branch when `Δ` is even (`C`-neutral) and the `−` branch when `Δ` is odd
  (`C`-charged).
* `chargeConjugation_branch_decomposition` — the `C`-even and `C`-odd branch projections reconstruct the
  universal wavefunction (`SciamaAdSCPTCorrespondence`'s `C` splits the state into two complementary Everett
  branches).
* `chargeConjugation_everett_branch` — **`C` (with `C² = 1`,
  `SciamaAdSCPTCliffordChargeConjugation.chargeConjugation_involutive`) generates an Everett relative-state
  branch**: its relative Heisenberg descriptor satisfies `(C·P)² = P` (Kuypers–Deutsch), so `C` selects a
  well-defined branch.
* `chargeConjugation_preserves_totalBornWeight` — the `+ ↔ −` `C`-conjugation preserves the total Born weight:
  `C`-conjugate Everett branches carry **equal weight** (the `CPT`-invariance
  `SciamaAdSCPTCorrespondence.sDuality_CPT_invariant` maps the branch decomposition to itself).
* `chargeConjugationBranch_adjacent_flip` — adjacent-dimension operators `𝒪_Δ`, `𝒪_{Δ+1}` lie in **opposite**
  Everett branches (`C` flips the branch as `Δ ↦ Δ+1`).

So the AdS/C-P-T `C` — an outer automorphism of the gauge group, dual to `Ω(−1)^{F_L}R_{456789}` — is, on the
Hilbert space, the `ℤ₂` superselection whose two eigenspaces are Everett's relative-state branches, with no
primitive collapse (`everettHeisenberg_excludes_primitive_collapse`).

Honest scope: the identification of the `(−1)^Δ` `C`-parity with the Kuypers–Deutsch two-outcome branch sign,
Born-weight, and relative-descriptor structure.  The `many-worlds` interpretation itself and the general
decoherent-branch continuum are the foundational content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTEverettBranches

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTChargeConjugationCondition
open Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

/-- The Everett branch a chiral primary `𝒪_Δ` occupies under the `C`-parity superselection: `C`-even (`Δ` even)
occupies the `+` branch, `C`-odd (`Δ` odd) the `−` branch. -/
def chargeConjugationBranch (Δ : ℕ) : SpinOutcome :=
  if Even Δ then SpinOutcome.plus else SpinOutcome.minus

/-- **[Eq. 2.25 as an Everett branch sign] the branch sign is the `C`-parity `(−1)^Δ`.**  The two-outcome
Everett branch label carries exactly the charge-conjugation eigenvalue of the chiral primary. -/
theorem chargeConjugationBranch_sign (Δ : ℕ) :
    SpinOutcome.sign (chargeConjugationBranch Δ) = ((chiralPrimaryParity Δ : ℤ) : ℝ) := by
  unfold chargeConjugationBranch
  rcases Nat.even_or_odd Δ with h | h
  · rw [if_pos h, chiralPrimaryParity_even_neutral h]
    simp [SpinOutcome.sign]
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), chiralPrimaryParity_odd_charged h]
    simp [SpinOutcome.sign]

/-- **[C-parity Everett branch decomposition] the `C`-even and `C`-odd projections reconstruct the state.**  The
two complementary `C`-parity sectors are Everett branches summing to the universal wavefunction. -/
theorem chargeConjugation_branch_decomposition (ψ : SpinOutcome → ℂ) :
    spinProjectedBranchVector SpinOutcome.plus ψ + spinProjectedBranchVector SpinOutcome.minus ψ = ψ :=
  spinProjectedBranchVector_sum ψ

/-- **[C generates an Everett relative-state branch] `(C·P)² = P`.**  A charge-conjugation operator `C` with
`C² = 1` (an involution) commuting with a branch projector `P` has a relative Heisenberg descriptor `C·P` that
squares to `P` (Kuypers–Deutsch) — so `C` selects a well-defined Everett branch, the `C`-even/`C`-odd worlds. -/
theorem chargeConjugation_everett_branch {A : Type*} [Semiring A] {C P : A}
    (hC : C * C = 1) (hP : IsBranchProjector P) (hcomm : C * P = P * C) :
    relativeDescriptor C P * relativeDescriptor C P = P :=
  relativeDescriptor_sq_eq_projector hC hP hcomm

/-- **[C-conjugate Everett branches carry equal Born weight] flipping `+ ↔ −` preserves total Born weight.**
The `C`-conjugation of the branch label is Born-weight preserving, so the two `C`-conjugate Everett branches
have equal weight — the `CPT`-invariance mapping the branch decomposition to itself. -/
theorem chargeConjugation_preserves_totalBornWeight (ψ : SpinOutcome → ℂ) :
    totalBornWeight (fun s => ψ (SpinOutcome.flip s)) = totalBornWeight ψ := by
  simp only [totalBornWeight, branchBornWeight]
  exact Fintype.sum_equiv
    ⟨SpinOutcome.flip, SpinOutcome.flip, fun s => by cases s <;> rfl, fun s => by cases s <;> rfl⟩
    (fun s => ‖ψ (SpinOutcome.flip s)‖ ^ 2) (fun s => ‖ψ s‖ ^ 2)
    (fun x => by cases x <;> rfl)

/-- **[C flips the Everett branch between adjacent dimensions] `branch(Δ+1) = flip (branch Δ)`.**  The chiral
primaries `𝒪_Δ` and `𝒪_{Δ+1}` sit in opposite `C`-parity Everett branches. -/
theorem chargeConjugationBranch_adjacent_flip (Δ : ℕ) :
    chargeConjugationBranch (Δ + 1) = SpinOutcome.flip (chargeConjugationBranch Δ) := by
  unfold chargeConjugationBranch
  rcases Nat.even_or_odd Δ with h | h
  · rw [if_pos h, if_neg (by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using h)]
    rfl
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), if_pos (by simpa [Nat.even_add_one] using h)]
    rfl

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTEverettBranches

end
