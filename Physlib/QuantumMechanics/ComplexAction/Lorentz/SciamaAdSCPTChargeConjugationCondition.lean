/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCorrespondence
public import Mathlib.Algebra.Ring.Parity

/-!
# When does 𝒩 = 4 SYM admit C? The existence condition and the action of C (Gomis 2507.12467, §2.1)

Gomis §2.1: a Yang–Mills theory coupled to a chiral Weyl fermion in representation `R` has charge conjugation
`C` iff `R` is **self-conjugate under an outer automorphism** `σ(R) = R` (Eq. 2.19).  Because the `𝒩 = 4` fields
are in the *adjoint* (self-conjugate under any `σ`), **`𝒩 = 4` SYM with gauge group `G` has `C` iff the Lie
algebra `𝔤` admits an outer automorphism** — i.e. its Dynkin diagram has a nontrivial symmetry: `𝔰𝔲(N)` for
`N ≥ 3` (`A_{N−1}`), `𝔰𝔬(2n)` (`D_n`), and `𝔢₆`, generating a `ℤ₂^C`; no `C` for other simple algebras.

This module formalizes that classification and the concrete action of `C`:

* `admitsChargeConjugation` — the Dynkin-diagram outer-automorphism data (Eq. 2.19); `su3_admitsC`,
  `su2_no_chargeConjugation`, `e6_admitsC`, `e7_no_chargeConjugation`, `so8_admitsC`.
* **Chiral-primary parity (Eq. 2.25)** `chiralPrimaryParity Δ = (−1)^Δ`, `C(𝒪_Δ) = (−1)^Δ 𝒪_Δ`:
  `chiralPrimaryParity_even_neutral` (even `Δ` neutral), `chiralPrimaryParity_odd_charged` (odd `Δ` charged),
  `chiralPrimaryParity_mul` (multiplicative on the OPE / a `ℤ₂` character).
* **Wilson-line conjugation (Eq. 2.31)** `C(W_{A_k}) = W_{A_{N−k}}`: the rank-`k` antisymmetric Wilson line
  maps to rank `N − k` (`wilsonAntisymmConj`), is `C`-self-conjugate iff `2k = N`
  (`wilsonAntisymm_selfConjugate_iff`), and `C² = 1` on the ranks (`wilsonAntisymmConj_involutive`).

This is the microscopic origin of the discrete `C` whose `(ℤ/2)³` `S`-duality action is
`SciamaAdSCPTCorrespondence`: `C` exists because `𝔰𝔲(N)` has the `A_{N−1}` flip `Υ ↦ −Υᵀ` (Eq. 2.21), it acts
on chiral primaries with parity `(−1)^Δ`, and on Wilson lines by `R ↦ R̄` — the boundary data whose bulk dual is
`bulkC = Ω(−1)^{F_L}R_{456789}` (`SciamaAdSCPTBulkCorrespondence`).

Honest scope: the Eq. 2.19 existence classification (as Dynkin outer-automorphism data), the `(−1)^Δ`
chiral-primary parity, and the `k ↦ N−k` Wilson-line conjugation.  The representation-theoretic derivations
(Schur's lemma fixing `B ∝ 𝟙`, the Dynkin-label permutation) are the paper's content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTChargeConjugationCondition

/-- A simple gauge Lie algebra, labelled by its Cartan type. -/
inductive GaugeAlgebra where
  /-- `𝔰𝔲(n)` — Cartan type `A_{n−1}`. -/
  | su (n : ℕ)
  /-- `𝔰𝔬(n)` — Cartan type `B` (odd `n`) or `D` (even `n`). -/
  | so (n : ℕ)
  /-- `𝔰𝔭(n)` — Cartan type `C`. -/
  | sp (n : ℕ)
  /-- The exceptional algebra `𝔢₆` (Dynkin `ℤ₂` symmetry). -/
  | e6
  /-- The exceptional algebra `𝔢₇`. -/
  | e7
  /-- The exceptional algebra `𝔢₈`. -/
  | e8
  /-- The exceptional algebra `𝔣₄`. -/
  | f4
  /-- The exceptional algebra `𝔤₂`. -/
  | g2

/-- **[Eq. 2.19] Whether `𝒩 = 4` SYM with this gauge algebra admits `C`** — equivalently whether the Dynkin
diagram has a nontrivial (outer) automorphism.  `𝔰𝔲(N≥3)` (`A_{N−1}`), `𝔰𝔬(2n)` (`D_n`), and `𝔢₆`; no others. -/
def admitsChargeConjugation : GaugeAlgebra → Prop
  | .su n => 3 ≤ n
  | .so n => Even n ∧ 4 ≤ n
  | .e6 => True
  | _ => False

/-- **[C for `𝔰𝔲(3)`] `A₂` has the diagram flip.** -/
theorem su3_admitsC : admitsChargeConjugation (.su 3) := by
  unfold admitsChargeConjugation; decide

/-- **[No C for `𝔰𝔲(2)`] `A₁` is symmetric (pseudoreal, self-conjugate without an outer auto).** -/
theorem su2_no_chargeConjugation : ¬ admitsChargeConjugation (.su 2) := by
  unfold admitsChargeConjugation; decide

/-- **[C for `𝔰𝔬(8)`] `D₄` has (an enhanced `S₃`) outer automorphism.** -/
theorem so8_admitsC : admitsChargeConjugation (.so 8) := by
  unfold admitsChargeConjugation; decide

/-- **[No C for `𝔰𝔬(7)`] `B₃` has no diagram automorphism.** -/
theorem so7_no_chargeConjugation : ¬ admitsChargeConjugation (.so 7) := by
  unfold admitsChargeConjugation; decide

/-- **[C for `𝔢₆`] the exceptional `ℤ₂` charge conjugation.** -/
theorem e6_admitsC : admitsChargeConjugation .e6 := trivial

/-- **[No C for `𝔢₇`].** -/
theorem e7_no_chargeConjugation : ¬ admitsChargeConjugation .e7 := by
  unfold admitsChargeConjugation; exact not_false

/-! ## Chiral-primary charge-conjugation parity (Eq. 2.25) -/

/-- **[Eq. 2.25] The `C`-parity of the chiral primary `𝒪_Δ`**: `C(𝒪_Δ) = (−1)^Δ 𝒪_Δ`. -/
def chiralPrimaryParity (Δ : ℕ) : ℤ := (-1) ^ Δ

/-- **[Even Δ is C-neutral] `chiralPrimaryParity Δ = 1`.** -/
theorem chiralPrimaryParity_even_neutral {Δ : ℕ} (h : Even Δ) : chiralPrimaryParity Δ = 1 := by
  rw [chiralPrimaryParity]; exact h.neg_one_pow

/-- **[Odd Δ is C-charged] `chiralPrimaryParity Δ = −1`.** -/
theorem chiralPrimaryParity_odd_charged {Δ : ℕ} (h : Odd Δ) : chiralPrimaryParity Δ = -1 := by
  rw [chiralPrimaryParity]; exact h.neg_one_pow

/-- **[C-parity is a ℤ₂ character] `parity(Δ₁+Δ₂) = parity(Δ₁)·parity(Δ₂)`.**  The `C`-parity is multiplicative
under the operator product — consistent with `C` being a `ℤ₂` global symmetry. -/
theorem chiralPrimaryParity_mul (Δ₁ Δ₂ : ℕ) :
    chiralPrimaryParity (Δ₁ + Δ₂) = chiralPrimaryParity Δ₁ * chiralPrimaryParity Δ₂ := by
  simp [chiralPrimaryParity, pow_add]

/-- **[C² = 1 on operators] `parity(Δ)² = 1`.** -/
theorem chiralPrimaryParity_sq (Δ : ℕ) : chiralPrimaryParity Δ * chiralPrimaryParity Δ = 1 := by
  rw [← chiralPrimaryParity_mul]
  exact chiralPrimaryParity_even_neutral ⟨Δ, rfl⟩

/-! ## Wilson-line charge conjugation (Eq. 2.31) -/

/-- **[Eq. 2.31] `C(W_{A_k}) = W_{A_{N−k}}`**: charge conjugation sends the rank-`k` antisymmetric Wilson line
to rank `N − k` (the conjugate representation `A_k↦ A_{N−k}` of `𝔰𝔲(N)`). -/
def wilsonAntisymmConj (N k : ℕ) : ℕ := N - k

/-- **[A Wilson line is C-self-conjugate iff `2k = N`] `N − k = k ↔ 2k = N`.**  The middle antisymmetric rep
`A_{N/2}` is the `C`-invariant Wilson line; others pair up. -/
theorem wilsonAntisymm_selfConjugate_iff (N k : ℕ) (h : k ≤ N) :
    wilsonAntisymmConj N k = k ↔ 2 * k = N := by
  unfold wilsonAntisymmConj
  omega

/-- **[C² = 1 on Wilson lines] `A_{N−(N−k)} = A_k`.**  Conjugating twice returns the original rank. -/
theorem wilsonAntisymmConj_involutive (N k : ℕ) (h : k ≤ N) :
    wilsonAntisymmConj N (wilsonAntisymmConj N k) = k := by
  unfold wilsonAntisymmConj
  omega

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTChargeConjugationCondition

end
