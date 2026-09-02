/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann
public import Physlib.Thermodynamics.KullbackLeiblerInformationGain

/-!
# The Sorkin–Johnston Born diagonal obeys the Snoke–Liu–Girvin H-theorem

The consistent-histories decoherence functional `D(α,β) = w(α)conj(w(β))` (`DecoherenceFunctionalSorkinJohnston`)
splits, as every SJ Hermitian kernel does, into a **diagonal** part — the Born probabilities
`quantalMeasure D α = |w(α)|²` — and an **off-diagonal** part suppressed by the entanglement action `S_ent`. This is
exactly the picture of the Snoke–Liu–Girvin quantum-Boltzmann H-theorem
(`Thermodynamics.SecondLawQuantumBoltzmann`): the total (von Neumann) entropy is unitarily invariant
(`vonNeumann_entropy_unitary_invariant`), the entropy *increase* lives entirely in the **diagonal** entropy
`S_d = −k_B ∑ Nₖ ln Nₖ`, and the constant gap `S_vN − S_d` is the off-diagonal (phase / dephasing) information.

Identifying the occupation numbers `Nₖ` with the Born diagonal `bornDistribution w = |w|²`, the H-theorem applies
verbatim: the entropy production between two SJ Born distributions is non-negative, and vanishes exactly at
detailed balance. The decoherence functional's off-diagonal suppression **is** the dephasing that the H-theorem
identifies as the source of the diagonal-entropy rise.

* **`bornDistribution`** — the Born diagonal `quantalMeasure (decoherenceFunctional w) = |w|²`; **`bornDistribution_pos`**.
* **`decoherenceFunctional_hTheorem`** — `0 ≤ ∑ᵢ (ln pᵢ − ln qᵢ)(pᵢ − qᵢ)` for Born distributions `p, q`
  (`hTheorem` — the second law for the Born diagonals).
* **`decoherenceFunctional_detailed_balance`** — the entropy-production term vanishes iff the Born probabilities
  agree (`entropyProduction_term_eq_zero_iff` — equilibrium).
* **`bornDiagonalEntropy`** — the Polkovnikov diagonal entropy `S_d = −k_B ∑ |w|² ln|w|²` of the SJ Born diagonal.
* **§B — the entropy production is a relative entropy.** **`entropyProduction_eq_jeffreys`**
  (`∑(ln p − ln q)(p − q) = D_KL(p‖q) + D_KL(q‖p)`) identifies the H-theorem production with the symmetrized KL
  (Jeffreys) divergence of `KullbackLeiblerInformationGain`, whence **`decoherenceFunctional_jeffreys_nonneg`**
  (`0 ≤ D_KL(p‖q) + D_KL(q‖p)` for the Born distributions — the second law as relative-entropy non-negativity).

**Honest layering.** No new inequalities — the H-theorem, the detailed-balance criterion and the diagonal entropy
are reused verbatim from `SecondLawQuantumBoltzmann`, applied to the Born diagonal supplied by
`DecoherenceFunctionalSorkinJohnston`. The only content is the identification `Nₖ = |w(k)|²` (occupation = Born
weight) and the positivity `|w|² > 0 ⇔ w ≠ 0`.

## References

* Composes `QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston` and
  `Thermodynamics.SecondLawQuantumBoltzmann` (Snoke–Liu–Girvin, Appendix A).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.Thermodynamics.SecondLawQuantumBoltzmann
open Physlib.Thermodynamics.KullbackLeiblerInformationGain

@[expose] public section

namespace Physlib.Thermodynamics.DecoherenceFunctionalBornHTheorem

variable {ι : Type*}

/-- The **Born diagonal** of the decoherence functional `p(α) = quantalMeasure (decoherenceFunctional w) α =
|w(α)|²` — the occupation numbers `Nₖ` of the Snoke H-theorem, supplied by the SJ history kernel. -/
noncomputable def bornDistribution (w : ι → ℂ) : ι → ℝ := quantalMeasure (decoherenceFunctional w)

/-- **The Born diagonal is `|w|²`.** -/
lemma bornDistribution_eq (w : ι → ℂ) (i : ι) : bornDistribution w i = Complex.normSq (w i) :=
  decoherenceFunctional_quantalMeasure w i

/-- **The Born weight is strictly positive** for a nonzero history amplitude — required for the log-balance
inequality. -/
lemma bornDistribution_pos (w : ι → ℂ) (i : ι) (h : w i ≠ 0) : 0 < bornDistribution w i := by
  rw [bornDistribution_eq]; exact Complex.normSq_pos.mpr h

/-- **The Born diagonals obey the H-theorem** `0 ≤ ∑ᵢ (ln pᵢ − ln qᵢ)(pᵢ − qᵢ)` — the entropy production between
two Sorkin–Johnston Born distributions is non-negative, the second law applied to the diagonal (Born) sector of
the decoherence functional. -/
lemma decoherenceFunctional_hTheorem [Fintype ι] (w₁ w₂ : ι → ℂ)
    (h₁ : ∀ i, w₁ i ≠ 0) (h₂ : ∀ i, w₂ i ≠ 0) :
    0 ≤ ∑ i, (Real.log (bornDistribution w₁ i) - Real.log (bornDistribution w₂ i))
          * (bornDistribution w₁ i - bornDistribution w₂ i) :=
  hTheorem _ _ (fun i => bornDistribution_pos w₁ i (h₁ i)) (fun i => bornDistribution_pos w₂ i (h₂ i))

/-- **Detailed balance** — the per-index entropy production vanishes iff the two Born probabilities agree
`|w₁(i)|² = |w₂(i)|²`: the equilibrium condition of the H-theorem, realized on the SJ Born diagonal. -/
lemma decoherenceFunctional_detailed_balance (w₁ w₂ : ι → ℂ) (i : ι) (h₁ : w₁ i ≠ 0) (h₂ : w₂ i ≠ 0) :
    (Real.log (bornDistribution w₁ i) - Real.log (bornDistribution w₂ i))
        * (bornDistribution w₁ i - bornDistribution w₂ i) = 0
      ↔ bornDistribution w₁ i = bornDistribution w₂ i :=
  entropyProduction_term_eq_zero_iff (bornDistribution_pos w₁ i h₁) (bornDistribution_pos w₂ i h₂)

/-- The **Polkovnikov diagonal entropy of the Born diagonal** `S_d = −k_B ∑ |w|² ln|w|²` — the diagonal entropy
(`diagonalEntropy`) of the Sorkin–Johnston decoherence functional's Born probabilities, the entropy the H-theorem
drives up to its detailed-balance maximum. -/
noncomputable def bornDiagonalEntropy [Fintype ι] (kB : ℝ) (w : ι → ℂ) : ℝ :=
  diagonalEntropy kB (bornDistribution w)


/-- **The H-theorem entropy production is the symmetrized KL divergence** `∑ᵢ (ln pᵢ − ln qᵢ)(pᵢ − qᵢ) =
D_KL(p‖q) + D_KL(q‖p)` (the Jeffreys divergence), for positive distributions — identifying the log-balance
inequality of the H-theorem with the relative entropy of `KullbackLeiblerInformationGain`. -/
lemma entropyProduction_eq_jeffreys {J : Type*} [Fintype J] (p q : J → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∑ i, (Real.log (p i) - Real.log (q i)) * (p i - q i)
      = finiteKLDivergence p q + finiteKLDivergence q p := by
  rw [finiteKLDivergence, finiteKLDivergence, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.log_div (hp i).ne' (hq i).ne', Real.log_div (hq i).ne' (hp i).ne']
  ring

/-- **The SJ Born-diagonal entropy production is the Jeffreys divergence of the Born distributions** — the
H-theorem production between two decoherence functionals is `D_KL(p‖q) + D_KL(q‖p)` for the Born weights
`p = |w₁|²`, `q = |w₂|²`. -/
lemma decoherenceFunctional_entropyProduction_eq_jeffreys [Fintype ι] (w₁ w₂ : ι → ℂ)
    (h₁ : ∀ i, w₁ i ≠ 0) (h₂ : ∀ i, w₂ i ≠ 0) :
    ∑ i, (Real.log (bornDistribution w₁ i) - Real.log (bornDistribution w₂ i))
          * (bornDistribution w₁ i - bornDistribution w₂ i)
      = finiteKLDivergence (bornDistribution w₁) (bornDistribution w₂)
        + finiteKLDivergence (bornDistribution w₂) (bornDistribution w₁) :=
  entropyProduction_eq_jeffreys _ _ (fun i => bornDistribution_pos w₁ i (h₁ i))
    (fun i => bornDistribution_pos w₂ i (h₂ i))

/-- **The Jeffreys divergence of the Born distributions is non-negative** `0 ≤ D_KL(p‖q) + D_KL(q‖p)` — the second
law (H-theorem) restated as the non-negativity of the symmetrized relative entropy between two SJ Born diagonals,
vanishing exactly at detailed balance (`p = q`). -/
lemma decoherenceFunctional_jeffreys_nonneg [Fintype ι] (w₁ w₂ : ι → ℂ)
    (h₁ : ∀ i, w₁ i ≠ 0) (h₂ : ∀ i, w₂ i ≠ 0) :
    0 ≤ finiteKLDivergence (bornDistribution w₁) (bornDistribution w₂)
        + finiteKLDivergence (bornDistribution w₂) (bornDistribution w₁) := by
  rw [← decoherenceFunctional_entropyProduction_eq_jeffreys w₁ w₂ h₁ h₂]
  exact decoherenceFunctional_hTheorem w₁ w₂ h₁ h₂

end Physlib.Thermodynamics.DecoherenceFunctionalBornHTheorem
