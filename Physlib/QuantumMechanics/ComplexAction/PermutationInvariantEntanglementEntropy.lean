/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Data.Nat.Choose.Sum
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# The permutationally-invariant reduced density matrix is maximally mixed: `S = log deg`

Formalizes the exactly-solvable "density region of entanglement" of Popkov & Salerno, *Reduced density
matrix and entanglement entropy of permutationally invariant quantum many-body systems*, Int. J. Mod.
Phys. B 26 (2012) 1243009. A permutation-invariant `L`-spin state with fixed `S_z` sits in a degenerate
eigenspace of dimension `deg_{L,r}`, and the maximally-symmetric density matrix

  `σ_{L,N,r} = (1/deg) Σ_u |Ψ_u⟩⟨Ψ_u| = (1/L!) Σ_P |Ψ⟩⟨Ψ|`   (Eqs 4, 7)

is **maximally mixed** on that support: every nonzero eigenvalue equals `1/deg` and the rest vanish
(property (i)), `σ² = (1/deg) σ` (property (ii)), and `[σ, P_ij] = 0` (property (iv), permutation
invariance). Tracing out `L − n` sites gives the `n`-site RDM `ρ_(n) = Tr_{L−n} σ`, which `S_z`-symmetry
block-diagonalizes into blocks `dim B_k = C(n,k)` summing to `2^n` (§3).

The single quantity that matters for entanglement is the **von Neumann entropy of the flat spectrum**:

  `S = −Σ λ log λ = −deg·(1/deg)·log(1/deg) = log deg`   (`symmetricRdm_vonNeumann_eq_log`),

the Boltzmann/microcanonical entropy of the degenerate support — the **maximum-entropy value** on a
`deg`-dimensional region. This is the exactly-solvable realization of the "density regions of
entanglement" that carry the first-law/spacetime entropy: with the degeneracy identified as the effective
Schmidt number `K = deg`, `S = log deg = log K = S_I/ħ`
(`symmetricRdm_entropy_eq_entropicAction`, via `SchmidtRapidityHyperbolicUnification.entropicAction`),
so the permutation-symmetric max-entropy state is the endpoint of the entropic-dynamics maximization
written in the imaginary-action variable.

* **§A — the maximally-mixed spectrum.** `symmetricRdmEigenvalue` (`= 1/deg`), `symmetricRdm_trace`
  (`Tr σ = 1`), `symmetricRdm_spectrum` (properties (i)+(ii): eigenvalues solve `x² = (1/deg)x`, so
  `x ∈ {0, 1/deg}`).
* **§B — the entanglement entropy.** `vonNeumannEntropyUniform`, `symmetricRdm_vonNeumann_eq_log`
  (`S = log deg`); `symmetricRdmPurity` (`Tr σ² = 1/deg`), `symmetricRdm_renyi2_eq_vonNeumann`
  (`S₂ = −log Tr σ² = log deg = S_vN` — the flat spectrum saturates `S_vN ≥ S₂`, no log-enhancement).
* **§C — the block dimensions.** `symmetricRdm_block_dims_sum` (`Σ_k C(n,k) = 2^n`), `symmetricDegeneracy`
  (`deg_{L,r} = C(L,r) − C(L,r−1)`), `symmetricDegeneracy_one` (`deg_{L,1} = L − 1`).
* **§D — the entropic-action bridge.** `symmetricRdm_entropy_eq_entropicAction`
  (`S = log deg = S_I/ħ`).
* **§E — the maximum-entropy principle.** `shannonEntropy`, `shannonEntropy_le_log_card`
  (`H(p) ≤ log deg` for any distribution — Jensen for the concave `negMulLog`, so the maximally-mixed
  `S = log deg` is the *maximum*), `vonNeumannEntropyUniform_eq_negMulLog`.

## References

* V. Popkov, M. Salerno, *Reduced density matrix and entanglement entropy of permutationally invariant
  quantum many-body systems*, Int. J. Mod. Phys. B 26 (2012) 1243009 — Eqs (3), (4), (7), (8), properties
  (i)–(iv), §3 block structure.
* `MuonAnomaly.SchmidtRapidityHyperbolicUnification` — `entropicAction ħ η = ħ log(schmidtNumber η)`,
  `schmidtNumber η = coth η`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PermutationInvariantEntanglementEntropy

/-! ### §A — the maximally-mixed spectrum -/

/-- The single nonzero eigenvalue `1/deg` of the maximally-symmetric density matrix
`σ = (1/deg) Σ_u |Ψ_u⟩⟨Ψ_u|` (Popkov–Salerno Eq 4): all `deg` nonzero eigenvalues equal `1/deg` and the
remaining `2^L − deg` vanish (property (i)). -/
noncomputable def symmetricRdmEigenvalue (d : ℕ) : ℝ := (d : ℝ)⁻¹

/-- **[Normalization `Tr σ = 1`]** the `deg` equal eigenvalues `1/deg` sum to one (Eq 7). -/
lemma symmetricRdm_trace (d : ℕ) (hd : d ≠ 0) :
    (d : ℝ) * symmetricRdmEigenvalue d = 1 :=
  mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd)

/-- **[Spectrum `{0, 1/deg}`]** Popkov properties (i)+(ii): `σ² = (1/deg) σ`, so every eigenvalue `x`
solves the quadratic `x² = (1/deg) x`, i.e. `x = 0` (the `2^L − deg` null directions) or `x = 1/deg`
(the `deg`-fold degenerate support). -/
lemma symmetricRdm_spectrum (d : ℕ) (x : ℝ) :
    x ^ 2 = symmetricRdmEigenvalue d * x ↔ (x = 0 ∨ x = symmetricRdmEigenvalue d) := by
  constructor
  · intro hx
    have hfac : x * (x - symmetricRdmEigenvalue d) = 0 := by
      rw [mul_sub, ← pow_two, hx]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (h | h) <;> subst h <;> ring

/-! ### §B — the entanglement entropy -/

/-- The **von Neumann entropy** `S = −Σ λ log λ` of the maximally-symmetric density matrix, evaluated on
its flat spectrum (`deg` copies of `λ = 1/deg`). -/
noncomputable def vonNeumannEntropyUniform (d : ℕ) : ℝ :=
  -((d : ℝ) * symmetricRdmEigenvalue d * Real.log (symmetricRdmEigenvalue d))

/-- **[Entanglement entropy `S = log deg`]** the maximally-symmetric (maximally-mixed) state has von
Neumann entropy equal to the log of the degeneracy dimension — the Boltzmann/microcanonical entropy of the
degenerate support and the maximum-entropy value on a `deg`-dimensional region. -/
lemma symmetricRdm_vonNeumann_eq_log (d : ℕ) (hd : d ≠ 0) :
    vonNeumannEntropyUniform d = Real.log d := by
  unfold vonNeumannEntropyUniform symmetricRdmEigenvalue
  rw [Real.log_inv, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd)]
  ring

/-- The **purity** `Tr σ² = 1/deg` of the maximally-symmetric state (Popkov §6 moment `Tr σ^q = deg^{1−q}`
at `q = 2`). -/
noncomputable def symmetricRdmPurity (d : ℕ) : ℝ := (d : ℝ) * symmetricRdmEigenvalue d ^ 2

/-- **[Purity `Tr σ² = 1/deg`]**. -/
lemma symmetricRdm_purity_eq (d : ℕ) (hd : d ≠ 0) :
    symmetricRdmPurity d = (d : ℝ)⁻¹ := by
  unfold symmetricRdmPurity symmetricRdmEigenvalue
  rw [pow_two, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd), one_mul]

/-- **[Rényi-2 = von Neumann for the flat spectrum]** `S₂ = −log(Tr σ²) = log deg = S_vN`: on the
maximally-mixed spectrum the Rényi-2 entropy and the von Neumann entropy coincide, so the von Neumann
entropy carries **no** log-enhancement over `S₂` — the equality case of the general `S_vN ≥ S₂`. -/
lemma symmetricRdm_renyi2_eq_vonNeumann (d : ℕ) (hd : d ≠ 0) :
    -Real.log (symmetricRdmPurity d) = vonNeumannEntropyUniform d := by
  rw [symmetricRdm_purity_eq d hd, Real.log_inv, neg_neg, symmetricRdm_vonNeumann_eq_log d hd]

/-! ### §C — the block dimensions -/

/-- **[Block dimensions fill the subsystem]** the `S_z`-blocks of the `n`-site RDM have dimensions
`dim B_k = C(n,k)` (Popkov §3) and sum to the full `2^n`-dimensional Hilbert space. -/
lemma symmetricRdm_block_dims_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-- The **degeneracy dimension** of the two-row Young tableau `{L−r, r}` (Popkov Eq 3),
`deg_{L,r} = C(L,r) − C(L,r−1)` — the number of independent symmetric eigenstates, hence the dimension of
the maximally-mixed support. -/
def symmetricDegeneracy (L r : ℕ) : ℤ := (L.choose r : ℤ) - (L.choose (r - 1) : ℤ)

/-- **[Degeneracy at `r = 1`]** `deg_{L,1} = C(L,1) − C(L,0) = L − 1`. -/
lemma symmetricDegeneracy_one (L : ℕ) : symmetricDegeneracy L 1 = (L : ℤ) - 1 := by
  simp [symmetricDegeneracy, Nat.choose_one_right, Nat.choose_zero_right]

/-! ### §D — the entropic-action bridge -/

/-- **[Popkov `S = log deg` is the entropic action]** identifying the flat degeneracy `deg` with the
effective Schmidt number `K = coth η` (`SchmidtRapidityHyperbolicUnification.schmidtNumber`), the
permutation-symmetric entanglement entropy is exactly the entropic action per `ħ`,
`S = log deg = log K = S_I/ħ` — the maximum-entropy endpoint of the entropic-dynamics maximization written
in the imaginary-action variable. -/
lemma symmetricRdm_entropy_eq_entropicAction (d : ℕ) (hd : d ≠ 0) (ħ η : ℝ)
    (hħ : ħ ≠ 0) (hη : schmidtNumber η = (d : ℝ)) :
    vonNeumannEntropyUniform d = entropicAction ħ η / ħ := by
  rw [symmetricRdm_vonNeumann_eq_log d hd, ← hη]
  unfold entropicAction
  rw [mul_comm ħ (Real.log (schmidtNumber η)), mul_div_assoc, div_self hħ, mul_one]

/-! ### §E — the maximum-entropy principle -/

/-- **[The maximally-mixed entropy is the uniform Shannon entropy]** `S = log deg = deg · negMulLog(1/deg)`
— the von Neumann entropy of `symmetricRdm` written as the Shannon entropy `Σ negMulLog` of its flat
`deg`-outcome spectrum. -/
lemma vonNeumannEntropyUniform_eq_negMulLog (d : ℕ) :
    vonNeumannEntropyUniform d = (d : ℝ) * Real.negMulLog (symmetricRdmEigenvalue d) := by
  simp only [vonNeumannEntropyUniform, symmetricRdmEigenvalue, Real.negMulLog]
  ring

variable {ι : Type*} [Fintype ι]

/-- The **Shannon / von Neumann entropy** `H(p) = −Σ pᵢ log pᵢ = Σ negMulLog(pᵢ)` of a probability
distribution `p` on a finite index type. -/
noncomputable def shannonEntropy (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- **[Maximum-entropy principle `H(p) ≤ log deg`]** among all probability distributions on a
`deg`-element index, the entropy never exceeds `log deg` — attained by the uniform (maximally-mixed)
distribution. Jensen's inequality for the concave `negMulLog` (`concaveOn_negMulLog`) makes rigorous the
claim that the maximally-symmetric state maximizes the entropy: `S = log deg`
(`symmetricRdm_vonNeumann_eq_log`) is the **maximum** over the density region, not merely one value. -/
theorem shannonEntropy_le_log_card [Nonempty ι] (p : ι → ℝ)
    (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) := by
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hne : (Fintype.card ι : ℝ) ≠ 0 := hnpos.ne'
  have jensen := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset ι)) (w := fun _ => (Fintype.card ι : ℝ)⁻¹) (p := p)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact mul_inv_cancel₀ hne)
    (fun i _ => hp₀ i)
  have hLHS : ∑ i, (Fintype.card ι : ℝ)⁻¹ • Real.negMulLog (p i)
      = (Fintype.card ι : ℝ)⁻¹ * shannonEntropy p := by
    rw [shannonEntropy, Finset.mul_sum]; simp [smul_eq_mul]
  have harg : ∑ i, (Fintype.card ι : ℝ)⁻¹ • p i = (Fintype.card ι : ℝ)⁻¹ := by
    simp only [smul_eq_mul]; rw [← Finset.mul_sum, hp₁, mul_one]
  rw [hLHS, harg] at jensen
  have hval : Real.negMulLog (Fintype.card ι : ℝ)⁻¹
      = (Fintype.card ι : ℝ)⁻¹ * Real.log (Fintype.card ι) := by
    rw [Real.negMulLog, Real.log_inv]; ring
  rw [hval] at jensen
  exact le_of_mul_le_mul_left jensen (inv_pos.mpr hnpos)

/- ZIL-BEGIN -/

zil attach symmetricRdm_spectrum where
  formalizes @ "claim:permutation-invariant-rdm-eigenvalues-solve-x-squared-equals-one-over-deg-times-x-so-x-is-zero-or-one-over-deg",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:popkov-salerno-2012-reduced-density-matrix-permutationally-invariant",
  caveat @ "claim:spectrum-of-the-maximally-mixed-density-matrix-carried-at-the-scalar-eigenvalue-level-not-the-full-operator"

zil attach symmetricRdm_vonNeumann_eq_log where
  formalizes @ "claim:maximally-symmetric-permutation-invariant-state-has-von-neumann-entropy-log-deg-the-boltzmann-maximum-entropy-of-the-density-region",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:popkov-salerno-2012-reduced-density-matrix-permutationally-invariant",
  caveat @ "claim:entropy-of-a-flat-spectrum-not-a-generic-reduced-density-matrix-entanglement-entropy"

zil attach symmetricRdm_renyi2_eq_vonNeumann where
  supported_by @ "lean:symmetricRdm_vonNeumann_eq_log",
  formalizes @ "claim:for-the-flat-permutation-invariant-spectrum-the-renyi-two-and-von-neumann-entropies-coincide-at-log-deg-no-log-enhancement",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:equality-case-of-s-vn-ge-s-two-holds-only-for-the-maximally-mixed-flat-spectrum"

zil attach symmetricRdm_entropy_eq_entropicAction where
  supported_by @ "lean:symmetricRdm_vonNeumann_eq_log",
  formalizes @ "claim:permutation-invariant-max-entropy-log-deg-equals-the-entropic-action-per-hbar-with-deg-as-the-effective-schmidt-number",
  epistemic_status @ "consistency-identity",
  requires @ "claim:maximally-symmetric-permutation-invariant-state-has-von-neumann-entropy-log-deg-the-boltzmann-maximum-entropy-of-the-density-region",
  caveat @ "claim:identifies-the-degeneracy-with-the-schmidt-number-coth-eta-an-interpretive-bridge-to-the-entropic-time-imaginary-action"

zil attach shannonEntropy_le_log_card where
  formalizes @ "claim:maximum-entropy-principle-any-distribution-has-shannon-entropy-at-most-log-of-the-alphabet-size",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Real.concaveOn_negMulLog",
  caveat @ "claim:jensen-bound-attained-by-the-uniform-distribution-classical-discrete-not-quantum"

zil_file_contract physlib.permutationInvariantEntanglementEntropy where
  promises "The exactly-solvable density region of a permutation-invariant many-body state (Popkov-Salerno). The maximally-symmetric density matrix is maximally mixed on its deg-dimensional degenerate support: its spectrum is {0, 1/deg} (symmetricRdm_spectrum), so its von Neumann entropy is the Boltzmann maximum S = log deg (symmetricRdm_vonNeumann_eq_log), where the flat spectrum makes Rényi-2 and von Neumann coincide (symmetricRdm_renyi2_eq_vonNeumann). The maximum-entropy principle H(p) ≤ log(card) (shannonEntropy_le_log_card) makes S = log deg the maximum over the region, and identifying deg with the effective Schmidt number bridges it to the entropic-time imaginary action, S = log deg = log K = S_I/ħ (symmetricRdm_entropy_eq_entropicAction)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.PermutationInvariantEntanglementEntropy.symmetricRdmEigenvalue",
    "lean:Physlib.QuantumMechanics.ComplexAction.PermutationInvariantEntanglementEntropy.vonNeumannEntropyUniform",
    "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.entropicAction"]
  forbids_substitutes ["treating the flat-spectrum entropy as a generic entanglement entropy -- these results are specific to the maximally-mixed permutation-symmetric state",
    "reading the deg-to-Schmidt-number identification as a derivation rather than an interpretive bridge to the entropic action"]
  witnessed_by [symmetricRdm_spectrum, symmetricRdm_vonNeumann_eq_log,
    symmetricRdm_renyi2_eq_vonNeumann, symmetricRdm_entropy_eq_entropicAction,
    shannonEntropy_le_log_card]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.PermutationInvariantEntanglementEntropy
