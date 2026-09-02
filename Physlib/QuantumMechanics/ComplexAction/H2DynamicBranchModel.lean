/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The `H₂` STO-3G dynamic branch model: entropic selection of the bonding channel

The minimal concrete chemistry benchmark for CAT/EPT entropic time, from the quantum-computational-chemistry
review's `H₂` example (McArdle et al, Rev. Mod. Phys. **92** (2020) 015003, arXiv:1808.10402 §VIII). The
Hartree–Fock state `|Ψ_HF⟩ = |0011⟩` and the simplified UCCSD operator `U = e^{−iθ X₃X₂X₁Y₀}` give a
**two-branch dynamical transition** between the bonding `|0011⟩` and antibonding `|1100⟩` configurations:

  `U|0011⟩ = cos θ |0011⟩ + sin θ |1100⟩`.

The CAT/EPT extension attenuates the antibonding branch by the entropic weight `e^{−S_I/ħ}`
(`QuantumChemistry.TimeEvolution.entropicWeight`):

  `|ψ(θ,τ)⟩ = cos θ |0011⟩ + e^{−S_I(τ)/ħ} sin θ |1100⟩`.

* **§A — the branch weights.** `bondingWeight = cos²θ`, `antibondingWeight = e^{−2S_I/ħ} sin²θ`, and the total
  entropic norm `h2BranchNorm`.
* **§B — entropic selection.** The norm is **unit** in the reversible limit (`h2_norm_reversible`,
  `S_I = 0`, standard unitary UCCSD), **sub-normalized** under entropy (`h2_norm_le_one`); the **antibonding
  branch is suppressed** (`h2_antibonding_le_sin`) and **decreases monotonically with `S_I`**
  (`h2_antibonding_antitone`) — the entropic mechanism by which the bonding channel is physically selected.
* **§C — the main result** `h2_dynamic_branch_model`.

**Honest layering.** Proven: the real-analytic branch-weight identities and inequalities (unit norm at zero
entropy, sub-normalization, monotone antibonding suppression) on the two real amplitudes `(cos θ,
e^{−S_I/ħ} sin θ)`. The four-qubit state vectors `|0011⟩, |1100⟩`, the Pauli-string Hamiltonian, and the
unitary `e^{−iθ X₃X₂X₁Y₀}` are the named operational content; here only the (sub-normalized) amplitude weights
are modelled — the part that encodes the entropic selection.

## References

* S. McArdle, S. Endo, A. Aspuru-Guzik, S. C. Benjamin, X. Yuan, *Quantum computational chemistry*, Rev. Mod.
  Phys. **92** (2020) 015003, doi:10.1103/RevModPhys.92.015003; arXiv:1808.10402 [quant-ph] §VIII — the `H₂`
  STO-3G Hamiltonian, `|Ψ_HF⟩=|0011⟩`, `U|0011⟩ = cos θ|0011⟩ + sin θ|1100⟩`. `Physlib`
  (`QuantumChemistry.TimeEvolution.entropicWeight`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.H2DynamicBranchModel

/-- The entropic weight is non-negative (it is a real exponential). -/
lemma entropicWeight_nonneg (SI ħ : ℝ) : 0 ≤ entropicWeight SI ħ := by
  unfold entropicWeight; positivity


/-- **The bonding-branch weight** `|cos θ|²` (the `|0011⟩` configuration). -/
noncomputable def bondingWeight (θ : ℝ) : ℝ := Real.cos θ ^ 2

/-- **The antibonding-branch weight** `e^{−2S_I/ħ} sin²θ` (the `|1100⟩` configuration, attenuated by the
entropic weight). -/
noncomputable def antibondingWeight (θ SI ħ : ℝ) : ℝ := entropicWeight SI ħ ^ 2 * Real.sin θ ^ 2

/-- The **total entropic norm** `‖ψ(θ,S_I)‖² = cos²θ + e^{−2S_I/ħ} sin²θ` of the two-branch state. -/
noncomputable def h2BranchNorm (θ SI ħ : ℝ) : ℝ := bondingWeight θ + antibondingWeight θ SI ħ


/-- **[Reversible UCCSD has unit norm]** `S_I = 0 ⇒ ‖ψ‖² = cos²θ + sin²θ = 1` — the standard norm-preserving
unitary `H₂` transition. -/
lemma h2_norm_reversible (θ ħ : ℝ) : h2BranchNorm θ 0 ħ = 1 := by
  unfold h2BranchNorm bondingWeight antibondingWeight
  rw [entropicWeight_zero, one_pow, one_mul, add_comm]
  exact Real.sin_sq_add_cos_sq θ

/-- **[The antibonding branch is suppressed]** `e^{−2S_I/ħ} sin²θ ≤ sin²θ` for `S_I ≥ 0`, `ħ > 0` — the
entropic weight attenuates the `|1100⟩` amplitude. -/
lemma h2_antibonding_le_sin (θ SI ħ : ℝ) (hSI : 0 ≤ SI) (hħ : 0 < ħ) :
    antibondingWeight θ SI ħ ≤ Real.sin θ ^ 2 := by
  unfold antibondingWeight
  exact mul_le_of_le_one_left (sq_nonneg _)
    (pow_le_one₀ (entropicWeight_nonneg SI ħ) (entropicWeight_le_one SI ħ hSI hħ))

/-- **[Entropy sub-normalizes the state]** `‖ψ‖² ≤ 1` for `S_I ≥ 0`, `ħ > 0` — amplitude is lost to the
entropic channel (the operational `d/dt‖ψ‖² ≤ 0`). -/
lemma h2_norm_le_one (θ SI ħ : ℝ) (hSI : 0 ≤ SI) (hħ : 0 < ħ) : h2BranchNorm θ SI ħ ≤ 1 := by
  unfold h2BranchNorm bondingWeight
  have hab := h2_antibonding_le_sin θ SI ħ hSI hħ
  have hcs := Real.sin_sq_add_cos_sq θ
  linarith

/-- **[Monotone entropic branch selection]** the antibonding weight `e^{−2S_I/ħ} sin²θ` is **antitone in
`S_I`** (for `ħ > 0`): as entropy is produced the `|1100⟩` channel is progressively suppressed and the bonding
`|0011⟩` channel is selected. -/
lemma h2_antibonding_antitone (θ ħ : ℝ) (hħ : 0 < ħ) {S1 S2 : ℝ} (h : S1 ≤ S2) :
    antibondingWeight θ S2 ħ ≤ antibondingWeight θ S1 ħ := by
  unfold antibondingWeight
  have hle := entropicWeight_antitone ħ hħ h
  have h0 := entropicWeight_nonneg S2 ħ
  gcongr


/-- **[The `H₂` dynamic branch model]** the minimal CAT/EPT entropic-time chemistry benchmark: the two-branch
state `cos θ |0011⟩ + e^{−S_I/ħ} sin θ |1100⟩` is **unit-normed in the reversible limit** (`S_I = 0`, standard
UCCSD), **sub-normalized under entropy production** (`‖ψ‖² ≤ 1`), with the **antibonding branch suppressed**
(`e^{−2S_I/ħ} sin²θ ≤ sin²θ`) — entropic selection of the bonding channel. -/
lemma h2_dynamic_branch_model (θ ħ : ℝ) (hħ : 0 < ħ) {SI : ℝ} (hSI : 0 ≤ SI) :
    h2BranchNorm θ 0 ħ = 1
      ∧ h2BranchNorm θ SI ħ ≤ 1
      ∧ antibondingWeight θ SI ħ ≤ Real.sin θ ^ 2 :=
  ⟨h2_norm_reversible θ ħ, h2_norm_le_one θ SI ħ hSI hħ, h2_antibonding_le_sin θ SI ħ hSI hħ⟩

end Physlib.QuantumMechanics.ComplexAction.H2DynamicBranchModel

end
