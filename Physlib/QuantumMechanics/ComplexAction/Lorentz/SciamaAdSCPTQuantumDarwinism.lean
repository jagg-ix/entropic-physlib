/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quantum Darwinism: objectivity of the einselected pointer states (Zurek, arXiv:2107.03378)

Decoherence einselects the pointer states (`SciamaAdSCPTConfinementColourDecoherence` — confinement einselects
the colour singlet; `SciamaAdSCPTTransportDecoherenceInterference` — the transport pointer basis).  **Quantum
Darwinism** goes beyond: the same monitoring environment that decoheres the system also imprints **many
redundant copies** of the pointer state in its fragments, so that many observers can find out the state
*independently and indirectly*, without disturbing it — this is how **objective classical reality** emerges.
This module formalizes the information-theoretic core (Zurek §"Quantum Darwinism, Classical Reality, and
Objective Existence"): the mutual information, the classical plateau, the information deficit, and the
redundancy.

* **§1 — mutual information and the plateau.**  `mutualInformation H_S H_F H_{SF} = H_S + H_F − H_{SF}` (Eq. 3);
  a **perfect record** (`H_{SF} = H_F`, the fragment determines the system) gives `I = H_S`
  (`perfect_record_mutualInformation`) — the plateau of the redundancy plot, where a fragment already carries
  *all* the classically accessible information `H_S`.
* **§2 — the information deficit and redundancy.**  `RevealsSystem I H_S δ := (1−δ)H_S ≤ I` (Eq. 5): a fragment
  reveals the system up to a tolerated deficit `δ`.  A perfect record reveals it for any `δ ≥ 0`
  (`perfect_record_reveals`).  The **redundancy** `R_δ = 1/f_δ` (Eq. 6) is the number of independent such
  records: `R_δ ≥ 1` (`redundancy_ge_one`), larger for smaller fragments (`redundancy_antitone`), and for `N`
  perfect copies `R = N` (`perfectCopy_redundancy_eq`).
* **§3 — objectivity from redundancy.**  `pointer_state_objective` — a perfect record reveals the system *and*
  the redundancy is `≥ 1`: the einselected pointer state is recorded and objectively accessible.  Large `R_δ`
  ("quantum spam") means many observers access it independently — the pointer state's objective existence.

So the arc's einselected pointer states (the colour singlet, the transport pointer basis) are exactly the ones
quantum Darwinism broadcasts redundantly into the environment; their Born weights `|α|², |β|²` are the
repo-derived weights of the branching state.  Objectivity = redundant records of the einselected states.

Honest scope: the exact information-theoretic identities (mutual information, the perfect-record plateau `I = H_S`,
the deficit condition, and `R_δ = 1/f_δ`) on abstract von-Neumann/Shannon entropies.  The full density-matrix
computation of `I(S:F_f)` for a specific model and the `logarithmic` weak `δ`-dependence of `R_δ` are Zurek's
content, contextualised here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumDarwinism

/-! ## §1. Mutual information and the classical plateau -/

/-- The quantum mutual information between the system `S` and an environment fragment `F` (Zurek Eq. 3):
`I(S:F) = H_S + H_F − H_{SF}`, in terms of the von-Neumann entropies. -/
def mutualInformation (HS HF HSF : ℝ) : ℝ := HS + HF - HSF

/-- **[The perfect-record plateau] `I = H_S`.**  When the fragment carries a *perfect* record of the system
(`H_{SF} = H_F`, so the fragment determines the system), the mutual information equals the full system entropy
`H_S` — the plateau of the redundancy plot: additional fragments only confirm what is already known. -/
theorem perfect_record_mutualInformation (HS HF : ℝ) : mutualInformation HS HF HF = HS := by
  unfold mutualInformation; ring

/-! ## §2. The information deficit and the redundancy -/

/-- **The information-deficit condition (Zurek Eq. 5)**: a fragment `reveals the system` up to a tolerated
deficit `δ` if its mutual information is at least `(1−δ)H_S`. -/
def RevealsSystem (I HS δ : ℝ) : Prop := (1 - δ) * HS ≤ I

/-- **[A perfect record reveals the system for any tolerated deficit]** — `I = H_S ≥ (1−δ)H_S` for `δ ≥ 0`,
`H_S ≥ 0`. -/
theorem perfect_record_reveals {HS HF δ : ℝ} (hδ : 0 ≤ δ) (hHS : 0 ≤ HS) :
    RevealsSystem (mutualInformation HS HF HF) HS δ := by
  unfold RevealsSystem
  rw [perfect_record_mutualInformation]
  nlinarith [mul_nonneg hδ hHS]

/-- The **redundancy** `R_δ = 1/f_δ` (Zurek Eq. 6): the number of independent fragments of the environment that
each carry a `(1−δ)`-record of the pointer state — how many observers can find out the system independently. -/
def redundancy (fδ : ℝ) : ℝ := 1 / fδ

/-- **[There is at least one record] `R_δ ≥ 1`** when the record fraction `f_δ ∈ (0, 1]`. -/
theorem redundancy_ge_one {fδ : ℝ} (h0 : 0 < fδ) (h1 : fδ ≤ 1) : 1 ≤ redundancy fδ := by
  unfold redundancy
  rw [le_div_iff₀ h0]
  linarith

/-- **[Smaller records ⇒ more redundancy]** — the redundancy is antitone in the record fraction `f_δ`. -/
theorem redundancy_antitone {f1 f2 : ℝ} (h0 : 0 < f1) (h : f1 ≤ f2) : redundancy f2 ≤ redundancy f1 :=
  one_div_le_one_div_of_le h0 h

/-- The redundancy of `N` perfect copies (each environment subsystem a full record, `f_δ = 1/N`). -/
def perfectCopyRedundancy (N : ℝ) : ℝ := redundancy (1 / N)

/-- **[N perfect copies give redundancy N]** `R = N` — the simplest quantum-Darwinism case, one full record per
environment subsystem. -/
theorem perfectCopy_redundancy_eq (N : ℝ) : perfectCopyRedundancy N = N := by
  unfold perfectCopyRedundancy redundancy
  rw [one_div_one_div]

/-! ## §3. Objectivity from redundancy -/

/-- **[The einselected pointer state is objective]** — a perfect environmental record reveals the system (`I =
H_S ≥ (1−δ)H_S`) *and* the redundancy is `≥ 1`: the einselected pointer state is recorded and independently
accessible.  Large redundancy `R_δ` ("quantum spam") means many observers access it independently and
indirectly — the objective existence of the pointer state (the colour singlet / transport pointer basis of the
decoherence arc). -/
theorem pointer_state_objective {HS HF δ fδ : ℝ} (hδ : 0 ≤ δ) (hHS : 0 ≤ HS)
    (h0 : 0 < fδ) (h1 : fδ ≤ 1) :
    RevealsSystem (mutualInformation HS HF HF) HS δ ∧ 1 ≤ redundancy fδ :=
  ⟨perfect_record_reveals hδ hHS, redundancy_ge_one h0 h1⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumDarwinism

end
