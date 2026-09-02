/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementComputationCommunication
public import Physlib.Thermodynamics.KullbackLeiblerInformationGain

/-!
# Quantum Darwinism is the communication side of measurement

Quantum Darwinism (`SciamaAdSCPTQuantumDarwinism`) says the environment **broadcasts** many redundant copies of
the einselected pointer state so observers learn it indirectly — the environment as a *communication channel*.
The repo already carries the "measurement as information communication" content, and this module ties the two
together by reuse.

A measurement splits (Caticha, complex-action `Re/Im`, `CatichaMeasurementComputationCommunication`) into a
**computation** part `Re(S)` — the Born-rule readout / decoherence / einselection — and a **communication** part
`Im(S)` — the unitary device `Û_M`, information-preserving.  Quantum Darwinism *is* the communication side: the
environment faithfully and completely broadcasts the pointer-state information, and the observer's information
gain about the system via a fragment is the **mutual information** (`KullbackLeiblerInformationGain`).

* **§1 — the acquired information is the mutual information** (`measurement_info_gain_is_mutual_information`,
  reusing `finiteInformationGain_eq_mutualInformation`): the observer's information *gain* about the system from
  the environment channel is exactly `I(S:F)` — measurement is information communication.
* **§2 — the communication channel is faithful** (`communication_channel_faithful`, reusing
  `communication_preserves_norm`): the unitary broadcast preserves the norm — no information is lost, so the
  redundant copies are faithful (repeatability).
* **§3 — the broadcast is complete** (`broadcast_outcome_complete`, *new*): the outcome distribution read off the
  *communicated* state `Û_M ψ` in the broadcast basis sums to `‖ψ‖²` — the environment carries a complete,
  normalized copy of the pointer-state Born distribution.
* **§4 — readout and broadcast access the same information** (`readout_equals_broadcast`, reusing
  `computation_communication_duality`): the direct Born readout (computation / einselection) and the
  environmental broadcast (communication / Darwinism) give the same probabilities — the redundant records carry
  exactly the pointer-state information.
* `darwinism_is_faithful_complete_communication` — the synthesis: quantum Darwinism is the faithful, complete
  communication of the pointer-state information carried by the same measurement whose computation side is the
  einselection.

Honest scope: exact reuse of the Caticha computation/communication duality and the KL information-gain =
mutual-information identity; the one new step is the completeness of the broadcast distribution.  Quantum
Darwinism = communication side; einselection/decoherence = computation side; both access the same information.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMeasurementCommunicationDarwinism

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementComputationCommunication
open Physlib.Thermodynamics.KullbackLeiblerInformationGain
open scoped InnerProductSpace

/-! ## §1. The acquired information is the mutual information -/

/-- **[Measurement is information communication] the information gain is the mutual information.**  The observer's
information *gain* about the system `X` from the environment fragment `Y`, relative to the system marginal, is
exactly the mutual information `I(X:Y)` (KL of the joint from the product of marginals) — the observer acquires
the system's state indirectly, through the environment as a communication channel. -/
theorem measurement_info_gain_is_mutual_information {X Y : Type*} [Fintype X] [Fintype Y] (joint : X → Y → ℝ) :
    finiteKLDivergence₂ joint (fun x y => xMarginal joint x * yMarginal joint y)
      = finiteMutualInformation joint :=
  finiteInformationGain_eq_mutualInformation joint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## §2. The communication channel is faithful -/

/-- **[The communication channel is faithful] `‖Û_M ψ‖ = ‖ψ‖`.**  The unitary broadcast preserves the norm, so
no information is lost in communication — the environment's redundant copies are faithful (the repeatability
that quantum Darwinism requires). -/
theorem communication_channel_faithful (U : E →ₗᵢ[ℂ] E) (ψ : E) : ‖U ψ‖ = ‖ψ‖ :=
  communication_preserves_norm U ψ

/-! ## §3. The broadcast is complete -/

/-- **[The broadcast carries a complete copy] `∑_k |⟨Û_M s_k | Û_M ψ⟩|² = ‖ψ‖²`.**  The outcome distribution read
off the *communicated* (broadcast) state in the broadcast basis is normalized — the environment carries a
complete copy of the pointer-state Born distribution, not a partial one. -/
theorem broadcast_outcome_complete {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (U : E →ₗᵢ[ℂ] E) (ψ : E) :
    ∑ k, ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have hcopy : (∑ k, ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2) = ∑ k, bornOutcome b ψ k :=
    Finset.sum_congr rfl (fun k _ => computation_communication_duality b U ψ k)
  rw [hcopy]
  exact born_outcome_normalized b ψ

/-! ## §4. Readout and broadcast access the same information -/

/-- **[Readout equals broadcast] `|⟨Û_M s_k | Û_M ψ⟩|² = p_k`.**  The direct Born readout (computation /
einselection) and the environmental broadcast (communication / Darwinism) give the same outcome probability —
the redundant environmental records carry exactly the pointer-state information. -/
theorem readout_equals_broadcast {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (U : E →ₗᵢ[ℂ] E) (ψ : E)
    (k : ι) :
    ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2 = bornOutcome b ψ k :=
  computation_communication_duality b U ψ k

/-- **[Quantum Darwinism is faithful, complete communication]** — the environmental broadcast is norm-preserving
(faithful), its outcome distribution is normalized (complete), and it gives the same probabilities as the direct
readout: quantum Darwinism is the communication side of the very measurement whose computation side is the
einselection. -/
theorem darwinism_is_faithful_complete_communication {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (U : E →ₗᵢ[ℂ] E) (ψ : E) :
    ‖U ψ‖ = ‖ψ‖
      ∧ (∑ k, ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2) = ‖ψ‖ ^ 2
      ∧ (∀ k, ‖⟪U (b k), U ψ⟫_ℂ‖ ^ 2 = bornOutcome b ψ k) :=
  ⟨communication_preserves_norm U ψ, broadcast_outcome_complete b U ψ,
    fun k => computation_communication_duality b U ψ k⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMeasurementCommunicationDarwinism

end
