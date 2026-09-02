/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.L2KetAdapter
public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Entropy.DPI
public import QuantumInfo.Operators.Unitary
public import QuantumInfo.States.Entanglement
public import QuantumInfo.ClassicalInfo.Entropy
meta import Zil

/-!
# Reversible and irreversible dynamics as one channel layer

Reversible unitary evolution and irreversible GKLS evolution are one channel
layer on density operators — bundled `CPTPMap`s, not raw functions.

* A channel's entropy production is the change in von Neumann entropy it causes;
  `IsEntropyPreserving` is the property of causing none.
* A **genuinely reversible** channel is `CPTPMap.IsUnitary`; every unitary channel
  is entropy-preserving (`isUnitary_isEntropyPreserving`).  Entropy preservation
  is the *necessary* condition, not the full characterization of unitarity — the
  two are not identified.
* The **replacement** channel to the maximally mixed state has positive entropy
  production, so it is not entropy-preserving: the mixing sector is distinct.
* The **irreversibility law** shared by every channel is data processing —
  relative entropy contracts under any `CPTPMap` (`cptp_qRelativeEnt_le`), with
  the unitary reversible channels the equality case.  The repository's Lindblad
  `oneLevelChannel` and the Spohn free-energy H-theorem are the concrete GKLS
  semigroup realization; this module bridges to that law.
* A Koopman permutation step is the unitary channel `CPTPMap.ofEquiv`, hence
  entropy-preserving; generic non-permutation channels are not covered here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MState

namespace Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction

open Physlib.QuantumMechanics.KoopmanQuantization
open Physlib.QuantumMechanics.L2KetAdapter

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The **entropy production** of a channel on a state: the change in von Neumann
entropy it causes. -/
def entropyProduction (Φ : CPTPMap d d) (ρ : MState d) : ℝ :=
  Sᵥₙ (Φ ρ) - Sᵥₙ ρ

/-- A channel **preserves entropy** if it never changes the von Neumann entropy. -/
def IsEntropyPreserving (Φ : CPTPMap d d) : Prop :=
  ∀ ρ, entropyProduction Φ ρ = 0

/-- **A genuinely reversible (unitary) channel preserves entropy.**  This is the
necessary direction only: entropy preservation does not by itself imply
unitarity. -/
@[zil_level physical_theorem]
theorem isUnitary_isEntropyPreserving (Λ : CPTPMap d d) (h : Λ.IsUnitary) :
    IsEntropyPreserving Λ := by
  obtain ⟨U, hU⟩ := (CPTPMap.IsUnitary_iff_uConj Λ).mp h
  intro ρ
  unfold entropyProduction
  rw [hU ρ, Sᵥₙ_U_conj]
  ring

/-- The unitary channel `CPTPMap.ofUnitary U` preserves entropy. -/
theorem ofUnitary_isEntropyPreserving (U : 𝐔[d]) :
    IsEntropyPreserving (CPTPMap.ofUnitary U) :=
  isUnitary_isEntropyPreserving _ ⟨U, rfl⟩

/-- **A Koopman permutation step, as the unitary channel `CPTPMap.ofEquiv`,
preserves entropy.** -/
@[zil_level physical_theorem]
theorem ofEquiv_isEntropyPreserving (σ : d ≃ d) :
    IsEntropyPreserving (CPTPMap.ofEquiv σ) :=
  isUnitary_isEntropyPreserving _ (CPTPMap.IsUnitary_equiv σ)

/-- **The mixing sector is distinct**: the replacement channel to the maximally
mixed state has positive entropy production on a pure input, so it does not
preserve entropy. -/
@[zil_level physical_theorem]
theorem replacement_not_isEntropyPreserving [Nonempty d] [Nontrivial d] :
    ¬ IsEntropyPreserving (CPTPMap.replacement (MState.uniform : MState d)) := by
  intro h
  have hprod := h (MState.pure (Ket.basis (Classical.arbitrary d)))
  unfold entropyProduction at hprod
  rw [CPTPMap.replacement_apply, Sᵥₙ_of_pure_zero, sub_zero] at hprod
  have huniform : Sᵥₙ (MState.uniform : MState d) = Real.log (Fintype.card d) := by
    rw [MState.uniform, Sᵥₙ_ofClassical ProbDistribution.uniform, Hₛ_uniform,
      Finset.card_univ]
  rw [huniform] at hprod
  exact (Real.log_pos (by exact_mod_cast Fintype.one_lt_card)).ne' hprod

/-! ## The GKLS irreversibility bridge -/

/-- **Data processing — the irreversibility law of the channel layer**: relative
entropy contracts under every `CPTPMap`.  Reversible unitary channels are the
equality case; the strictly-contracting channels are the irreversible GKLS
sector, concretely realized by the Lindblad `oneLevelChannel` and the Spohn
free-energy H-theorem in the repository's open-systems layer. -/
@[zil_level bridge_theorem]
theorem cptp_qRelativeEnt_le {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂] (Φ : CPTPMap d₁ d₂) (ρ σ : MState d₁) :
    𝐃(Φ ρ‖Φ σ) ≤ 𝐃(ρ‖σ) :=
  sandwichedRenyiEntropy_DPI_eq_one ρ σ Φ

/-! ## The reversible (pure-state) sector -/

/-- **A pure state has zero von Neumann entropy.** -/
theorem pureState_zero_vonNeumann {m : Type*} [Fintype m] [DecidableEq m]
    (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) :
    Sᵥₙ (pureOfL2State ψ h) = 0 :=
  Sᵥₙ_of_pure_zero _

/-- **The Koopman step keeps von Neumann entropy zero**: pure states stay pure,
so the permutation evolution produces no entropy — the reversible,
entropy-preserving behaviour of the Koopman steps. -/
@[zil_level physical_theorem]
theorem koopmanStep_zero_entropyProduction {m : Type*} [Fintype m] [DecidableEq m]
    (σ : m ≃ m) (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) :
    Sᵥₙ (pureOfL2State (koopmanStateStep σ ψ)
        (by rw [(koopmanStateStep σ).norm_map]; exact h))
      - Sᵥₙ (pureOfL2State ψ h) = 0 := by
  rw [pureState_zero_vonNeumann, pureState_zero_vonNeumann, sub_self]

zil attach isUnitary_isEntropyPreserving where
  formalizes @ "claim:a-genuinely-reversible-unitary-cptp-channel-preserves-von-neumann-entropy-necessary-direction-not-a-characterization",
  represents @ "lean:QuantumInfo.Channels.CPTPMap.IsUnitary",
  supported_by @ "lean:Sᵥₙ_U_conj"

zil attach ofEquiv_isEntropyPreserving where
  formalizes @ "claim:the-koopman-permutation-step-as-the-unitary-channel-ofEquiv-preserves-entropy",
  supported_by @ "lean:CPTPMap.ofEquiv"

zil attach replacement_not_isEntropyPreserving where
  formalizes @ "claim:the-replacement-to-maximally-mixed-channel-does-not-preserve-entropy-the-mixing-sector-is-distinct",
  supported_by @ "lean:CPTPMap.replacement_apply"

zil attach cptp_qRelativeEnt_le where
  formalizes @ "claim:relative-entropy-contracts-under-every-cptp-channel-the-data-processing-irreversibility-law-with-unitary-the-equality-case",
  intertwines @ "lean:sandwichedRenyiEntropy_DPI_eq_one",
  supported_by @ "lean:sandwichedRenyiEntropy_DPI_eq_one"

zil attach koopmanStep_zero_entropyProduction where
  formalizes @ "claim:the-koopman-step-produces-no-von-neumann-entropy-its-pure-states-stay-pure",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.pureOfL2State"

zil_file_contract physlib.channelEntropyProduction where
  promises "Reversible and irreversible dynamics unified as one bundled CPTPMap channel layer on density operators. Entropy production is the change in von Neumann entropy and IsEntropyPreserving the property of causing none; a genuinely reversible channel is CPTPMap.IsUnitary and every unitary channel is entropy-preserving (necessary direction, not a characterization); the replacement-to-maximally-mixed channel is not entropy-preserving so the mixing sector is distinct; and relative entropy contracts under every CPTPMap by data processing, with unitary channels the equality case and the Lindblad and Spohn open-systems layer the concrete irreversible GKLS realization. A Koopman permutation step is the unitary channel ofEquiv, hence entropy-preserving; generic non-permutation channels are not covered."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.L2KetAdapter.pureOfL2State",
    "lean:Physlib.QuantumMechanics.KoopmanQuantization.koopmanStateStep"
  ]
  forbids_substitutes [
    "identifying entropy preservation with unitarity as a full characterization",
    "putting irreversible evolution into a reversible-only unitary sector",
    "modelling channels as raw functions rather than bundled CPTPMaps",
    "claiming generic non-permutation channels are covered here"
  ]
  witnessed_by [
    isUnitary_isEntropyPreserving,
    ofEquiv_isEntropyPreserving,
    replacement_not_isEntropyPreserving,
    cptp_qRelativeEnt_le,
    koopmanStep_zero_entropyProduction
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.channelEntropyProduction

end Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction
