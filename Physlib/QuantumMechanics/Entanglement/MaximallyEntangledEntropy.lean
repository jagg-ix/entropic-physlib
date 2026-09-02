/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.States.Entanglement
public import QuantumInfo.Entropy.VonNeumann
public import Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
meta import Zil

/-!
# The von Neumann entropy composition of maximally entangled states

The information axiom of the relational-information programme states that for a
pure entangled bipartite state the *global* von Neumann entropy vanishes while the
*reduced* states carry positive entropy, and that the mutual information measures
the total correlation.  Every ingredient is a proved theorem in the
quantum-information layer (`Sᵥₙ_of_pure_zero`, the Schmidt symmetry
`Sᵥₙ_of_partial_eq`, the maximally-mixed entropy `log d`), but the *composed*
statement was never assembled.

This module assembles it once, generically, for any pure bipartite state whose
reduced state is maximally mixed
(`entropy_composition_of_traceRight_uniform`):

`Sᵥₙ ρ_AB = 0`,  `Sᵥₙ ρ_A = Sᵥₙ ρ_B = log d`,  `I(A:B) = 2 log d`,

and instantiates it at two carriers:

* the abstract maximally entangled state `Ket.MES d` on `d × d`; and
* the **explicit Bell singlet density matrix** `MState.pure bellPsiMinus`,
  `|Ψ⁻⟩ = (|01⟩ − |10⟩)/√2` — giving the genuine von Neumann mutual information
  `I(A:B) = 2 log 2` of a concrete `4 × 4` Bell density matrix.

The latter is the substantive von Neumann quantity, distinct from the parametric
input of the closed-form Bell-violation interpolator
`Entanglement.predictBellViolation`, whose Tsirelson input `log 2` is the
*single-party* reduced entropy `Sᵥₙ ρ_A`, one half of this mutual information.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling

namespace Physlib.QuantumMechanics.Entanglement

/-- **The maximally mixed state has entropy `log d`.** -/
theorem Sᵥₙ_uniform (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d] :
    Sᵥₙ (MState.uniform : MState d) = Real.log (Fintype.card d) := by
  rw [MState.uniform, Sᵥₙ_ofClassical ProbDistribution.uniform, Hₛ_uniform, Finset.card_univ]

/-- **The entropy composition of any pure bipartite state with a maximally mixed
reduced state.**  If the right-reduced state of a pure state on `d₁ × d₂` is the
maximally mixed state, then the global entropy vanishes, both reduced entropies are
`log d₁`, and the quantum mutual information is `2 log d₁`.  The reusable core: any
maximally entangled carrier inherits this exact information–correlation relation. -/
@[zil_level bridge_theorem]
theorem entropy_composition_of_traceRight_uniform {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Nonempty d₁] [Fintype d₂] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) (hred : (MState.pure ψ).traceRight = MState.uniform) :
    Sᵥₙ (MState.pure ψ) = 0
      ∧ Sᵥₙ (MState.pure ψ).traceRight = Real.log (Fintype.card d₁)
      ∧ Sᵥₙ (MState.pure ψ).traceLeft = Real.log (Fintype.card d₁)
      ∧ qMutualInfo (MState.pure ψ) = 2 * Real.log (Fintype.card d₁) := by
  have hAB : Sᵥₙ (MState.pure ψ) = 0 := Sᵥₙ_of_pure_zero _
  have hR : Sᵥₙ (MState.pure ψ).traceRight = Real.log (Fintype.card d₁) := by
    rw [hred, Sᵥₙ_uniform]
  have hL : Sᵥₙ (MState.pure ψ).traceLeft = Real.log (Fintype.card d₁) := by
    rw [Sᵥₙ_of_partial_eq, hR]
  refine ⟨hAB, hR, hL, ?_⟩
  unfold qMutualInfo
  rw [hL, hR, hAB]
  ring

/-! ## The abstract maximally entangled state -/

variable (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d]

/-- **The maximally entangled state's entropy composition** on `d × d`:
`S_AB = 0`, `S_A = S_B = log d`, `I(A:B) = 2 log d`. -/
@[zil_level bridge_theorem]
theorem MES_entropy_composition :
    Sᵥₙ (MState.pure (Ket.MES d)) = 0
      ∧ Sᵥₙ (MState.pure (Ket.MES d)).traceRight = Real.log (Fintype.card d)
      ∧ Sᵥₙ (MState.pure (Ket.MES d)).traceLeft = Real.log (Fintype.card d)
      ∧ qMutualInfo (MState.pure (Ket.MES d)) = 2 * Real.log (Fintype.card d) := by
  exact entropy_composition_of_traceRight_uniform (Ket.MES d) (traceRight_pure_MES d)

/-- **The maximally entangled state is genuinely entangled.** -/
@[zil_level physical_theorem]
theorem MES_isEntangled [Nontrivial d] : (Ket.MES d).IsEntangled :=
  Ket.MES_isEntangled

/-! ## The explicit Bell singlet density matrix `|Ψ⁻⟩⟨Ψ⁻|` -/

/-- **The entropy composition of the explicit Bell singlet density matrix**
`MState.pure bellPsiMinus`, `|Ψ⁻⟩ = (|01⟩ − |10⟩)/√2`: the global von Neumann
entropy vanishes, each reduced state is maximally mixed with entropy `log 2`, and
the genuine quantum mutual information is `I(A:B) = 2 log 2`. -/
@[zil_level bridge_theorem]
theorem bellSinglet_entropy_composition :
    Sᵥₙ (MState.pure bellPsiMinus) = 0
      ∧ Sᵥₙ (MState.pure bellPsiMinus).traceRight = Real.log 2
      ∧ Sᵥₙ (MState.pure bellPsiMinus).traceLeft = Real.log 2
      ∧ qMutualInfo (MState.pure bellPsiMinus) = 2 * Real.log 2 := by
  have h := entropy_composition_of_traceRight_uniform bellPsiMinus bellPsiMinus_traceRight_uniform
  rwa [Fintype.card_fin] at h

/-- **The genuine von Neumann mutual information of the Bell singlet density matrix
is `2 log 2`** — the concrete `4 × 4` Bell density matrix `|Ψ⁻⟩⟨Ψ⁻|` carries
`2 ln 2` nats of quantum mutual information. -/
@[zil_level physical_theorem]
theorem bellSinglet_qMutualInfo :
    qMutualInfo (MState.pure bellPsiMinus) = 2 * Real.log 2 :=
  bellSinglet_entropy_composition.2.2.2

/-- **The Bell singlet's reduced entropy is strictly positive** (`log 2 > 0`), so
the singlet density matrix is genuinely correlated — its reduced state is mixed,
not pure. -/
@[zil_level physical_theorem]
theorem bellSinglet_reducedEntropy_pos :
    0 < Sᵥₙ (MState.pure bellPsiMinus).traceRight := by
  rw [bellSinglet_entropy_composition.2.1]
  exact Real.log_pos (by norm_num)

end Physlib.QuantumMechanics.Entanglement

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.Entanglement

zil attach entropy_composition_of_traceRight_uniform where
  formalizes @ "claim:a-pure-bipartite-state-with-a-maximally-mixed-reduced-state-has-zero-global-entropy-reduced-entropy-log-d-and-mutual-information-two-log-d",
  supported_by @ "lean:Sᵥₙ_of_pure_zero",
  supported_by @ "lean:Sᵥₙ_of_partial_eq"

zil attach MES_entropy_composition where
  formalizes @ "claim:the-maximally-entangled-state-has-zero-global-von-neumann-entropy-reduced-entropy-log-d-and-mutual-information-two-log-d",
  supported_by @ "lean:traceRight_pure_MES"

zil attach bellSinglet_entropy_composition where
  formalizes @ "claim:the-explicit-bell-singlet-density-matrix-has-zero-global-entropy-reduced-entropy-log-two-and-mutual-information-two-log-two",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform"

zil attach bellSinglet_qMutualInfo where
  formalizes @ "claim:the-genuine-von-neumann-mutual-information-of-the-bell-singlet-density-matrix-is-two-log-two",
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.bellSinglet_entropy_composition",
  caveat @ "claim:this-is-the-von-neumann-mutual-information-not-the-single-party-reduced-entropy-input-of-the-bell-violation-interpolator"

zil attach MES_isEntangled where
  formalizes @ "claim:the-maximally-entangled-state-is-genuinely-entangled",
  supported_by @ "lean:Ket.MES_isEntangled"

zil_file_contract physlib.maximallyEntangledEntropy where
  promises "Any pure bipartite state whose reduced state is maximally mixed has vanishing global von Neumann entropy, both reduced entropies log d, and quantum mutual information exactly 2 log d - the composed information-correlation statement assembled as proved von Neumann quantities. It is instantiated at the abstract maximally entangled state and at the explicit Bell singlet density matrix |Psi-> = (|01> - |10>)/sqrt 2, whose concrete 4 by 4 density matrix carries genuine mutual information 2 log 2 with strictly positive reduced entropy - the von Neumann quantity, distinct from the single-party reduced entropy that parameterizes the closed-form Bell-violation interpolator."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:qMutualInfo",
    "lean:traceRight_pure_MES",
    "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus",
    "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform"
  ]
  forbids_substitutes [
    "identifying the two-log-d mutual information with the single-party log-d reduced entropy",
    "reading the closed-form Bell-violation interpolator input as the full mutual information"
  ]
  witnessed_by [
    entropy_composition_of_traceRight_uniform,
    MES_entropy_composition,
    bellSinglet_entropy_composition,
    bellSinglet_qMutualInfo,
    bellSinglet_reducedEntropy_pos
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.maximallyEntangledEntropy
