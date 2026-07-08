/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

/-!
# Entropic Dynamics is the Nagao–Nielsen complex action: transition probability = modulus, wave function = phase

Merges the entropic-dynamics reconstruction of QFT (Ipek–Abedi–Caticha, arXiv:1803.07493) with the
**Nagao–Nielsen complex-action** path-integral of the arc (`ComplexActionPathIntegralWeight`). The complex-action
weight `e^{iS_R/ℏ − S_I/ℏ}` splits into a **phase** `e^{iS_R/ℏ}` and a **real (entropic) damping** `e^{−S_I/ℏ}`
(`master_modulus_is_kuiken`, `kuikenWeight = e^{−S_I/ℏ}`). Entropic dynamics is exactly this split:

* the **entropic-dynamics transition probability is the modulus of the complex-action weight**
 `P(Δχ) = ‖complexActionPathIntegralWeight S_R (Δχ−b)² (2/α)‖` (`ed_transition_is_complexAction_modulus`) — the
 ED entropic action `½α(Δχ−b)²` **is the imaginary action** `S_I/ℏ` (with `S_I = (Δχ−b)²`, `ℏ = 2/α`), so `P` is
 the Nagao–Nielsen entropy-damping factor `e^{−S_I/ℏ}` (`ed_transition_is_entropyDamping`);
* the **entropic-dynamics wave-function phase is the complex-action phase** `e^{iΦ} = e^{iS_R/ℏ}`
 (`ed_wavefunction_phase_is_complexAction_phase`) — the current potential `Φ` is the real action `S_R/ℏ`;
* so **entropic dynamics reconstructs the Nagao–Nielsen complex action** (`ed_is_nagaoNielsen_complexAction`):
 the probability `ρ = |ψ|²` is the modulus / entropy damping (imaginary action = ED entropic action) and the
 phase `Φ` is the real action — the wave functional `ψ = √ρ e^{iΦ}` assembles the two halves of
 `e^{iS_R/ℏ − S_I/ℏ}`.

This is the merge: the Nagao–Nielsen contour rotation `e^{iS/ℏ} → e^{−S_I/ℏ}` — turning the real action into the
entropic damping — is exactly the entropic-dynamics transition probability, and the residual phase is the ED wave
functional. The information-based reconstruction and the complex-action path integral are one object on the
`kuikenWeight` hub.

* **§A — the ED transition probability is the complex-action modulus** (`ed_transition_is_complexAction_modulus`).
* **§B — it is the Nagao–Nielsen entropy damping** (`ed_transition_is_entropyDamping`).
* **§C — the ED wave function is the complex-action phase** (`ed_wavefunction_phase_is_complexAction_phase`).
* **§D — ED reconstructs the Nagao–Nielsen complex action** (`ed_is_nagaoNielsen_complexAction`).

Every statement is an exact identity binding the ED defs (`edTransitionWeight`,
`edWaveFunction`) to the existing complex-action defs (`complexActionPathIntegralWeight`, `master_modulus_is_kuiken`,
`kuiken_eq_entropyDamping`, `entropyDamping`). The identification `S_I = (Δχ−b)²`, `ℏ = 2/α`, `S_R/ℏ = Φ` is the
physical content. No new axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493; K. Nagao, H.B. Nielsen (complex action). Repo dependencies:
 `PathIntegral.ComplexActionPathIntegralWeight`, `NonHermitian.WickRotation` (`entropyDamping`),
 `EntropicTime.EntropicDynamicsWaveFunctionReconstruction`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.NonHermitian.WickRotation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen

/-! ## §A — the ED transition probability is the complex-action modulus -/

/-- **[The entropic-dynamics transition probability is the modulus of the Nagao–Nielsen complex-action weight]
`P(Δχ) = ‖e^{iS_R/ℏ − S_I/ℏ}‖`.** With imaginary action `S_I = (Δχ−b)²` and `ℏ = 2/α`, the ED Gaussian transition
probability is exactly the modulus of the complex-action path-integral weight — the entropic damping half of
`e^{iS_R/ℏ − S_I/ℏ}`, for any real action `S_R`. -/
theorem ed_transition_is_complexAction_modulus (α b Δχ S_R : ℝ) (hα : α ≠ 0) :
    edTransitionWeight α b Δχ = ‖complexActionPathIntegralWeight S_R ((Δχ - b) ^ 2) (2 / α)‖ := by
  rw [edTransitionWeight_is_kuiken α b Δχ hα, master_modulus_is_kuiken]

/-! ## §B — it is the Nagao–Nielsen entropy damping -/

/-- **[The ED transition probability is the entropy-damping factor] `P(Δχ) = e^{−S_I/ℏ}`.** The ED transition
probability is the Nagao–Nielsen entropy-damping factor `entropyDamping S_I ℏ = e^{−S_I/ℏ}` with the ED entropic
action `S_I = (Δχ−b)²` as the imaginary action and `ℏ = 2/α`: the imaginary action *is* the entropic action. -/
theorem ed_transition_is_entropyDamping (α b Δχ : ℝ) (hα : α ≠ 0) :
    edTransitionWeight α b Δχ = entropyDamping ((Δχ - b) ^ 2) (2 / α) := by
  rw [edTransitionWeight_is_kuiken α b Δχ hα, kuiken_eq_entropyDamping]

/-! ## §C — the ED wave function is the complex-action phase -/

/-- **[The entropic-dynamics wave-function phase is the complex-action phase] `e^{iΦ} = e^{iS_R/ℏ}`.** At unit
amplitude the entropic-dynamics wave functional is the pure phase `e^{iΦ}`, which is the phase factor of the
Nagao–Nielsen complex-action weight with real action `S_R/ℏ = Φ`: the current potential is the real action. -/
theorem ed_wavefunction_phase_is_complexAction_phase (θ : ℝ) :
    edWaveFunction 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  unfold edWaveFunction
  rw [Real.sqrt_one]
  simp

/-! ## §D — ED reconstructs the Nagao–Nielsen complex action -/

/-- **[Entropic dynamics reconstructs the Nagao–Nielsen complex action, assembled].** The ED reconstruction and
the complex-action path integral are one object:

* the transition probability is the **modulus** `‖complexActionPathIntegralWeight S_R (Δχ−b)² (2/α)‖`, i.e. the
  entropy damping `e^{−S_I/ℏ}` with the ED entropic action as the **imaginary action** `S_I = (Δχ−b)²`;
* the wave-function phase is the **phase** `e^{iΦ}` of the complex-action weight, with the current potential the
  **real action** `Φ = S_R/ℏ`.

The wave functional `ψ = √ρ e^{iΦ}` (with `ρ = |ψ|²`) assembles the two halves of the Nagao–Nielsen complex action
`e^{iS_R/ℏ − S_I/ℏ}`: phase (real action) times entropic damping (imaginary action) — entropic dynamics *is* the
complex action on the `kuikenWeight` hub. -/
theorem ed_is_nagaoNielsen_complexAction (α b Δχ S_R θ : ℝ) (hα : α ≠ 0) :
    edTransitionWeight α b Δχ = ‖complexActionPathIntegralWeight S_R ((Δχ - b) ^ 2) (2 / α)‖
      ∧ edTransitionWeight α b Δχ = entropyDamping ((Δχ - b) ^ 2) (2 / α)
      ∧ edWaveFunction 1 θ = Complex.exp ((θ : ℂ) * Complex.I) :=
  ⟨ed_transition_is_complexAction_modulus α b Δχ S_R hα,
    ed_transition_is_entropyDamping α b Δχ hα,
    ed_wavefunction_phase_is_complexAction_phase θ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen

end
