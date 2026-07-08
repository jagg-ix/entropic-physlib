/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaTransitionLocalEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaComplexCanonicalBornProduct
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen

/-!
# Merging the Ipek–Caticha arc with the complex Schrödinger functional and the Nagao–Nielsen complex contour

Links the Ipek–Caticha coupled-gravity entropic dynamics (arXiv:2006.05036) to two established structures of the
repository: the **linear complex Schrödinger flow** (`HamiltonKillingComplexStructureSchrodinger`, Caticha's
Hamilton–Killing derivation) and the **Nagao–Nielsen complex action / contour**
(`EntropicDynamicsComplexActionNagaoNielsen`, `e^{iS_R/ℏ − S_I/ℏ}`). The two links pin down exactly *where*
gravity enters and *what* the local clock does.

* **the flat generator is the linear Schrödinger operator** (`flatGeneratorLM`, `flatGenerator_superposition`): the
 fixed-background Ipek–Caticha generator `𝓛₀(ψ) = E·ψ` is the `ℂ`-linear map `E·id`, so it superposes *by* the
 repository's `schrodinger_superposition` — flat entropic dynamics *is* the linear Schrödinger flow;
* **gravity breaks exactly that linearity** (`flat_linear_gravity_nonlinear`): the gravity-coupled generator
 violates the very superposition that `schrodinger_superposition` guarantees for the linear flow — the
 Ipek–Caticha prediction located precisely against the Hamilton–Killing linear Schrödinger operator;
* **the local entropic time is the Nagao–Nielsen `ℏ`** (`localClock_transition_is_entropyDamping`): the
 local-clock transition weight (`α = 1/δξ⊥`) is the Nagao–Nielsen entropy damping `e^{−S_I/ℏ}` with
 `ℏ = 2δξ⊥` — the local proper time *is* the effective `ℏ` of the complex-action contour, so the transition sits
 on the `kuikenWeight` hub with a position-dependent `ℏ`;
* **the conjugate wave function is the reversed contour phase** (`edWaveFunction_conj_is_nn_antiphase`):
 `Ψ* = \overline{Ψ}` at unit amplitude is `e^{−iθ}`, the anti-phase `e^{−iS_R/ℏ}` of the Nagao–Nielsen weight — the
 `Ψ*` canonical variable is the reversed complex-action contour.

So the Ipek–Caticha arc connects cleanly: its flat generator is the Hamilton–Killing linear Schrödinger operator
(superposition), its gravity coupling is the nonlinear departure from it, its local entropic time is the effective
`ℏ = 2δξ⊥` of the Nagao–Nielsen complex action, and its `(Ψ, Ψ*)` variables are the forward/reversed contours of
`e^{iS_R/ℏ − S_I/ℏ}`.

* **§A — the complex Schrödinger functional** (`flatGeneratorLM`, `flatGenerator_superposition`,
 `flat_linear_gravity_nonlinear`).
* **§B — the Nagao–Nielsen complex contour** (`localClock_transition_is_entropyDamping`,
 `edWaveFunction_conj_is_nn_antiphase`, `ipekCaticha_on_nagaoNielsen_contour`).

The linear-map representation, the superposition/violation dichotomy, the local-`ℏ` identity,
and the reversed-contour phase are exact algebra, reusing `schrodinger_superposition`,
`gravGenerator_superposition_violation`, `ed_transition_is_entropyDamping`,
`ed_wavefunction_phase_is_complexAction_phase`, and `edWaveFunction_conj`. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036; A. Caticha (Hamilton–Killing); K. Nagao, H.B. Nielsen (complex action).
 Repo dependencies: `EntropicTime.HamiltonKillingComplexStructureSchrodinger` (`schrodinger_superposition`),
 `EntropicTime.EntropicDynamicsComplexActionNagaoNielsen` (`ed_transition_is_entropyDamping`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaTransitionLocalEntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaComplexCanonicalBornProduct
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.NonHermitian.WickRotation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen

/-! ## §A — the complex Schrödinger functional -/

/-- **The flat generator as a `ℂ`-linear map** `𝓛₀ = E·id` — the fixed-background Ipek–Caticha Schrödinger
generator represented as the `ℂ`-linear operator `E·id` on `ℂ`, the Hamilton–Killing linear Schrödinger
Hamiltonian. -/
noncomputable def flatGeneratorLM (E : ℝ) : ℂ →ₗ[ℂ] ℂ := (E : ℂ) • LinearMap.id

/-- **[The linear map is the flat generator] `𝓛₀ = E·(·)`.** -/
theorem flatGeneratorLM_apply (E : ℝ) (ψ : ℂ) : flatGeneratorLM E ψ = flatGenerator E ψ := by
  simp only [flatGeneratorLM, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul,
    flatGenerator]

/-- **[The flat entropic-dynamics generator superposes, via the Hamilton–Killing linear Schrödinger flow].** The
fixed-background generator is `ℂ`-linear, so `𝓛₀(c₁ψ₁ + c₂ψ₂) = c₁𝓛₀ψ₁ + c₂𝓛₀ψ₂` follows from the repository's
`schrodinger_superposition` — flat entropic dynamics is the linear Schrödinger flow. -/
theorem flatGenerator_superposition (E : ℝ) (c₁ c₂ ψ₁ ψ₂ : ℂ) :
    flatGenerator E (c₁ • ψ₁ + c₂ • ψ₂) = c₁ • flatGenerator E ψ₁ + c₂ • flatGenerator E ψ₂ := by
  simp only [← flatGeneratorLM_apply]
  exact schrodinger_superposition (flatGeneratorLM E) c₁ c₂ ψ₁ ψ₂

/-- **[Flat linear Schrödinger, gravity nonlinear].** The combined result: the flat generator superposes exactly
as the Hamilton–Killing linear Schrödinger operator (`schrodinger_superposition`), while the gravity-coupled
generator violates that superposition (`gravGenerator_superposition_violation`) — gravity is precisely the
nonlinear departure from the linear Schrödinger flow. -/
theorem flat_linear_gravity_nonlinear (E lam : ℝ) (hlam : lam ≠ 0) :
    (∀ c₁ c₂ ψ₁ ψ₂ : ℂ, flatGenerator E (c₁ • ψ₁ + c₂ • ψ₂)
        = c₁ • flatGenerator E ψ₁ + c₂ • flatGenerator E ψ₂)
      ∧ (∃ ψ₁ ψ₂ : ℂ, gravGenerator E lam (ψ₁ + ψ₂)
        ≠ gravGenerator E lam ψ₁ + gravGenerator E lam ψ₂) :=
  ⟨fun c₁ c₂ ψ₁ ψ₂ => flatGenerator_superposition E c₁ c₂ ψ₁ ψ₂,
   gravGenerator_superposition_violation E lam hlam⟩

/-! ## §B — the Nagao–Nielsen complex contour -/

/-- **[The local entropic time is the Nagao–Nielsen `ℏ`] `P = e^{−S_I/(2δξ⊥)}`.** With the local-clock multiplier
`α = 1/δξ⊥`, the transition weight is the Nagao–Nielsen entropy damping `e^{−S_I/ℏ}` with imaginary action
`S_I = (Δχ−b)²` and effective `ℏ = 2δξ⊥` — the local proper time is the `ℏ` of the complex-action contour. -/
theorem localClock_transition_is_entropyDamping (δξ b Δχ : ℝ) (hδξ : δξ ≠ 0) :
    edTransitionWeight (entropicTimeMultiplier δξ) b Δχ = entropyDamping ((Δχ - b) ^ 2) (2 * δξ) := by
  have hα : entropicTimeMultiplier δξ ≠ 0 := by
    unfold entropicTimeMultiplier; exact one_div_ne_zero hδξ
  rw [ed_transition_is_entropyDamping (entropicTimeMultiplier δξ) b Δχ hα]
  congr 1
  unfold entropicTimeMultiplier
  field_simp

/-- **[The conjugate wave function is the reversed Nagao–Nielsen contour] `Ψ* = e^{−iθ}`.** At unit amplitude the
conjugate wave function `Ψ* = \overline{Ψ}` is the anti-phase `e^{−iθ} = e^{−iS_R/ℏ}` — the `Ψ*` canonical variable
is the reversed complex-action contour of the Nagao–Nielsen weight. -/
theorem edWaveFunction_conj_is_nn_antiphase (θ : ℝ) :
    (starRingEnd ℂ) (edWaveFunction 1 θ) = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [edWaveFunction_conj, ed_wavefunction_phase_is_complexAction_phase]

/-- **[The Ipek–Caticha arc on the Nagao–Nielsen contour, assembled].** The local-clock transition is the entropy
damping with `ℏ = 2δξ⊥`, and the conjugate wave function is the reversed contour phase — the coupled-gravity
entropic dynamics on the complex-action contour. -/
theorem ipekCaticha_on_nagaoNielsen_contour (δξ b Δχ θ : ℝ) (hδξ : δξ ≠ 0) :
    (edTransitionWeight (entropicTimeMultiplier δξ) b Δχ = entropyDamping ((Δχ - b) ^ 2) (2 * δξ))
      ∧ ((starRingEnd ℂ) (edWaveFunction 1 θ) = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) :=
  ⟨localClock_transition_is_entropyDamping δξ b Δχ hδξ, edWaveFunction_conj_is_nn_antiphase θ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen

end
