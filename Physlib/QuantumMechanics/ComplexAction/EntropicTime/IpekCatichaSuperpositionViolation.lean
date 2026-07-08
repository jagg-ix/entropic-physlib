/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

/-!
# Coupling quantum fields to gravity violates the superposition principle (Ipek–Caticha)

Formalizes the central *prediction* of Ipek–Caticha (arXiv:2006.05036): coupling the entropic-dynamics quantum
field to dynamical gravity makes the evolution **nonlinear**, violating the quantum superposition principle. The
mechanism is the metric backreaction: in flat space the functional Schrödinger generator `−iĤ` is a *fixed linear*
operator (Eq. 108 with fixed `g`), but with dynamical gravity the metric is *sourced by the state* `Ψ` (Eq. 104,
the geometry responds to `⟨Ĥ⟩` / the probability `ρ`), so the effective generator acquires a term proportional to
`|Ψ|² = ρ` (the Born rule) and becomes nonlinear.

Modeling the single-mode wave function `Ψ ∈ ℂ`:

* the **flat-space generator** `𝓛₀(ψ) = E·ψ` is **additive and homogeneous** (`flatGenerator_additive`,
 `flatGenerator_smul`) — a linear operator, so superposition holds;
* the **gravitational backreaction** `𝓑(ψ) = λ·|ψ|²·ψ` is sourced by the probability `ρ = |ψ|²`
 (`gravBackreaction_born`: on `Ψ = ρ^{1/2}e^{iΦ}` it is `λρ·Ψ`, reusing the Born rule
 `edWaveFunction_modulus_sq`);
* the **gravity-coupled generator** `𝓛(ψ) = E·ψ + λ|ψ|²ψ` **violates superposition** for `λ ≠ 0`
 (`gravGenerator_superposition_violation`): `𝓛(ψ₁+ψ₂) ≠ 𝓛(ψ₁) + 𝓛(ψ₂)` — the `|ψ|²` backreaction is not
 additive;
* in the **no-gravity limit** `λ = 0` the generator reduces to the flat linear one (`gravGenerator_flat_limit`), so
 superposition is restored — the violation is *exactly* the gravitational coupling.

So the Ipek–Caticha prediction is this structural dichotomy: fixed background ⟹ linear generator ⟹ superposition;
dynamical gravity ⟹ state-sourced `|Ψ|²` term ⟹ nonlinear generator ⟹ superposition violated. The nonlinearity is
driven by the Born-rule probability `ρ = |Ψ|²`, the same `ρ` that sources the geometry.

* **§A — the flat-space generator is linear (superposition holds)** (`flatGenerator`, `flatGenerator_additive`,
 `flatGenerator_smul`).
* **§B — the gravitational backreaction is the Born-rule probability** (`gravBackreaction`,
 `gravBackreaction_born`).
* **§C — the gravity-coupled generator violates superposition** (`gravGenerator`,
 `gravGenerator_superposition_violation`, `gravGenerator_flat_limit`).

The linearity of the flat generator, the Born-rule form of the backreaction, and the failure
of additivity are exact `ℂ` algebra on a single-mode wave function, reusing `edWaveFunction` and its Born rule. The
full functional Schrödinger equation, the metric source equation (Eq. 104), and the field-theoretic
superspace are the referenced content. The single-mode `λ|ψ|²ψ` term is a faithful minimal model of the
state-dependent (nonlinear) generator, not the full backreaction functional. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 104, 108; nonlinearity / superposition violation). Repo structure:
 `EntropicTime.EntropicDynamicsWaveFunctionReconstruction` (`edWaveFunction`, `edWaveFunction_modulus_sq`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation

/-! ## §A — the flat-space generator is linear (superposition holds) -/

/-- **The flat-space Schrödinger generator** `𝓛₀(ψ) = E·ψ` — multiplication by the fixed (background) Hamiltonian
coefficient `E`, the linear generator of the functional Schrödinger evolution on a fixed metric (Ipek–Caticha
Eq. 108 with fixed `g`). -/
noncomputable def flatGenerator (E : ℝ) (ψ : ℂ) : ℂ := (E : ℂ) * ψ

/-- **[The flat generator is additive] `𝓛₀(ψ₁+ψ₂) = 𝓛₀(ψ₁) + 𝓛₀(ψ₂)`.** The fixed-background generator respects
superposition — linear combinations of solutions evolve as the combination. -/
theorem flatGenerator_additive (E : ℝ) (ψ₁ ψ₂ : ℂ) :
    flatGenerator E (ψ₁ + ψ₂) = flatGenerator E ψ₁ + flatGenerator E ψ₂ := by
  unfold flatGenerator; ring

/-- **[The flat generator is homogeneous] `𝓛₀(c·ψ) = c·𝓛₀(ψ)`.** -/
theorem flatGenerator_smul (E : ℝ) (c ψ : ℂ) :
    flatGenerator E (c * ψ) = c * flatGenerator E ψ := by
  unfold flatGenerator; ring

/-! ## §B — the gravitational backreaction is the Born-rule probability -/

/-- **The gravitational backreaction term** `𝓑(ψ) = λ·|ψ|²·ψ` — the state-sourced contribution to the generator
when the metric responds to the quantum state (Ipek–Caticha Eq. 104), proportional to the probability `ρ = |ψ|²`. -/
noncomputable def gravBackreaction (lam : ℝ) (ψ : ℂ) : ℂ :=
  (lam : ℂ) * (Complex.normSq ψ : ℂ) * ψ

/-- **[The backreaction is sourced by the Born-rule probability] `𝓑(Ψ) = λρ·Ψ`.** On the entropic-dynamics wave
function `Ψ = ρ^{1/2}e^{iΦ}` the backreaction term is `λρ·Ψ`, since `|Ψ|² = ρ` is the Born rule
(`edWaveFunction_modulus_sq`) — the geometry is sourced by the probability, so the nonlinearity is too. -/
theorem gravBackreaction_born (lam ρ Φ : ℝ) (hρ : 0 ≤ ρ) :
    gravBackreaction lam (edWaveFunction ρ Φ) = ((lam * ρ : ℝ) : ℂ) * edWaveFunction ρ Φ := by
  unfold gravBackreaction
  have hn : Complex.normSq (edWaveFunction ρ Φ) = ρ := by
    rw [Complex.normSq_eq_norm_sq]
    exact edWaveFunction_modulus_sq ρ Φ hρ
  rw [hn]
  push_cast
  ring

/-! ## §C — the gravity-coupled generator violates superposition -/

/-- **The gravity-coupled Schrödinger generator** `𝓛(ψ) = E·ψ + λ|ψ|²ψ` — the flat generator plus the
state-sourced backreaction, the effective (nonlinear) generator when quantum matter is coupled to dynamical
gravity. -/
noncomputable def gravGenerator (E lam : ℝ) (ψ : ℂ) : ℂ :=
  flatGenerator E ψ + gravBackreaction lam ψ

/-- **[The gravity-coupled generator violates superposition] for `λ ≠ 0`.** There exist states `ψ₁, ψ₂` with
`𝓛(ψ₁+ψ₂) ≠ 𝓛(ψ₁) + 𝓛(ψ₂)`: the `|ψ|²` backreaction breaks additivity (witnessed by `ψ₁ = ψ₂ = 1`, defect `6λ`).
Coupling quantum fields to gravity destroys the linear superposition principle — the central Ipek–Caticha
prediction. -/
theorem gravGenerator_superposition_violation (E lam : ℝ) (hlam : lam ≠ 0) :
    ∃ ψ₁ ψ₂ : ℂ, gravGenerator E lam (ψ₁ + ψ₂) ≠ gravGenerator E lam ψ₁ + gravGenerator E lam ψ₂ := by
  refine ⟨1, 1, ?_⟩
  have hdiff : gravGenerator E lam ((1 : ℂ) + 1)
      - (gravGenerator E lam 1 + gravGenerator E lam 1) = ((6 * lam : ℝ) : ℂ) := by
    unfold gravGenerator flatGenerator gravBackreaction
    have h2 : Complex.normSq ((1 : ℂ) + 1) = 4 := by
      rw [show (1 : ℂ) + 1 = ((2 : ℝ) : ℂ) by norm_num, Complex.normSq_ofReal]; norm_num
    have h1 : Complex.normSq (1 : ℂ) = 1 := Complex.normSq_one
    rw [h2, h1]
    push_cast
    ring
  intro h
  rw [h, sub_self] at hdiff
  have h6 : (6 * lam : ℝ) = 0 := by exact_mod_cast hdiff.symm
  exact hlam (by linarith)

/-- **[The no-gravity limit restores superposition] `𝓛|_{λ=0} = 𝓛₀`.** At zero gravitational coupling the
generator is the flat linear one, so superposition holds — the violation is exactly the gravitational backreaction. -/
theorem gravGenerator_flat_limit (E : ℝ) (ψ : ℂ) : gravGenerator E 0 ψ = flatGenerator E ψ := by
  unfold gravGenerator gravBackreaction
  simp

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation

end
