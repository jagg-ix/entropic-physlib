/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockUnitaryDynamics
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-!
# Coherent-state dynamics and the Heisenberg evolution: the clock hand in phase space

The time evolution `U(t) = e^{-itH}` (`SciamaFockUnitaryDynamics`) acts on a coherent state `|α⟩`
(`SciamaFockCoherentState`) by **rotating its label in phase space**:

`U(t)|α⟩ = e^{-iωt/2} |e^{-iωt}α⟩`,

so a coherent state stays coherent, and the label traces the circle `α ↦ e^{-iωt}α` — a **hand rotating on a
clock face**.  Correspondingly the annihilation operator evolves by that phase, `U(t)†aU(t) = e^{-iωt}a` (the
**Heisenberg equation of motion**): `U(t)|α⟩` is an annihilation eigenstate with the rotated eigenvalue
`e^{-iωt}α`.

This is where the single mode's dynamics meets the entropic-time / three-clock program:

* **Compton–de Broglie clock.**  The rotation rate is the mode frequency `ω`; at the Compton value
  `ω = ω_C = mc²/ℏ` (`FrequencyTrinity.comptonFrequency`) the phase-space hand is the *rest-energy quantum
  clock*, and its boosted rate `cosh θ · ω_C` is the de Broglie clock of `DiamondThreeClocks`.
* **Modular clock / thermal time.**  For the Gibbs state `ρ = e^{-βH}/Z` (`SciamaFockBoltzmannOperator`) the
  modular (Tomita) flow is `σ_s(A) = ρ^{is}Aρ^{-is} = U(-sβ)†AU(-sβ)`, i.e. the Heisenberg evolution at
  physical time `t = -sβ`: by **Connes–Rovelli**, physical time is `β ×` modular time, the KMS `β = 2π`
  (Bisognano–Wichmann/Unruh) of `DiamondBisognanoWichmannKMS` setting the thermal-time scale.
* **Page–Wootters relational time.**  `U(t)|α⟩` is the conditional state of the mode given the clock reads
  `t`; the rotating coherent label `e^{-iωt}α` is the **clock pointer**, and its minimum-uncertainty
  Gaussian makes the coherent state an ideal Page–Wootters clock.
* **Witten framing phase.**  The phases compose by the group law `rotationPhase ω s · rotationPhase ω t =
  rotationPhase ω (s+t)` — the same **multiplicative phase law** as Witten's framing-shift anomaly for the
  Jones polynomial (`WittenJonesPolynomialChernSimons`); one full revolution `t = 2π/ω` returns the label but
  leaves the geometric phase `e^{-iπ}` from the zero-point `ω/2`.

* `rotationPhase`, `rotationPhase_mul` — the clock-hand phase `e^{-iωt}` and its group/framing law.
* `evolutionOp_coherentState` — `U(t)|α⟩ = e^{-iωt/2}|e^{-iωt}α⟩` (coherent states stay coherent).
* `evolutionOp_coherentState_annihilation_coord` — `a·U(t)|α⟩ = e^{-iωt}α·U(t)|α⟩` (Heisenberg, coordinate form).

Honest scope: the exact coherent evolution and the annihilation eigen-relation; the three-clock/Page–Wootters/
thermal-time/Witten readings are the interpretive links (docstring), with `rotationPhase` at `ω_C` the concrete
tie to `FrequencyTrinity`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentEvolution

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockUnitaryDynamics
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState

/-- **The clock-hand phase** `e^{-iωt}` — the phase-space rotation of the coherent label (`= U(t)†aU(t)/a`). -/
def rotationPhase (ω t : ℝ) : ℂ := Complex.exp (((-(ω * t) : ℝ) : ℂ) * Complex.I)

/-- **[Framing/group law] `e^{-iωs}·e^{-iωt} = e^{-iω(s+t)}`.**  The clock phases compose multiplicatively —
Witten's framing-shift phase law. -/
theorem rotationPhase_mul (ω s t : ℝ) :
    rotationPhase ω s * rotationPhase ω t = rotationPhase ω (s + t) := by
  rw [rotationPhase, rotationPhase, rotationPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The evolution phase advances by one clock-hand step per quantum: `e^{-iω(n+1+½)t} = e^{-iωt}·e^{-iω(n+½)t}`. -/
theorem evolutionPhase_succ (ω t : ℝ) (n : ℕ) :
    evolutionPhase ω t (n + 1) = rotationPhase ω t * evolutionPhase ω t n := by
  rw [evolutionPhase, evolutionPhase, rotationPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **[Coherent states stay coherent] `U(t)|α⟩ = e^{-iωt/2}|e^{-iωt}α⟩`.**  Time evolution rotates the coherent
label on the phase-space circle — the clock hand. -/
theorem evolutionOp_coherentState (ω t : ℝ) (α : ℂ) :
    evolutionOp ω t (coherentState α)
      = evolutionPhase ω t 0 • coherentState (rotationPhase ω t * α) := by
  apply lp.ext
  funext n
  rw [evolutionOp_apply_coe, coherentState_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    coherentState_apply, coherentCoeff, coherentCoeff, mul_pow]
  rw [show evolutionPhase ω t n = evolutionPhase ω t 0 * rotationPhase ω t ^ n from ?_]
  · field_simp
  · rw [evolutionPhase, evolutionPhase, rotationPhase, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- **[Heisenberg equation, coordinate form] `a·U(t)|α⟩ = e^{-iωt}α·U(t)|α⟩`.**  The evolved coherent state is
an annihilation eigenstate with the rotated eigenvalue `e^{-iωt}α` — the annihilation operator evolves as
`U(t)†aU(t) = e^{-iωt}a`. -/
theorem evolutionOp_coherentState_annihilation_coord (ω t : ℝ) (α : ℂ) (n : ℕ) :
    (Real.sqrt (n + 1) : ℂ) * (evolutionOp ω t (coherentState α)) (n + 1)
      = (rotationPhase ω t * α) * (evolutionOp ω t (coherentState α)) n := by
  rw [evolutionOp_apply_coe, evolutionOp_apply_coe, coherentState_apply, coherentState_apply,
    evolutionPhase_succ,
    show (Real.sqrt (n + 1) : ℂ) * (rotationPhase ω t * evolutionPhase ω t n * coherentCoeff α (n + 1))
      = rotationPhase ω t * evolutionPhase ω t n * ((Real.sqrt (n + 1) : ℂ) * coherentCoeff α (n + 1))
      from by ring, coherentCoeff_shift]
  ring

/-- **[Compton-clock rate] the phase-space hand at `ω = ω_C = mc²/ℏ`** is the rest-energy quantum clock
`e^{-i(mc²/ℏ)t}` — the tie to the Compton–de Broglie clock of `FrequencyTrinity`/`DiamondThreeClocks`. -/
theorem rotationPhase_compton (m c ħ t : ℝ) :
    rotationPhase (Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency m c ħ) t
      = Complex.exp (((-(m * c ^ 2 / ħ * t) : ℝ) : ℂ) * Complex.I) := by
  rw [rotationPhase, Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentEvolution

end
