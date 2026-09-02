/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
public import Physlib.Thermodynamics.GravitationalCouplingSystem
public import Physlib.Thermodynamics.NewtonGIsolation

/-!
# The gravitational constant from an information-theoretic mass and an area-per-bit screen

Two information-theoretic derivations meet at Newton's law of gravity:

* **Inertia** — Caticha and Cafaro (arXiv:0710.1071) obtain the inertial mass as the reciprocal
  position-uncertainty variance `m = 1/σ₀²` (`EntropicMassNewtonianDynamics.inferenceMass`).
* **Coupling** — Verlinde's entropic gravity fixes the force on a holographic screen at
  `F = 4π m M c³/(ℏ N)` with the bit count `N` (`NewtonGIsolation.entropicForce_bitForm`); Newton's
  form `F = G M m/R²` holds exactly when `N = holographicBits (sphereArea R) G ℏ c = 4πR²c³/(Gℏ)`, and
  then `G = sphereArea R · c³/(ℏ N)` is the **area per bit** (`NewtonGIsolation.newtonG_eq_area_per_bit`).

Feeding the inference mass into the entropic force makes the gravitational force fully
information-theoretic: neither the mass nor the coupling is a free constant.

* **§A** the gravitational force on an inference-mass test particle, `F = G M/(σ₀² R²)`.
* **§B** its `G`-free bit form `F = 4π M c³/(ℏ N σ₀²)`: mass from the variance `σ₀²`, coupling from the
  bit count `N`, no `G`.
* **§C** Newton's form still forces `G = sphereArea R · c³/(ℏ N)` — the area-per-bit derivation is
  unchanged by the reinterpretation of mass.
* **§D** the full gravitational hierarchy at the isolated `G`: the inference-mass bit force, the
  area-per-bit `G`, the Einstein coupling `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)`
  (`GravitationalCouplingSystem.einsteinCoupling_bitForm`), the dust source
  `κ(ρc²/2) = 4πGρ/c²` (`dust_traceReversed_source`) and the Schwarzschild radius
  `r_s = 2Mc·A/(ℏN)` (`schwarzschildRadius_bitForm`).

The `4π` of the Newtonian/Poisson source and the `8π` of the Einstein equation are the two faces of the
same field equation: Blume (JAMP 10 (2022) 1461) shows that Newton's `ΔΦ = 4πGρ` and Einstein's
`Ric − (R/2)g = 8πGT/c⁴` are the *same* velocity-field divergence equation
`v[div v] + div(v,v) = −4πρ`. The dust reduction `κ(ρc²/2) = 4πGρ/c²` and the weak-field Poisson limit
(`ComptonClock.NewtonianAndGRLimit.weakField_einstein_poisson`) are that transition carried by the one
`G = sphereArea R · c³/(ℏN)`.

## References

* A. Caticha, C. Cafaro, arXiv:0710.1071 — the inertial mass `m = 1/σ₀²`.
* E. Verlinde, *On the origin of gravity and the laws of Newton*, JHEP 04 (2011) 029 — the entropic
  force and the area-per-bit `G`.
* F. Blume, *On the Transition from Newtonian Gravity to General Relativity*, J. Appl. Math. Phys. 10
  (2022) 1461 — the `4π`↔`8π` velocity-field divergence unification of the Newtonian and Einstein
  field equations.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Physlib.Relativity.SemiClassical

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant

@[expose] public section

/-! ## A. The gravitational force on an inference-mass test particle -/

/-- **[Newtonian gravity with the information-theoretic mass]** With the test mass set to the
inference mass `m = inferenceMass σ₀ = 1/σ₀²`, Newton's gravitational force is
`F = G M m/R² = G M/(σ₀² R²)` — the force is inversely proportional to the test particle's position
variance. -/
theorem gravitational_force_inference_mass (G M σ₀ R : ℝ) :
    G * M * inferenceMass σ₀ / R ^ 2 = G * M / (σ₀ ^ 2 * R ^ 2) := by
  rw [inferenceMass]; ring

/-! ## B. The `G`-free bit form of the gravitational force -/

/-- **[The gravitational force in pure information form]** Feeding the inference mass
`m = inferenceMass σ₀ = 1/σ₀²` into Verlinde's entropic force
(`NewtonGIsolation.entropicForce_bitForm`) gives `F = 4π M c³/(ℏ N σ₀²)`: the mass comes from the
position variance `σ₀²`, the coupling from the bit count `N`, and `G` does not appear. This is the
gravitational force with neither the inertial mass nor the gravitational constant a free parameter. -/
theorem gravitational_force_bitForm_inference (M c N kB σ₀ ℏ Δx : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) :
    verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB (inferenceMass σ₀) c Δx) Δx
      = 4 * Real.pi * M * c ^ 3 / (ℏ * N * σ₀ ^ 2) := by
  rw [entropicForce_bitForm M c N kB (inferenceMass σ₀) ℏ Δx hN hkB hΔx, inferenceMass]
  ring

/-! ## C. Newton's form still forces `G` to be the area per bit -/

/-- **[The area-per-bit `G` is unchanged by the information-theoretic mass]** If the entropic force on
an inference-mass particle takes Newton's form `F = G M (inferenceMass σ₀)/R²`, then `G` is still the
area per bit `G = sphereArea R · c³/(ℏ N)` (`NewtonGIsolation.newtonG_eq_area_per_bit`): the derivation
of `G` does not depend on whether the test mass is fundamental or read off the position variance. -/
theorem newtonG_area_per_bit_inference (M c N kB σ₀ ℏ Δx G R : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hσ : σ₀ ≠ 0) (hM : M ≠ 0)
    (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (h : verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB (inferenceMass σ₀) c Δx) Δx
      = G * M * inferenceMass σ₀ / R ^ 2) :
    G = sphereArea R * c ^ 3 / (ℏ * N) := by
  have hmass : inferenceMass σ₀ ≠ 0 := by
    rw [inferenceMass]; exact inv_ne_zero (pow_ne_zero 2 hσ)
  exact newtonG_eq_area_per_bit M c N kB (inferenceMass σ₀) ℏ Δx G R
    hN hkB hΔx hmass hM hc hℏ hG hR h

/-! ## D. The full gravitational hierarchy at the isolated `G` -/

/-- **[The entropic gravitational system]** From the single identification
`N = holographicBits (sphereArea R) G ℏ c` (the bit count forced by Newton's form), with an
information-theoretic test mass `m = inferenceMass σ₀`, the whole hierarchy follows: the `G`-free bit
force `F = 4π M c³/(ℏ N σ₀²)`, the area-per-bit `G = sphereArea R · c³/(ℏ N)`, the Einstein coupling
`κ = 8πG/c⁴ = 8π(A/N)/(ℏc)`, the dust source `κ(ρc²/2) = 4πGρ/c²` (the `4π`↔`8π` Newton→Einstein
transition, Blume 2022) and the Schwarzschild radius `r_s = 2Mc·A/(ℏN)`. Both the inertia and the
gravitational coupling are information-theoretic. -/
theorem entropic_gravity_system (M c N kB σ₀ ℏ Δx G R ρ : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hσ : σ₀ ≠ 0) (hM : M ≠ 0)
    (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB (inferenceMass σ₀) c Δx) Δx
        = 4 * Real.pi * M * c ^ 3 / (ℏ * N * σ₀ ^ 2)
    ∧ G = sphereArea R * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c)
    ∧ (8 * Real.pi * G / c ^ 4) * (ρ * c ^ 2 / 2) = 4 * Real.pi * G * ρ / c ^ 2
    ∧ schwarzschildRadius M G c = 2 * M * c * sphereArea R / (ℏ * N) := by
  have hmass : inferenceMass σ₀ ≠ 0 := by
    rw [inferenceMass]; exact inv_ne_zero (pow_ne_zero 2 hσ)
  have hNewton := (newtonG_isolated M c N kB (inferenceMass σ₀) ℏ Δx G R
    hN hkB hΔx hmass hM hc hℏ hG hR).mpr hbits
  refine ⟨gravitational_force_bitForm_inference M c N kB σ₀ ℏ Δx hN hkB hΔx,
    newtonG_eq_area_per_bit M c N kB (inferenceMass σ₀) ℏ Δx G R
      hN hkB hΔx hmass hM hc hℏ hG hR hNewton,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits,
    dust_traceReversed_source G c ρ hc,
    schwarzschildRadius_bitForm M G ℏ c N R hℏ hc hG hR hbits⟩

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant
