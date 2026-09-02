/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The generalized isotonic oscillator is a rapidity oscillator: link to the Compton clock

The hyperbolic factor `√(ξ²+1)` of the generalized isotonic potential (`GeneralizedIsotonicOscillator`,
Ghose-Choudhury et al. arXiv:1906.10387) is **the relativistic Lorentz factor**: with the isotonic coordinate
written in rapidity form `ξ = sinh η`, one has `√(ξ²+1) = cosh η = γ`, the base `√(ξ²+1) + ξ = eη` is the boost
(Doppler factor), and the potential collapses to a **pure `sinh²` rapidity oscillator**

`Ũ(ξ) = (c/2) sinh²((α+1)η/2)`  (`genIsotonicU_rapidity`).

This links the isotonic oscillator to the **Compton clock**: the very same `γ = cosh η = √(ξ²+1)` is the de Broglie
boost of the Compton frequency `ω_dB = γ ω_C` (`ComptonClock.FrequencyTrinity.deBroglie_eq_gamma_compton`). So the
isotonic oscillator's hyperbolic factor is the boost acting on the internal Compton clock `ℏω/c² = m` — the clock
whose single frequency underlies the Higgs-free mass origins (`yukawaMass`, `gravitationalMass` horizon entropy,
`topologicalMass` Chern-Simons; all equal `comptonMass (comptonFrequency m)` = `m`).

* **§A — the isotonic factor is the Lorentz factor.** **`sqrt_sq_add_one_eq_cosh_arsinh`** (`√(ξ²+1) = cosh(arsinh ξ)`)
  and **`sqrt_sq_add_one_add_eq_exp_arsinh`** (`√(ξ²+1) + ξ = e^{arsinh ξ}`, the boost).
* **§B — the rapidity form of the potential.** **`genIsotonicU_rapidity`** (`Ũ(sinh η) = (c/2) sinh²((α+1)η/2)`).
* **§C — the Compton-clock boost.** **`sqrt_sq_add_one_boosts_compton`** (`ω_dB(γ·mc²) = √(ξ²+1)·ω_C`, the isotonic
  Lorentz factor is the de Broglie boost of the Compton clock).

**Honest layering — the genuine link and its limit.** §A–§C are exact `Real.cosh`/`sinh`/`arsinh`/`exp` identities.
The genuine, formalized link is *Lorentzian* (rapidity): the isotonic hyperbolic factor **is** the Compton-clock
boost `γ`. The often-mentioned *spherical* dual — the "two 3-spheres as a single 4-sphere" picture — is the
**Euclidean/Wick-rotation continuation** `η → iθ` (under which `e^η → e^{iθ}` maps the unit hyperbola to the unit
circle and `sinh² → −sin²`): mathematically suggestive but **not** part of physlib, and **not** formalized here as
fact. This module establishes only the rapidity side; the 4-sphere dual remains a conjecture, deliberately left
un-formalized rather than asserted.

## References

* Ghose-Choudhury, Ghosh, Guha, Pandey, arXiv:1906.10387 (isotonic factor); the Compton frequency trinity of
  `ComptonClock.FrequencyTrinity`. Bridges `GeneralizedIsotonicOscillator` and the Compton clock.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IsotonicRapidityComptonClock


/-- **The isotonic factor is the Lorentz factor** `√(ξ²+1) = cosh(arsinh ξ)` — writing the isotonic coordinate as
`ξ = sinh η` (rapidity `η = arsinh ξ`), the hyperbolic factor is `cosh η = γ`, the relativistic Lorentz factor. -/
lemma sqrt_sq_add_one_eq_cosh_arsinh (ξ : ℝ) :
    Real.sqrt (ξ ^ 2 + 1) = Real.cosh (Real.arsinh ξ) := by
  rw [Real.cosh_arsinh]; congr 1; ring

/-- **The isotonic base is the boost** `√(ξ²+1) + ξ = e^{arsinh ξ}` — the Doppler/boost factor `eη = cosh η + sinh η`. -/
lemma sqrt_sq_add_one_add_eq_exp_arsinh (ξ : ℝ) :
    Real.sqrt (ξ ^ 2 + 1) + ξ = Real.exp (Real.arsinh ξ) := by
  rw [sqrt_sq_add_one_eq_cosh_arsinh, ← Real.cosh_add_sinh, Real.sinh_arsinh]


/-- **The generalized isotonic potential is a `sinh²` rapidity oscillator** `Ũ(sinh η) = (c/2) sinh²((α+1)η/2)` —
in the rapidity variable `η` (with `ξ = sinh η`), the two-branch generalized isotonic potential is exactly a pure
hyperbolic oscillator, the amplitude entering through the rapidity. -/
lemma genIsotonicU_rapidity (c α η : ℝ) :
    genIsotonicU c α (Real.sinh η) = c / 2 * Real.sinh ((α + 1) / 2 * η) ^ 2 := by
  have hbase : Real.sqrt (Real.sinh η ^ 2 + 1) + Real.sinh η = Real.exp η := by
    rw [sqrt_sq_add_one_add_eq_exp_arsinh, Real.arsinh_sinh]
  unfold genIsotonicU
  rw [hbase, ← Real.exp_mul, ← Real.exp_mul,
    show η * ((α + 1) / 2) = (α + 1) / 2 * η from by ring,
    show η * (-((α + 1) / 2)) = -((α + 1) / 2 * η) from by ring,
    show Real.exp ((α + 1) / 2 * η) - Real.exp (-((α + 1) / 2 * η))
      = 2 * Real.sinh ((α + 1) / 2 * η) from by rw [Real.sinh_eq]; ring]
  ring


/-- **The isotonic Lorentz factor boosts the Compton clock** `ω_dB(γ·mc²) = √(ξ²+1)·ω_C` — the isotonic hyperbolic
factor `γ = √(ξ²+1) = cosh η` is exactly the de Broglie boost of the Compton frequency
(`FrequencyTrinity.deBroglie_eq_gamma_compton`): the isotonic oscillator's geometry is the boost acting on the
internal Compton clock `ℏω/c² = m`. -/
lemma sqrt_sq_add_one_boosts_compton (m c ħ ξ : ℝ) :
    deBroglieFrequency (Real.sqrt (ξ ^ 2 + 1) * (m * c ^ 2)) ħ
      = Real.sqrt (ξ ^ 2 + 1) * comptonFrequency m c ħ :=
  deBroglie_eq_gamma_compton (Real.sqrt (ξ ^ 2 + 1)) m c ħ

end Physlib.QuantumMechanics.ComplexAction.IsotonicRapidityComptonClock
