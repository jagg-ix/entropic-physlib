/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

/-!
# The NN lapse `N − iε` is the hyperbolic spacetime interval — closing the boost/diamond triangle

The Minkowski spacetime interval written with hyperbolic functions already lives in the repo as
`TimeOperator.HyperbolicPoincareLorentzMisra.boostVector_lorentzianForm`: `L(Δcosh θ + iΔsinh θ) = Δ²`
(`cosh²θ − sinh²θ = 1`), where `L = ComplexDelta.Convergence.lorentzianForm` is *simultaneously* the
Minkowski interval and the Nagao–Nielsen path-integral convergence cone. This file closes the last
connector: the **Banihashemi–Jacobson lapse** `N − iε` (`WickRotation.complexEnergy N ε`) is the same
hyperbolic interval point, identifying it with the boost vector and the Jacobson causal-diamond rapidity.

Under the identification `N = Δcosh θ`, `ε = Δsinh θ`:

| | time / `Re` | space / `Im` | interval `L` | velocity |
|---|---|---|---|---|
| boost vector | `Δcosh θ` | `Δsinh θ` | `Δ²` | `tanh θ` |
| **lapse `N − iε`** | `N` | `ε` | `N² − ε²` | `ε/N` |
| diamond `η = R⋆/L` | `cosh η` | `sinh η` | `1` | `R/L` |

* **§A — the lapse is on the mass shell** (`lapse_on_massShell`). `L(complexEnergy (Δcosh θ) (Δsinh θ)) = Δ²`
  — the NN lapse contour point sits on the Minkowski mass shell of invariant gap `Δ`, derived from
  `boostVector_lorentzianForm` through the lapse's own `lapse_lorentzianForm_eq`. The lapse displacement `ε`
  is the spacelike direction; the gap `Δ` is the invariant interval.
* **§B — the lapse displacement ratio is the rapidity velocity** (`lapse_velocity_eq_rapidity`).
  `ε/N = (Δsinh θ)/(Δcosh θ) = tanh θ` (`boostVector_velocity`): the displacement-to-lapse ratio is the
  relativistic velocity `β = tanh θ`.
* **§C — the lapse rapidity velocity IS the causal-diamond velocity** (`lapse_velocity_eq_diamond`,
  `lapse_N_eq_diamondEnergy`). `tanh θ = sinh θ / bogoliubovEnergy(sinh θ, 1)` is the Jacobson causal-diamond
  velocity `R/L = tanh(R⋆/L)` (`CausalDiamond.Helicity`), and the unit-gap lapse component
  `N = cosh θ = bogoliubovEnergy(sinh θ, 1)` is the diamond horizon energy `E = cosh(R⋆/L)`. So the lapse
  `N − iε` *is* the diamond's Bogoliubov mode `(E = cosh, |p| = sinh, Δ = 1)`.
* **§D — the triangle** (`lapse_boost_diamond_triangle`). For the unit gap, the lapse `N − iε` at
  `(cosh θ, sinh θ)` is on the mass shell `L = 1` and its velocity is the diamond velocity — closing
  Jacobson thermodynamics (diamond rapidity) ↔ Nagao–Nielsen `p,q` QM (`L` = NN cone) ↔ the NN lapse
  `N − iε`, all at the single object `lorentzianForm`.

## References

* B. Banihashemi, T. Jacobson, arXiv:2405.10307v3 (2025), DOI `10.48550/arXiv.2405.10307` — the `N − iε`
  lapse.
* T. Jacobson, M. Visser, arXiv:1812.01596 — causal-diamond gravitational thermodynamics (the diamond
  rapidity `R⋆/L`).
* K. Nagao, H. B. Nielsen, Prog. Theor. Phys. 126 (2011) 1021 — the Lorentzian convergence form
  `L = lorentzianForm`.
* N. N. Bogoljubov (1958) — the quasiparticle energy `bogoliubovEnergy(ξ, Δ) = √(ξ² + Δ²)`.
* Repo carriers: `TimeOperator.HyperbolicPoincareLorentzMisra` (`boostVector_lorentzianForm`, `boostVector_velocity`),
  `CausalDiamond.Helicity` (`diamond_velocity_eq_bogoliubov`, `diamond_horizon_energy`),
  `GravLapse.ContourEntropicTime` (`lapse_lorentzianForm_eq`), `WickRotation` (`complexEnergy`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.HyperbolicInterval

open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.NonHermitian.WickRotation


/-- **[Link lapse ↔ boost vector] The lapse contour point is on the hyperbolic mass shell.** At
`N = Δcosh θ`, `ε = Δsinh θ`, the Banihashemi–Jacobson lapse `complexEnergy N ε = N − iε` has Minkowski
interval `L(N − iε) = N² − ε² = Δ²` — the same mass shell as the boost vector `Δcosh θ + iΔsinh θ`
(`boostVector_lorentzianForm`). The lapse displacement `ε` is the spacelike leg; the invariant interval is
the gap `Δ`. -/
lemma lapse_on_massShell (Δ θ : ℝ) :
    lorentzianForm (complexEnergy (Δ * Real.cosh θ) (Δ * Real.sinh θ)) = Δ ^ 2 := by
  rw [lapse_lorentzianForm_eq, ← lorentzianForm_ofReal_add_mul_I]
  exact boostVector_lorentzianForm Δ θ


/-- **[Link] The lapse displacement-to-lapse ratio is the relativistic velocity** `ε/N = tanh θ`. With
`N = Δcosh θ`, `ε = Δsinh θ`, the ratio `ε/N = (Δsinh θ)/(Δcosh θ) = tanh θ` (`boostVector_velocity`): the
`iε`-displacement, measured against the lapse, is the rapidity velocity `β`. -/
lemma lapse_velocity_eq_rapidity (Δ θ : ℝ) (hΔ : Δ ≠ 0) :
    (Δ * Real.sinh θ) / (Δ * Real.cosh θ) = Real.tanh θ :=
  boostVector_velocity Δ θ hΔ


/-- **[Link lapse ↔ Jacobson diamond] The lapse rapidity velocity is the causal-diamond velocity.**
`tanh θ = sinh θ / bogoliubovEnergy(sinh θ, 1)` is the Jacobson causal-diamond velocity `R/L = tanh(R⋆/L)`
(`CausalDiamond.Helicity.diamond_velocity_eq_bogoliubov`): the unit-gap lapse's velocity is the
diamond's area-radius ratio. -/
lemma lapse_velocity_eq_diamond (θ : ℝ) :
    Real.tanh θ = Real.sinh θ / bogoliubovEnergy (Real.sinh θ) 1 :=
  diamond_velocity_eq_bogoliubov θ

/-- **[Link lapse ↔ Jacobson diamond] The unit-gap lapse `N` is the diamond horizon energy.**
`N = cosh θ = bogoliubovEnergy(sinh θ, 1)` is the causal-diamond conformal-Killing-horizon energy
`E = cosh(R⋆/L)` (`CausalDiamond.Helicity.diamond_horizon_energy`): the lapse time-component is the
diamond/Bogoliubov energy, the displacement `ε = sinh θ` is its momentum `|p|`, and the gap `Δ = 1` is the
mass-shell interval. The NN lapse `N − iε` *is* the diamond's Bogoliubov mode. -/
lemma lapse_N_eq_diamondEnergy (θ : ℝ) :
    Real.cosh θ = bogoliubovEnergy (Real.sinh θ) 1 :=
  (diamond_horizon_energy θ).symm


/-- **[Triangle] The NN lapse `N − iε`, the boost vector, and the Jacobson diamond rapidity coincide.** For
the unit gap, the lapse `complexEnergy (cosh θ) (sinh θ) = cosh θ − i sinh θ`:

* lies on the Minkowski mass shell, `L = 1` (the boost-vector interval, `boostVector_lorentzianForm`);
* has velocity `ε/N = sinh θ / cosh θ = sinh θ / bogoliubovEnergy(sinh θ, 1)` — the Jacobson causal-diamond
  velocity `R/L = tanh(R⋆/L)`.

So `lorentzianForm` (the Minkowski interval = Nagao–Nielsen `p,q` convergence cone) carries the NN lapse
`N − iε`, the boost vector, and the Jacobson diamond rapidity as one and the same hyperbolic-interval point. -/
lemma lapse_boost_diamond_triangle (θ : ℝ) :
    lorentzianForm (complexEnergy (Real.cosh θ) (Real.sinh θ)) = 1
      ∧ Real.sinh θ / Real.cosh θ = Real.sinh θ / bogoliubovEnergy (Real.sinh θ) 1 := by
  refine ⟨?_, ?_⟩
  · have h := lapse_on_massShell 1 θ; simpa using h
  · rw [← Real.tanh_eq_sinh_div_cosh, lapse_velocity_eq_diamond]

end Physlib.QuantumMechanics.ComplexAction.GravLapse.HyperbolicInterval

end
