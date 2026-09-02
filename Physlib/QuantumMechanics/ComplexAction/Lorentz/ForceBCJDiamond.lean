/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DiamondTimeReversal

/-!
# The Lorentz-force BCJ dual at the Jacobson diamond mode

Connects the BCJ double-copy dual of the Lorentz force (`Lorentz.ForceBCJDual`) to the Jacobson causal-diamond
/ Nagao–Nielsen time-reversal structure (`BCJDoubleCopy.DiamondTimeReversal`,
`CausalDiamond.Helicity.diamond_horizon_energy`). Evaluated **at the diamond mode** — the gauge Lorentz
numerator set to the diamond momentum `|p| = sinh θ`, the mass-shell propagator set to the diamond horizon
energy squared `cosh²θ = bogoliubovEnergy(sinh θ, 1)²` — the Lorentz-force gravitational dual `(F·V)²/D` is
exactly the **squared diamond velocity** `tanh²θ`, the diamond BCJ double-copy diagonal.

So the two double-copy duals coincide: the gravitational dual of the Lorentz force *is* the diamond's
gravity-side amplitude, and both are time-reversal (`θ ↦ −θ`) invariant — the gauge force / diamond momentum
is `T`-odd, the gravitational dual / diamond velocity² is `T`-even. The single antiunitary `T` of the §2.4
temporal-orientation framework — reversing the diamond rapidity `R⋆/L`, the boost velocity, and the
Nagao–Nielsen displacement `ε`, while preserving the mass shell `Δ²` / horizon energy `cosh θ` / NN cone
`lorentzianForm = p² − q²` — is the same `T` the BCJ double copy squares away.

* **§A — the Lorentz dual at the diamond mode** (`lorentzForceDual_eq_diamond_velocity_sq`,
  `lorentzForceDual_eq_diamondBCJ`). `(F·V)²/cosh²θ = tanh²θ`, the diamond BCJ diagonal (consuming
  `diamond_horizon_energy`).
* **§B — the shared time-reversal invariance** (`lorentzForce_and_diamond_dual_invariant`). Both
  gravitational duals are `T`-even — the Lorentz dual (`lorentzForceDual_timeReversal_invariant`) and the
  diamond diagonal (`diamondBCJ_doublecopy_timeReversal_invariant`) are one statement: gravity = gauge²
  squares away the velocity-reversing `T`.

## References

* The Jacobson diamond rapidity `R⋆/L` and its `θ ↦ −θ` time reversal; the Bogoliubov mass shell
  `√(ξ²+Δ²)`; the Nagao–Nielsen convergence cone `lorentzianForm`.
* Repo carriers: `Lorentz.ForceBCJDual` (`lorentzForceDual`); `BCJDoubleCopy.DiamondTimeReversal`
  (`diamondBCJTriple`, `diamondBCJ_diagonal`, `diamondBCJ_doublecopy_timeReversal_invariant`);
  `CausalDiamond.Helicity.diamond_horizon_energy`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamond

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DiamondTimeReversal


/-- **[Lorentz dual = diamond velocity²] `(F·V)²/cosh²θ = tanh²θ`.** With the gauge Lorentz numerator at the
diamond momentum (`(F V)_μ = sinh θ`) and the mass-shell propagator the diamond horizon energy squared
(`bogoliubovEnergy(sinh θ,1)² = cosh²θ`), the Lorentz-force gravitational dual equals the squared diamond
velocity (consuming `diamond_horizon_energy`). -/
lemma lorentzForceDual_eq_diamond_velocity_sq (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (μ : Fin 4) (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2) = Real.tanh θ ^ 2 := by
  unfold lorentzForceDual lorentzForceNum
  rw [hnum, diamond_horizon_energy, Real.tanh_eq_sinh_div_cosh, div_pow]

/-- **[Lorentz dual = diamond BCJ diagonal] The Lorentz-force dual at the diamond mode is the diamond BCJ
double-copy diagonal** `(diamondBCJTriple θ).numerator²/(diamondBCJTriple θ).propagator` — the gravitational
dual of the Lorentz force *is* the diamond's gravity-side amplitude. -/
lemma lorentzForceDual_eq_diamondBCJ (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (μ : Fin 4) (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
      = (diamondBCJTriple θ).numerator ^ 2 / (diamondBCJTriple θ).propagator := by
  rw [lorentzForceDual_eq_diamond_velocity_sq F V μ θ hnum, diamondBCJ_diagonal]


/-- **[Both `T`-even] One time reversal squared away.** The Lorentz-force gravitational dual and the diamond
BCJ diagonal are *both* `θ ↦ −θ` invariant — the gauge Lorentz force / diamond momentum is `T`-odd, the
gravitational dual / diamond velocity² is `T`-even. Gravity = gauge² squares away the single antiunitary `T`
(the diamond rapidity, boost velocity, and NN displacement `ε` all reverse; the mass shell stays fixed). -/
lemma lorentzForce_and_diamond_dual_invariant (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (μ : Fin 4) (D : ℝ) (θ : ℝ) :
    lorentzForceDual F (-V) μ D = lorentzForceDual F V μ D
      ∧ (diamondBCJTriple (-θ)).numerator ^ 2 / (diamondBCJTriple (-θ)).propagator
          = (diamondBCJTriple θ).numerator ^ 2 / (diamondBCJTriple θ).propagator :=
  ⟨lorentzForceDual_timeReversal_invariant F V μ D,
    diamondBCJ_doublecopy_timeReversal_invariant θ⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamond

end
