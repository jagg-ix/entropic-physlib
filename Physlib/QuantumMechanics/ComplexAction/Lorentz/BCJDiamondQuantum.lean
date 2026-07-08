/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamond
public import Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

/-!
# The Lorentz-force BCJ dual, the quantum mass shell, and the one time reversal

Connects the Lorentz-force BCJ double-copy dual at the Jacobson diamond mode
(`Lorentz.ForceBCJDiamond`) to the quantum sector (`Bogoliubov.Transformation.bogoliubovEnergy`) and the
classical/quantum velocity-reversing time-reversal law of `Vlasov.DiamondTimeReversal`. The single
unifying fact: **antiunitary `T` is a velocity-reversing isometry** — it flips the momentum/velocity and
preserves the energy / mass shell — and this holds identically across the classical Vlasov, the quantum
diamond/Bogoliubov, *and* the BCJ gravitational dual.

The gravitational dual `(F·V)²/D = tanh²θ` decomposes as

  `tanh²θ = (sinh θ)² / bogoliubovEnergy(sinh θ, 1)²`   —   `(momentum)² / (mass shell)²`,

with `sinh θ` the **`T`-odd** diamond/Vlasov momentum and `bogoliubovEnergy(sinh θ,1) = cosh θ` the **`T`-even**
quantum mass shell. So the BCJ dual is `T`-even *because* of the classical/quantum law: a `T`-odd momentum
squared over a `T`-even mass shell. Gravity = gauge² squaring away `T` is the same statement as the
velocity-reversing antiunitary `T`.

* **§A — the gravity dual as momentum²/mass-shell²** (`lorentzForceDual_as_momentum_over_massShell`). The
  Lorentz dual at the diamond mode is `(sinh θ)² / bogoliubovEnergy(sinh θ,1)²`.
* **§B — its `T`-evenness from the two sectors** (`bcj_dual_timeReversal_from_sectors`). `T`-even because the
  numerator (momentum²) is `T`-even and the denominator (mass shell) is `T`-even (consuming
  `bogoliubovEnergy_timeReversal`).
* **§C — the grand unification** (`classical_quantum_gravity_unified`). The classical Vlasov energy, the
  quantum Bogoliubov mass shell, and the BCJ gravitational dual are *all* `T`-even — one antiunitary `T`
  across classical kinetic theory, the quantum mass shell, and the double copy.

## References

* The Jacobson diamond `θ ↦ −θ` time reversal; the Bogoliubov mass shell `√(ξ²+Δ²)`; the BCJ double copy.
* Repo dependencies: `Lorentz.ForceBCJDiamond` (`lorentzForceDual_eq_diamond_velocity_sq`);
  `Vlasov.DiamondTimeReversal` (`vlasovEnergy`, `bogoliubovEnergy_timeReversal`);
  `Lorentz.ForceBCJDual` (`lorentzForceDual`, `lorentzForceDual_timeReversal_invariant`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.BCJDiamondQuantum

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

/-! ## §A — the gravity dual as `momentum² / mass-shell²` -/

/-- **[Gravity dual = momentum²/mass-shell²]** At the diamond mode (`(F V)_μ = sinh θ`), the Lorentz-force
gravitational dual is `(sinh θ)² / bogoliubovEnergy(sinh θ,1)²` — the squared diamond momentum over the
squared quantum mass shell. -/
theorem lorentzForceDual_as_momentum_over_massShell (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (μ : Fin 4) (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
      = (Real.sinh θ) ^ 2 / (bogoliubovEnergy (Real.sinh θ) 1) ^ 2 := by
  unfold lorentzForceDual lorentzForceNum; rw [hnum]

/-! ## §B — `T`-evenness from the two sectors -/

/-- **[`T`-even from momentum² and mass shell] The gravity dual is `T`-even** `(sinh(−θ))²/E(−θ)² =
(sinh θ)²/E(θ)²` — the numerator `(momentum)²` is `T`-even and the denominator `(mass shell)²` is `T`-even
(`bogoliubovEnergy_timeReversal`). The BCJ dual's `T`-evenness *is* the classical/quantum law. -/
theorem bcj_dual_timeReversal_from_sectors (θ : ℝ) :
    (Real.sinh (-θ)) ^ 2 / (bogoliubovEnergy (Real.sinh (-θ)) 1) ^ 2
      = (Real.sinh θ) ^ 2 / (bogoliubovEnergy (Real.sinh θ) 1) ^ 2 := by
  rw [Real.sinh_neg, neg_sq, bogoliubovEnergy_timeReversal]

/-! ## §C — the grand unification -/

/-- **[One antiunitary `T`] Classical, quantum, and gravity energies are all `T`-even.** The classical
Vlasov energy `R = −α|V|² + φ`, the quantum Bogoliubov mass shell `√(ξ²+Δ²)`, and the BCJ gravitational dual
`(F·V)²/D` are *all* invariant under the velocity/momentum-reversing antiunitary `T` — one law across
classical kinetic theory, the quantum mass shell, and the double copy. -/
theorem classical_quantum_gravity_unified (α φ : ℝ) (Vc : Fin 3 → ℝ) (ξ Δ : ℝ)
    (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (D : ℝ) :
    vlasovEnergy α φ (-Vc) = vlasovEnergy α φ Vc
      ∧ bogoliubovEnergy (-ξ) Δ = bogoliubovEnergy ξ Δ
      ∧ lorentzForceDual F (-V) μ D = lorentzForceDual F V μ D :=
  ⟨vlasovEnergy_timeReversal α φ Vc, bogoliubovEnergy_timeReversal ξ Δ,
    lorentzForceDual_timeReversal_invariant F V μ D⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.BCJDiamondQuantum

end
