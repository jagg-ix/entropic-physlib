/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravLapse.HyperbolicInterval
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

/-!
# The BCJ double copy meets the Jacobson-diamond time reversal

Links `BCJDoubleCopy.ColorKinematicsDoubleCopy` to the Jacobson causal-diamond / Nagao–Nielsen lapse arc of
`GravLapse.HyperbolicInterval`, through the single fact that antiunitary time reversal acts as
`θ ↦ −θ` on the hyperbolic interval. The connection is the BCJ slogan **gravity = gauge²**: the double copy
*squares away* the time-reversal sign.

Build a BCJ channel from the diamond Bogoliubov mode (`E = cosh θ`, `|p| = sinh θ`, `Δ = 1`): the **gauge
kinematic numerator** is the diamond momentum `n = sinh θ`, and the **propagator** is the mass shell
`D = bogoliubovEnergy(sinh θ, 1)² = cosh²θ > 0`. Then the **double-copy diagonal** is the diamond velocity
squared,

  `n²/D = sinh²θ / cosh²θ = tanh²θ`.

Under time reversal `θ ↦ −θ`:

* the **gauge numerator** `n = sinh θ` flips sign (`diamondBCJ_numerator_timeReversal`) — `T`-odd, like the
  diamond rapidity / horizon momentum;
* the **propagator / mass shell** `D = cosh²θ` is invariant (`diamondBCJ_propagator_timeReversal`) — the
  Bogoliubov energy and gap `Δ²` are preserved;
* hence the **double copy** `n²/D = tanh²θ` is invariant (`diamondBCJ_doublecopy_timeReversal_invariant`) —
  the gravity side is `T`-even even though the gauge numerator is `T`-odd.

So the Bern–Carrasco–Johansson double copy is the algebraic shadow of the diamond's antiunitary
`T`: it converts the velocity-reversing gauge numerator into the velocity-squared, mass-shell-locked
gravity amplitude — the same invariant hyperbolic interval (`= lorentzianForm`, the Nagao–Nielsen
convergence cone) that the lapse / boost-vector / diamond triangle records.

* **§A — the diamond BCJ channel** (`diamondBCJTriple`, `diamondBCJ_diagonal`, `diamondBCJ_diagonal_nonneg`).
  The double-copy diagonal `n²/D = tanh²θ` (diamond velocity²), nonnegative by
  `BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDoubleCopy_diagonal_nonneg`.
* **§B — time reversal `θ ↦ −θ`** (`diamondBCJ_numerator_timeReversal`, `diamondBCJ_propagator_timeReversal`,
  `diamondBCJ_doublecopy_timeReversal_invariant`). Gauge numerator `T`-odd, mass-shell propagator and the
  double copy `T`-even.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, arXiv:0805.3993 (the double copy).
* Repo dependencies: `BCJDoubleCopy.ColorKinematicsDoubleCopy` (`BCJTriple`, `bcjDoubleCopy_diagonal_nonneg`);
  `CausalDiamond.Helicity.diamond_horizon_energy` (`bogoliubovEnergy(sinh θ,1) = cosh θ`);
  `GravLapse.HyperbolicInterval` (the lapse / diamond / NN-contour triangle at `θ ↦ −θ`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DiamondTimeReversal

open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity

/-! ## §A — the diamond BCJ channel -/

/-- **The BCJ channel of the Jacobson-diamond Bogoliubov mode.** Kinematic numerator = diamond momentum
`n = sinh θ`; propagator = mass shell `D = bogoliubovEnergy(sinh θ, 1)² = cosh²θ > 0`. -/
noncomputable def diamondBCJTriple (θ : ℝ) : BCJTriple where
  numerator := Real.sinh θ
  color := Real.sinh θ
  propagator := (bogoliubovEnergy (Real.sinh θ) 1) ^ 2
  prop_pos := by rw [diamond_horizon_energy]; positivity

/-- **[Double copy = diamond velocity²] `n²/D = tanh²θ`.** The BCJ double-copy diagonal of the diamond
channel is the squared diamond velocity `(sinh θ / cosh θ)²`, using `diamond_horizon_energy`
(`bogoliubovEnergy(sinh θ,1) = cosh θ`). -/
theorem diamondBCJ_diagonal (θ : ℝ) :
    (diamondBCJTriple θ).numerator ^ 2 / (diamondBCJTriple θ).propagator = Real.tanh θ ^ 2 := by
  simp only [diamondBCJTriple, diamond_horizon_energy]
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]

/-- **The diamond double-copy diagonal is nonnegative** — consuming
`BCJDoubleCopy.ColorKinematicsDoubleCopy.bcjDoubleCopy_diagonal_nonneg`. -/
theorem diamondBCJ_diagonal_nonneg (θ : ℝ) :
    0 ≤ (diamondBCJTriple θ).numerator ^ 2 / (diamondBCJTriple θ).propagator :=
  bcjDoubleCopy_diagonal_nonneg (diamondBCJTriple θ)

/-! ## §B — time reversal `θ ↦ −θ` -/

/-- **[`T`-odd] The gauge numerator (diamond momentum) flips sign** `n(−θ) = −n(θ)` — `sinh` is odd, the
horizon momentum / rapidity reverses. -/
theorem diamondBCJ_numerator_timeReversal (θ : ℝ) :
    (diamondBCJTriple (-θ)).numerator = -(diamondBCJTriple θ).numerator := by
  simp [diamondBCJTriple, Real.sinh_neg]

/-- **[`T`-even] The propagator (mass shell) is invariant** `D(−θ) = D(θ)` — `bogoliubovEnergy(sinh θ,1) =
cosh θ` is even, the Bogoliubov energy and gap `Δ²` are preserved. -/
theorem diamondBCJ_propagator_timeReversal (θ : ℝ) :
    (diamondBCJTriple (-θ)).propagator = (diamondBCJTriple θ).propagator := by
  simp only [diamondBCJTriple, diamond_horizon_energy, Real.cosh_neg]

/-- **[Gravity is `T`-even] The double copy `n²/D = tanh²θ` is time-reversal invariant.** Although the gauge
numerator `n = sinh θ` is `T`-odd (`diamondBCJ_numerator_timeReversal`), the double-copied gravity quantity
`n²/D` squares the sign away and is locked to the invariant mass shell — `tanh²(−θ) = tanh²θ`. The BCJ double
copy is the algebraic shadow of the diamond's antiunitary, velocity-reversing time reversal. -/
theorem diamondBCJ_doublecopy_timeReversal_invariant (θ : ℝ) :
    (diamondBCJTriple (-θ)).numerator ^ 2 / (diamondBCJTriple (-θ)).propagator
      = (diamondBCJTriple θ).numerator ^ 2 / (diamondBCJTriple θ).propagator := by
  rw [diamondBCJ_diagonal, diamondBCJ_diagonal, Real.tanh_neg]; ring

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DiamondTimeReversal

end
