/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-!
# The BCJ double-copy dual of the Lorentz force

Uses the Bern–Carrasco–Johansson formalization (`BCJDoubleCopy.ColorKinematicsDoubleCopy`) to construct the
**double-copy dual of the Lorentz force**. The Lorentz force `F^μ_ν V^ν` is the *gauge*-side force on a
charged particle (the field strength `F = dA` contracted with the velocity); being linear in `V` it is
**`T`-odd** under the velocity reversal `V ↦ −V` of the Vlasov / diamond time reversal. Its BCJ double copy —
`(F·V)²/D`, the gauge numerator squared over the mass-shell propagator — is the **gravity**-side dual, and it
is **`T`-even**: the double copy "gravity = gauge²" *squares away* the velocity reversal, exactly as the
Jacobson-diamond channel does (`BCJDoubleCopy.DiamondTimeReversal.diamondBCJ_doublecopy_timeReversal_invariant`).

So the Lorentz force has a gravitational dual that is nonnegative and time-reversal invariant — the BCJ shadow
of the geodesic/tidal force, with the gauge force's `T`-odd sign squared away.

* **§A — the Lorentz force as a gauge BCJ numerator** (`lorentzForceNum`, `lorentzForceNum_timeReversal`,
  `lorentzForceTriple`). `n = (F V)_μ`, `T`-odd; packaged as a BCJ channel with a positive mass-shell
  propagator.
* **§B — the gravitational dual via the double copy** (`lorentzForceDual`, `lorentzForceDual_nonneg`,
  `lorentzForceDual_timeReversal_invariant`). `n²/D ≥ 0` (consuming `bcjDoubleCopy_diagonal_nonneg`) and
  `T`-even — gravity = gauge² removes the sign.
* **§C — the Maxwell instance** (`maxwellLorentzForceDual_nonneg`, `maxwellLorentzForceDual_invariant`). For
  the field strength `F = faraday k A`, the Lorentz-force dual of the Maxwell field; the field does no work
  on the 4-velocity (`F^μ_ν U^μ U^ν = 0`, the antisymmetry — cf. `Vlasov.MaxwellEM.faraday_no_work`),
  yet its double-copy dual `(F U)²/D` is a nonnegative `T`-even gravitational force.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, arXiv:0805.3993 (the double copy); the gauge/gravity Lorentz
  force ↔ geodesic correspondence.
* Repo dependencies: `BCJDoubleCopy.ColorKinematicsDoubleCopy` (`BCJTriple`, `bcjDoubleCopy_diagonal_nonneg`);
  `PTSymmetricQFT.MaxwellFaraday` (`faraday`); cf. `BCJDoubleCopy.DiamondTimeReversal`,
  `Vlasov.DiamondTimeReversal`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual

open Matrix
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## §A — the Lorentz force as a gauge BCJ numerator -/

/-- **The Lorentz force** `(F^μ_ν V^ν)_μ` — the gauge force, the field strength contracted with the
4-velocity, a component. -/
def lorentzForceNum (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) : ℝ := (F *ᵥ V) μ

/-- **[`T`-odd] The Lorentz force flips under velocity reversal** `(F(−V))_μ = −(F V)_μ` — the gauge force
is `T`-odd, like the Vlasov velocity and the diamond momentum. -/
theorem lorentzForceNum_timeReversal (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) :
    lorentzForceNum F (-V) μ = -(lorentzForceNum F V μ) := by
  simp [lorentzForceNum, Matrix.mulVec_neg]

/-- **The BCJ gauge channel of the Lorentz force** — kinematic numerator `(F V)_μ`, positive mass-shell
propagator `D`. -/
noncomputable def lorentzForceTriple (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (D : ℝ) (hD : 0 < D) : BCJTriple where
  numerator := lorentzForceNum F V μ
  color := lorentzForceNum F V μ
  propagator := D
  prop_pos := hD

/-! ## §B — the gravitational dual via the double copy -/

/-- **The double-copy dual of the Lorentz force** `(F V)²/D` — the gravity-side force, the gauge numerator
squared over the mass-shell propagator. -/
noncomputable def lorentzForceDual (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (D : ℝ) : ℝ := (lorentzForceNum F V μ) ^ 2 / D

/-- **The gravitational dual is nonnegative** — consuming `bcjDoubleCopy_diagonal_nonneg` for the Lorentz
channel. -/
theorem lorentzForceDual_nonneg (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (D : ℝ) (hD : 0 < D) : 0 ≤ lorentzForceDual F V μ D :=
  bcjDoubleCopy_diagonal_nonneg (lorentzForceTriple F V μ D hD)

/-- **[Gravity = gauge² squares `T` away] The Lorentz-force dual is `T`-even** `(F(−V))²/D = (F V)²/D` —
although the gauge Lorentz force is `T`-odd (`lorentzForceNum_timeReversal`), the double-copied gravitational
dual squares the sign away and is time-reversal invariant, exactly as the diamond channel
(`diamondBCJ_doublecopy_timeReversal_invariant`). -/
theorem lorentzForceDual_timeReversal_invariant (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (μ : Fin 4) (D : ℝ) : lorentzForceDual F (-V) μ D = lorentzForceDual F V μ D := by
  unfold lorentzForceDual; rw [lorentzForceNum_timeReversal]; ring

/-! ## §C — the Maxwell instance -/

/-- **The Maxwell Lorentz-force dual is nonnegative** — for the field strength `F = dA`. -/
theorem maxwellLorentzForceDual_nonneg (k A V : Fin 4 → ℝ) (μ : Fin 4) (D : ℝ) (hD : 0 < D) :
    0 ≤ lorentzForceDual (faraday k A) V μ D :=
  lorentzForceDual_nonneg (faraday k A) V μ D hD

/-- **The Maxwell Lorentz-force dual is `T`-even** — the gravitational dual of the Maxwell field's Lorentz
force is time-reversal invariant. -/
theorem maxwellLorentzForceDual_invariant (k A V : Fin 4 → ℝ) (μ : Fin 4) (D : ℝ) :
    lorentzForceDual (faraday k A) (-V) μ D = lorentzForceDual (faraday k A) V μ D :=
  lorentzForceDual_timeReversal_invariant (faraday k A) V μ D

end Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual

end
