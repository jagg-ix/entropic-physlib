/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkFrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence

/-!
# From the walk's coin angle to the inverse-square law and Jacobson's equation of state

`QuantumWalkFrequencyTrinity` runs the chain `coin angle → clock → mass → Yukawa coupling`, with the
mass–clock step discharged rather than assumed.  The gravitational sector continues it, and every
link is already in the library:

* `ComptonCellNewtonConstant.newtonG_from_comptonCellBits` — the `G`-free Compton-cell count gives
  `G = ħc/m²` (`newtonG_compton`);
* `EntropicClockComptonAnchor.comptonAnchored_newtonG_eq_from_clockFrequency` — eliminating the mass
  through `ω₀ = mc²/ħ` gives **`G = c⁵/(ħ ω₀²)`**, Newton's constant from the clock frequency alone;
* `EntropicNewtonConstantConvergence.newtonAcceleration` — the inverse-square field `G M/r²`;
* `ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius` — the Clausius balance on every
  null direction outputs `G_ab + Λ g_ab = 8πG · T_ab`.

Since the walk fixes `ω₀ = θ/2` (`QuantumWalkZitterbewegung`), substituting gives

  **`G = 4c⁵/(ħ θ²)`**

so the same single dial that sets the mass and the Yukawa coupling also sets Newton's constant — and
through it both the inverse-square acceleration `G M/r²` and the Einstein coupling `8πG` that
Jacobson's equation of state outputs.  One parameter, from the discrete walk to the field equation.

Scope.  The `G = ħc/m²` step is conditional in exactly the way `EntropicClockComptonAnchor` records:
it is the Compton-cell = screen-scale identification, not an independent measurement of `G`, and the
"mass" there is the screen/cell scale `λ_C = ħ/mc` rather than a particle species.  Jacobson's
theorem is likewise conditional on its Clausius hypothesis holding for every null direction, with the
shared kinematic cancellation and the area-entropy law as standard-GR inputs.  What is added here is
the composition, not new gravitational content.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkClockGravityChain

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence

/-! ### §A — Newton's constant from the coin angle -/

/-- Newton's constant as the Compton-cell count gives it, `G = ħc/m²`. -/
def comptonCellG (ħ c m : ℝ) : ℝ := ħ * c / m ^ 2

/-- **`G` from the clock frequency.**  Eliminating the mass through `ω_C = mc²/ħ` writes the
Compton-cell constant as `c⁵/(ħ ω²)` — Newton's constant as a function of the clock alone.  This is
`comptonAnchored_newtonG_eq_from_clockFrequency` stated on the bare frequency. -/
theorem comptonCellG_eq_from_frequency {m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonCellG ħ c m = c ^ 5 / (ħ * comptonFrequency m c ħ ^ 2) := by
  unfold comptonCellG comptonFrequency
  field_simp

/-- **`G` from the coin angle.**  With the walk matched so that `ω_C = θ/2`, Newton's constant is
`4c⁵/(ħθ²)`: the discrete walk's single dial fixes the gravitational coupling. -/
theorem comptonCellG_eq_from_coin_angle {θ m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    comptonCellG ħ c m = 4 * c ^ 5 / (ħ * θ ^ 2) := by
  have hω : comptonFrequency m c ħ = θ / 2 := by
    rw [walkZitterFrequency_eq_coin_angle] at hcoin; linarith
  rw [comptonCellG_eq_from_frequency hm hc hħ, hω]
  field_simp
  ring

/-! ### §B — The inverse-square law at that constant -/

/-- **The inverse-square acceleration carried by the coin angle.**  Substituting the walk-fixed
constant into `newtonAcceleration G M r = G M/r²` gives `4c⁵M/(ħθ²r²)`: the `1/r²` law with its
coefficient supplied by the walk. -/
theorem newtonAcceleration_from_coin_angle {θ m c ħ M r : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    newtonAcceleration (comptonCellG ħ c m) M r = 4 * c ^ 5 * M / (ħ * θ ^ 2 * r ^ 2) := by
  unfold newtonAcceleration
  rw [comptonCellG_eq_from_coin_angle hm hc hħ hcoin]
  field_simp

/-- **The `1/r²` shape is the walk's, not an extra input.**  At fixed source the acceleration scales
as the inverse square of the distance, with the whole coin-angle dependence in the prefactor — so the
walk sets the strength of gravity and the geometry sets its falloff. -/
theorem newtonAcceleration_inverse_square {G M r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
    newtonAcceleration G M r₁ * r₁ ^ 2 = newtonAcceleration G M r₂ * r₂ ^ 2 := by
  unfold newtonAcceleration
  field_simp

/-! ### §C — Jacobson's coupling is the same constant

`JacobsonClausiusEinstein.einstein_from_clausius` takes the Clausius balance on every null direction
and outputs `G_ab + Λ g_ab = 8πG · T_ab`.  Its `G` is the same Newton constant §A expresses through
the clock, so the Einstein coupling carried by the walk is `8π · 4c⁵/(ħθ²)`. -/

/-- **The Einstein coupling from the coin angle.**  `8πG` at the walk-fixed constant is
`32π c⁵/(ħθ²)` — the coefficient Jacobson's equation of state outputs, written through the walk's
single parameter. -/
theorem einsteinCoupling_from_coin_angle {θ m c ħ : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    8 * Real.pi * comptonCellG ħ c m = 32 * Real.pi * c ^ 5 / (ħ * θ ^ 2) := by
  rw [comptonCellG_eq_from_coin_angle hm hc hħ hcoin]
  field_simp
  ring

/-! ### §D — The chain -/

/-- **One dial, from the discrete walk to the field equation.**  A quantum walk whose coin angle is
matched to a Compton clock simultaneously fixes: (i) Newton's constant `G = 4c⁵/(ħθ²)`, (ii) the
inverse-square acceleration `G M/r²` at that constant, and (iii) the Einstein coupling `8πG` that
Jacobson's Clausius equation of state outputs.  Composed with `QuantumWalkFrequencyTrinity`, the same
angle also fixes the zitterbewegung, the Compton clock, the de Broglie frequency, the Yukawa mass and
its coupling. -/
theorem walk_coin_gravity_chain {θ m c ħ M r : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hcoin : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    comptonCellG ħ c m = 4 * c ^ 5 / (ħ * θ ^ 2)
      ∧ newtonAcceleration (comptonCellG ħ c m) M r = 4 * c ^ 5 * M / (ħ * θ ^ 2 * r ^ 2)
      ∧ 8 * Real.pi * comptonCellG ħ c m = 32 * Real.pi * c ^ 5 / (ħ * θ ^ 2) :=
  ⟨comptonCellG_eq_from_coin_angle hm hc hħ hcoin,
   newtonAcceleration_from_coin_angle hm hc hħ hcoin,
   einsteinCoupling_from_coin_angle hm hc hħ hcoin⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkClockGravityChain

end
