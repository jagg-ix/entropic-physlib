/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ReggeWidthEntropyProduction
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The complex Regge trajectory as the geometric (string) replacement for the Yukawa coupling

In string theory mass is *not* a Higgs–Yukawa coupling: it comes from the **rotating-string spectrum**, the
Regge trajectory `α(s) = α₀ + α' s`, where `s = M²` and `α'` is the slope (`1/2π` times the inverse string
tension). A resonance of spin `J` sits at `Re α(M²) = J`, fixing `M² = (J − α₀)/α'`; the trajectory's small
imaginary part fixes the width `Γ = Im α/(α' M)` (`reggeResonanceWidth`, the entropy-production rate of
`EntropicTime.ReggeWidthEntropyProduction`).

So a **single complex trajectory** `α(s) = α_R + iα_I`, parametrized by the geometric string data
`(α₀, α', Im α)`, plays the Yukawa double role:

* **`Re α` ⟹ mass** — `reggeMassSq J α₀ α' = (J − α₀)/α'` (`reggeTrajectory_at_massSq`: `α₀ + α'·M² = J`, the
 spin–mass relation); `reggeMass = √M²`.
* **`Im α` ⟹ width = entropy production** — `reggeWidth_at_mass_eq_widthFromRate_iff`: the width at the Regge
 mass equals the Bender entropy-production width iff `Im α = 2 α' M Ṡ_I`.

There is **no Higgs VEV and no Yukawa coupling**: the scale is the string tension `1/α'`, exactly as the
gravity construction (`MassOrigin.GravitationalMassHorizonEntropyNoYukawa`) used `G` (the holographic `c³/4G`). This is
the string face of "avoid the Yukawa coupling": mass and width are two parts of one geometric trajectory.

**Scope.** Like the gravity version, this is not creation from nothing: the trajectory data `(α₀, α')`
(equivalently the string tension) is the input replacing `y_f`. The win is that the *one* geometric object
sources both the mass and the width, and the intercept gives the massless states for free
(`reggeMass_at_intercept`: `J = α₀ ⟹ M = 0`, e.g. the graviton/photon on the leading trajectory).

## References

* T. Regge (1959); the rotating-string / Veneziano Regge trajectory `J = α₀ + α' M²`. `Physlib`
 (`EntropicTime.ReggeWidthEntropyProduction`, `MassOrigin.GravitationalMassHorizonEntropyNoYukawa`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ReggeWidthEntropyProduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement

/-- **The resonance mass² from the real Regge trajectory** at spin `J`: `Re α(M²) = J ⟹ M² = (J − α₀)/α'`. -/
noncomputable def reggeMassSq (J α₀ α' : ℝ) : ℝ := (J - α₀) / α'

/-- **The resonance mass** `M = √M²` from the trajectory. -/
noncomputable def reggeMass (J α₀ α' : ℝ) : ℝ := Real.sqrt (reggeMassSq J α₀ α')

/-- **[The spin–mass relation]** `α₀ + α'·M² = J`: the resonance mass² lies on the real Regge trajectory at
spin `J` (`α' ≠ 0`). Mass from the string spectrum, not a Higgs coupling. -/
theorem reggeTrajectory_at_massSq (J α₀ α' : ℝ) (hα' : α' ≠ 0) :
    α₀ + α' * reggeMassSq J α₀ α' = J := by
  unfold reggeMassSq
  field_simp
  ring

/-- **[`M² = (J − α₀)/α'` recovered from the mass]** `(reggeMass)² = M²` (when `M² ≥ 0`). -/
theorem reggeMass_sq (J α₀ α' : ℝ) (h : 0 ≤ reggeMassSq J α₀ α') :
    reggeMass J α₀ α' ^ 2 = reggeMassSq J α₀ α' := by
  unfold reggeMass
  rw [Real.sq_sqrt h]

/-- **[The intercept is massless]** at `J = α₀` (the trajectory intercept) the mass vanishes — the leading
massless state (graviton/photon) on the trajectory, with no Higgs needed. -/
theorem reggeMass_at_intercept (α₀ α' : ℝ) :
    reggeMass α₀ α₀ α' = 0 := by
  unfold reggeMass reggeMassSq
  simp

/-- **[`M² = 0 ⟺ J = α₀`]** the mass-shell sits at the spin equal to the intercept. -/
theorem reggeMassSq_eq_zero_iff (J α₀ α' : ℝ) (hα' : α' ≠ 0) :
    reggeMassSq J α₀ α' = 0 ↔ J = α₀ := by
  unfold reggeMassSq
  rw [div_eq_zero_iff]
  simp [hα', sub_eq_zero]

/-- **[The imaginary trajectory is the entropy-production width]** at the Regge mass, the resonance width
equals the Bender entropy-production width `widthFromRate Ṡ_I` iff the trajectory's imaginary part is
`Im α = 2 α' M Ṡ_I`. So the *same* trajectory whose real part gives the mass has an imaginary part that *is*
the entropy-production rate — the Yukawa double role, geometrized. -/
theorem reggeWidth_at_mass_eq_widthFromRate_iff (J α₀ α' imAlpha dSI : ℝ)
    (hαM : α' * reggeMass J α₀ α' ≠ 0) :
    reggeResonanceWidth imAlpha α' (reggeMass J α₀ α') = widthFromRate dSI
      ↔ imAlpha = 2 * α' * reggeMass J α₀ α' * dSI :=
  reggeResonanceWidth_eq_widthFromRate_iff imAlpha dSI α' (reggeMass J α₀ α') hαM

end Physlib.QuantumMechanics.ComplexAction.Yukawa.ReggeStringMassYukawaReplacement

end
