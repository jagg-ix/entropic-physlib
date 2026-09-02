/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons
meta import Zil

/-!
# The Nariai limit of the Schwarzschild–de Sitter black hole

As the mass grows the black-hole horizon rises and the cosmological horizon shrinks until they merge, at
the **Nariai limit** `9ΛM² = 1`.  The merged horizon sits at the cubic's critical point `r₀ = 1/√Λ`,
where the horizon cubic `p(r) = Λr³ − 3r + 6M` has a **double root** — both `p(r₀) = 0` and `p'(r₀) = 0`.

* `nariaiRadius` — `r₀ = 1/√Λ`; `kottlerHorizonPoly_criticalPoint` — `p'(r₀) = 3Λr₀² − 3 = 0`.
* `kottlerHorizonPoly_nariai_value` — `p(r₀) = 6M − 2r₀`.
* `nariai_double_root` — at `9ΛM² = 1` (`M > 0`) the horizons merge: `p(r₀) = 0`.

Honest scope: the double-root / critical-point algebra at the Nariai radius; the near-horizon geometry of
the Nariai spacetime is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons

/-- **The Nariai radius** `r₀ = 1/√Λ` — the critical point of the horizon cubic. -/
def nariaiRadius (Λ : ℝ) : ℝ := Real.sqrt (1 / Λ)

/-- `r₀² = 1/Λ`. -/
lemma nariaiRadius_sq {Λ : ℝ} (hΛ : 0 < Λ) : nariaiRadius Λ ^ 2 = 1 / Λ :=
  Real.sq_sqrt (by positivity)

/-- `r₀ > 0`. -/
lemma nariaiRadius_pos {Λ : ℝ} (hΛ : 0 < Λ) : 0 < nariaiRadius Λ :=
  Real.sqrt_pos.mpr (by positivity)

/-- **The horizon cubic's derivative vanishes at the Nariai radius** `p'(r₀) = 3Λr₀² − 3 = 0` — the merged
horizon is a critical point. -/
@[zil_level physical_theorem]
theorem kottlerHorizonPoly_criticalPoint (Λ : ℝ) (hΛ : 0 < Λ) :
    3 * Λ * nariaiRadius Λ ^ 2 - 3 = 0 := by
  have hΛ0 : Λ ≠ 0 := hΛ.ne'
  have hkey : Λ * nariaiRadius Λ ^ 2 = 1 := by
    rw [nariaiRadius_sq hΛ, mul_one_div, div_self hΛ0]
  rw [show 3 * Λ * nariaiRadius Λ ^ 2 = 3 * (Λ * nariaiRadius Λ ^ 2) from by ring, hkey]
  ring

/-- **The horizon cubic at the Nariai radius** `p(r₀) = 6M − 2r₀`. -/
@[zil_level physical_theorem]
theorem kottlerHorizonPoly_nariai_value (M Λ : ℝ) (hΛ : 0 < Λ) :
    kottlerHorizonPoly M Λ (nariaiRadius Λ) = 6 * M - 2 * nariaiRadius Λ := by
  have hΛ0 : Λ ≠ 0 := hΛ.ne'
  have hcube : Λ * nariaiRadius Λ ^ 3 = nariaiRadius Λ := by
    have h3 : nariaiRadius Λ ^ 3 = nariaiRadius Λ ^ 2 * nariaiRadius Λ := by ring
    rw [h3, nariaiRadius_sq hΛ]
    field_simp
  unfold kottlerHorizonPoly
  rw [hcube]; ring

/-- **The Nariai double root** — at `9ΛM² = 1` (`M > 0`) the black-hole and cosmological horizons merge
into one degenerate horizon at `r₀ = 1/√Λ`: the horizon cubic vanishes there. -/
@[zil_level physical_theorem]
theorem nariai_double_root (M Λ : ℝ) (hΛ : 0 < Λ) (hM : 0 < M) (h : 9 * Λ * M ^ 2 = 1) :
    kottlerHorizonPoly M Λ (nariaiRadius Λ) = 0 := by
  rw [kottlerHorizonPoly_nariai_value M Λ hΛ]
  have hΛ0 : Λ ≠ 0 := hΛ.ne'
  have hsq : nariaiRadius Λ ^ 2 = (3 * M) ^ 2 := by
    rw [nariaiRadius_sq hΛ]
    field_simp
    nlinarith [h]
  have hn : nariaiRadius Λ = 3 * M := by
    have hc := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (nariaiRadius_pos hΛ).le, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 3 * M)] at hc
  rw [hn]; ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai

zil attach kottlerHorizonPoly_criticalPoint where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.nariaiRadius_sq",
  formalizes @ "claim:the-schwarzschild-de-sitter-horizon-cubic-derivative-vanishes-at-the-nariai-radius-one-over-square-root-lambda-the-critical-point"

zil attach kottlerHorizonPoly_nariai_value where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterNariai.nariaiRadius_sq",
  formalizes @ "claim:the-schwarzschild-de-sitter-horizon-cubic-at-the-nariai-radius-equals-six-m-minus-twice-the-nariai-radius"

zil attach nariai_double_root where
  supported_by @ "lean:kottlerHorizonPoly_nariai_value",
  formalizes @ "claim:at-the-nariai-limit-nine-lambda-m-squared-equals-one-with-positive-mass-the-schwarzschild-de-sitter-black-hole-and-cosmological-horizons-merge-into-one-degenerate-horizon-at-one-over-square-root-lambda-the-horizon-cubic-has-a-double-root"

zil_file_contract physlib.schwarzschildDeSitterNariai where
  promises "The Nariai limit of the Schwarzschild-de Sitter black hole. As the mass grows the black-hole horizon rises and the cosmological horizon shrinks until they merge at the Nariai limit nine Lambda M squared equals one. The merged horizon sits at the horizon cubic's critical point, the Nariai radius one over the square root of Lambda, where the horizon cubic Lambda r cubed minus three r plus six M has a double root: both the cubic and its derivative vanish there. The derivative three Lambda r squared minus three vanishes at the Nariai radius, the cubic at the Nariai radius equals six M minus twice the Nariai radius, and at the Nariai limit with positive mass the horizons merge and the cubic vanishes. Honest scope: the double-root and critical-point algebra at the Nariai radius; the near-horizon geometry of the Nariai spacetime is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerHorizonPoly"
  ]
  forbids_substitutes [
    "reading the double-root algebra as a construction of the near-horizon Nariai geometry"
  ]
  witnessed_by [
    kottlerHorizonPoly_criticalPoint,
    kottlerHorizonPoly_nariai_value,
    nariai_double_root
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.schwarzschildDeSitterNariai
