/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChangeMorse
public import Physlib.Relativity.Special.HyperbolicBoost

/-!
# Louko–Sorkin §2.2–2.4: the Misner space of the yarmulke, and the trousers strength

The yarmulke spacetime (Louko–Sorkin §2.2) is (one causal region of) **Misner space** — the future
Minkowski wedge `T > |X|` with the `φ ~ φ + 2π` periodicity realized as a **boost identification** of
rapidity `4π/√(ζ−1)` (`misnerRapidity`, from `TwoDimensionalTopologyChangeMorse`). This module links
the topology-change strengths to that Misner structure and to the repository's hyperbolic-boost
infrastructure.

* **§A — the physical yarmulke strength** (Eqs. 2.19, 2.21). Computed with the imaginary regulator
  `γ = iσ`, the density is `½√(−g)R = 2π(2/√(ζ−1) − i)δ₂`. Its **real part is exactly the Misner
  rapidity** (`yarmulkeDeltaStrength_re_eq_misnerRapidity`), its imaginary part the regulator-fixed
  `−2π` (`yarmulkeDeltaStrength_im`), and the whole strength is the `β − 2πi` already carried by
  `yarmulkeStrength` (`yarmulkeDeltaStrength_eq_yarmulkeStrength`).
* **§B — Misner space as the boosted wedge** (Eqs. 2.13–2.14). The Morse coordinates put the metric in
  Minkowski form `−dT² + dX²` on the hyperbolae `T² − X² = ¼(ζ−1)r²` (`misnerCoords_minkowski`), and
  the `φ ~ φ + 2π` identification is a rapidity-`misnerRapidity` boost that preserves that form
  (`misnerBoost_preserves_minkowski`, reusing `HyperbolicBoost.RapidityBoost.preserves_minkowski`).
* **§C — the trousers strength** (Eq. 2.35). The crotch density is `½√(−g)R = 2πi δ₂`, **independent
  of `ζ`** (`trousersDeltaStrength_eq`, `trousers_strength_zeta_independent`) — no rapidity, pure
  `2πi`, matching `trousersStrength`.

**Honest layering.** Proven: the equality of the physical strength `2π(2/√(ζ−1) − i)` with `β − 2πi`,
its Misner-rapidity real part, the Minkowski hyperbola form, and the boost invariance. Interpretive:
the distributional computations (Eqs. 2.15–2.35) and the `φ ~ φ + 2π → boost` identification are
Louko–Sorkin's; encoded here through `misnerRapidity` and the boost, not re-derived as distributions.

## References

* J. Louko, R. D. Sorkin, "Complex actions in two-dimensional topology change", Class. Quantum Grav.
  **14**, 179 (1997) [`Louko:1995jw`], §2.2–2.4, Eqs. (2.13)–(2.35); C. W. Misner, in *Relativity
  Theory and Astrophysics I* (1967) (Misner space). Reuses `TwoDimensionalTopologyChange`
  (`yarmulkeStrength`, `trousersStrength`), `TwoDimensionalTopologyChangeMorse` (`misnerRapidity`),
  `Relativity.Special.HyperbolicBoost` (`boostX`, `boostT`, `RapidityBoost.preserves_minkowski`).


-/

set_option autoImplicit false

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChange
open Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChangeMorse
open Physlib.Relativity.Special

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChangeMisner


/-- **The Louko–Sorkin yarmulke delta strength** `2π(2/√(ζ−1) − i)` (Eqs. 2.19, 2.21, convergent
sign): the `γ → 0` limit of `½√(−g)R` with the imaginary regulator. -/
noncomputable def yarmulkeDeltaStrength (ζ : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * (2 / (Real.sqrt (ζ - 1) : ℂ) - Complex.I)

/-- **The physical strength is `β − 2πi`** with `β = misnerRapidity ζ` — the computed Louko–Sorkin
strength is exactly the `yarmulkeStrength` taken as input in `TwoDimensionalTopologyChange`. -/
lemma yarmulkeDeltaStrength_eq_yarmulkeStrength (ζ : ℝ) :
    yarmulkeDeltaStrength ζ = yarmulkeStrength (misnerRapidity ζ) := by
  unfold yarmulkeDeltaStrength yarmulkeStrength misnerRapidity
  rw [Complex.ofReal_div]; push_cast; ring

/-- **The real part of the yarmulke strength is the Misner rapidity** (Louko–Sorkin §2.2): the boost
parameter of the associated Misner space. -/
lemma yarmulkeDeltaStrength_re_eq_misnerRapidity (ζ : ℝ) :
    (yarmulkeDeltaStrength ζ).re = misnerRapidity ζ := by
  rw [yarmulkeDeltaStrength_eq_yarmulkeStrength, yarmulkeStrength_re]

/-- **The imaginary part is `−2π`, independent of the rapidity** — the regulator-fixed piece. -/
lemma yarmulkeDeltaStrength_im (ζ : ℝ) : (yarmulkeDeltaStrength ζ).im = -(2 * Real.pi) := by
  rw [yarmulkeDeltaStrength_eq_yarmulkeStrength]; exact yarmulkeStrength_im _


/-- The Misner time coordinate `T = ½√(ζ−1) r cosh(2φ/√(ζ−1))` (Louko–Sorkin Eq. 2.13). -/
noncomputable def misnerT (ζ r φ : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (ζ - 1) * r * Real.cosh (2 * φ / Real.sqrt (ζ - 1))

/-- The Misner space coordinate `X = ½√(ζ−1) r sinh(2φ/√(ζ−1))` (Eq. 2.13). -/
noncomputable def misnerX (ζ r φ : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (ζ - 1) * r * Real.sinh (2 * φ / Real.sqrt (ζ - 1))

/-- **The Misner coordinates put the metric in Minkowski form on the hyperbolae** `T² − X² =
¼(ζ−1)r²` (Eq. 2.14, `ds² = −dT² + dX²`): the constant-`r` orbits of the Misner boost. -/
lemma misnerCoords_minkowski (ζ r φ : ℝ) (hζ : 1 ≤ ζ) :
    (misnerT ζ r φ) ^ 2 - (misnerX ζ r φ) ^ 2 = (1 / 4) * (ζ - 1) * r ^ 2 := by
  unfold misnerT misnerX
  have hc := Real.cosh_sq_sub_sinh_sq (2 * φ / Real.sqrt (ζ - 1))
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ ζ - 1 by linarith)
  have expand :
      (1 / 2 * Real.sqrt (ζ - 1) * r * Real.cosh (2 * φ / Real.sqrt (ζ - 1))) ^ 2
        - (1 / 2 * Real.sqrt (ζ - 1) * r * Real.sinh (2 * φ / Real.sqrt (ζ - 1))) ^ 2
      = (1 / 4) * Real.sqrt (ζ - 1) ^ 2 * r ^ 2
        * (Real.cosh (2 * φ / Real.sqrt (ζ - 1)) ^ 2
           - Real.sinh (2 * φ / Real.sqrt (ζ - 1)) ^ 2) := by ring
  rw [expand, hc, hs]; ring

/-- **The Misner identification is a boost preserving the Minkowski form**: the `φ ~ φ + 2π`
periodicity is realized by a boost of rapidity `misnerRapidity ζ`, which preserves `X² − T²` (reusing
`HyperbolicBoost.RapidityBoost.preserves_minkowski`). -/
lemma misnerBoost_preserves_minkowski (ζ x t : ℝ) :
    (boostX (misnerRapidity ζ) x t) ^ 2 - (boostT (misnerRapidity ζ) x t) ^ 2 = x ^ 2 - t ^ 2 :=
  RapidityBoost.preserves_minkowski (B := { η := misnerRapidity ζ }) x t


/-- **The Louko–Sorkin trousers (crotch) delta strength** `2πi` (Eq. 2.35), the `γ → 0` limit of
`½√(−g)R` for the Lorentzian crotch. -/
noncomputable def trousersDeltaStrength : ℂ := trousersStrength

/-- The trousers strength is the pure `2πi` of `trousersStrength` — no rapidity, no `ζ`. -/
lemma trousersDeltaStrength_eq : trousersDeltaStrength = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := rfl

/-- **The trousers strength is independent of the parameter `ζ`** (Louko–Sorkin §2.4): unlike the
yarmulke, the crotch has no rapidity — its imaginary strength `2π` is the same for every `ζ`. -/
lemma trousers_strength_zeta_independent : trousersDeltaStrength.im = 2 * Real.pi := by
  rw [trousersDeltaStrength]; exact trousersStrength_im

end Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChangeMisner
