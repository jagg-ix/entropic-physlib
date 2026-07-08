/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Hyperbolic geometry foundations: unit hyperbola, rapidity boost, GR escape orbit

Scalar hyperbolic-geometry content shared between SR (the unit hyperbola
`x² − t² = 1` and rapidity-form Lorentz boost) and GR (the hyperbolic escape
orbit `r(θ) = a(e²−1)/(1+e cos θ)`).  This module provides the scalar structures
and connects the **rapidity-form boost** to physlib's existing
**velocity-form** `γ(β) = 1/√(1−β²)` via the standard identification
`β = tanh η`, `γ = cosh η`.

## Contents

* `UnitHyperbola x t` — Prop-level membership of `(x, t)` in the unit
  hyperbola `x² − t² = 1`.
* `unitHyperbola_cosh_sinh` — `(cosh η, sinh η)` lies on the unit hyperbola.
* `RapidityBoost` — scalar `(1+1)`-D Lorentz boost in rapidity form, with
  `boostX η x t = x cosh η − t sinh η`,
  `boostT η x t = −x sinh η + t cosh η`,
  and the proven Minkowski-form invariance
  `(boostX)² − (boostT)² = x² − t²`.
* `γ_tanh_eq_cosh` — rapidity ↔ velocity bridge:
  `LorentzGroup.γ (tanh η) = cosh η`.  Bridges the rapidity-form scalar
  boost into physlib's existing `LorentzGroup.γ` velocity parameterisation.
* `abs_tanh_lt_one` — `|tanh η| < 1` (rapidity rapidities map into the
  open velocity range `(−1, 1)` required by physlib's `γ`).
* `HyperbolicOrbit` — GR hyperbolic-escape-orbit structure `(a, e)` with
  `e > 1` and the orbit formula `r(θ) = a(e² − 1)/(1 + e cos θ)`.


## References

- **Grosche 1993** — *Path integrals, hyperbolic spaces, Selberg trace formulae*
- **Rindler 1966** — *Hyperbolic motion in curved space-time*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special

open Real

/-! ## §1 — Unit hyperbola -/

/-- **Unit hyperbola** in `ℝ²`: `x² − t² = 1`.  Foundational for SR
proper-time intervals and the rapidity parameterisation of Lorentz
boosts. -/
def UnitHyperbola (x t : ℝ) : Prop := x ^ 2 - t ^ 2 = 1

/-- **`(cosh η, sinh η)` on the unit hyperbola**: the hyperbolic identity
`cosh²η − sinh²η = 1` places the rapidity-parameterised point on the unit
hyperbola. -/
theorem unitHyperbola_cosh_sinh (η : ℝ) :
    UnitHyperbola (Real.cosh η) (Real.sinh η) := by
  unfold UnitHyperbola
  exact Real.cosh_sq_sub_sinh_sq η

/-! ## §2 — Rapidity-form Lorentz boost -/

/-- **Scalar `(1+1)`-D Lorentz boost in rapidity form.**  structure holding
the rapidity `η`; the boost map is exposed via the standalone functions
`boostX η x t = x cosh η − t sinh η`,
`boostT η x t = −x sinh η + t cosh η`. -/
structure RapidityBoost where
  /-- Rapidity. -/
  η : ℝ

/-- The boosted spatial coordinate in rapidity form. -/
def boostX (η x t : ℝ) : ℝ := x * Real.cosh η - t * Real.sinh η

/-- The boosted temporal coordinate in rapidity form. -/
def boostT (η x t : ℝ) : ℝ := -x * Real.sinh η + t * Real.cosh η

namespace RapidityBoost

variable (B : RapidityBoost)

/-- **Rapidity-form boost preserves the Minkowski form**:
`(boostX η x t)² − (boostT η x t)² = x² − t²`. -/
theorem preserves_minkowski (x t : ℝ) :
    (boostX B.η x t) ^ 2 - (boostT B.η x t) ^ 2 = x ^ 2 - t ^ 2 := by
  unfold boostX boostT
  nlinarith [Real.cosh_sq_sub_sinh_sq B.η, sq_nonneg x, sq_nonneg t]

/-- Trivial existence: zero rapidity (identity boost). -/
theorem exists_trivial : ∃ _ : RapidityBoost, True :=
  ⟨{ η := 0 }, trivial⟩

end RapidityBoost

/-! ## §3 — Rapidity ↔ velocity bridge -/

/-- **`|tanh η| < 1`**: the rapidity-form velocity sits in the open
range required by physlib's velocity-form `LorentzGroup.γ`. -/
theorem abs_tanh_lt_one (η : ℝ) : |Real.tanh η| < 1 := by
  have h1 : Real.tanh η < 1 := Real.tanh_lt_one η
  have h2 : -1 < Real.tanh η := Real.neg_one_lt_tanh η
  exact abs_lt.mpr ⟨h2, h1⟩

/-- **Rapidity ↔ velocity bridge** for the Lorentz factor:
`γ(tanh η) = cosh η`.  Identifies the rapidity-form parameterisation
with physlib's existing velocity-form `LorentzGroup.γ`. -/
theorem γ_tanh_eq_cosh (η : ℝ) :
    LorentzGroup.γ (Real.tanh η) = Real.cosh η := by
  unfold LorentzGroup.γ
  have hcosh_pos : 0 < Real.cosh η := Real.cosh_pos η
  have hcosh_ne : Real.cosh η ≠ 0 := ne_of_gt hcosh_pos
  -- 1 − tanh²η = 1/cosh²η, from the hyperbolic identity cosh² − sinh² = 1.
  have h1 : 1 - Real.tanh η ^ 2 = 1 / Real.cosh η ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    linarith [Real.cosh_sq_sub_sinh_sq η]
  -- √(1 − tanh²η) = 1/cosh η.
  have h2 : Real.sqrt (1 - Real.tanh η ^ 2) = 1 / Real.cosh η := by
    rw [h1]
    rw [show (1 : ℝ) / Real.cosh η ^ 2 = (1 / Real.cosh η) ^ 2 from by
      field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [h2]
  field_simp

/-- **Rapidity-velocity correspondence**: at `β = tanh η, γ = cosh η`,
the rapidity-form boost coincides with the standard velocity-form
parameterisation. -/
theorem rapidity_to_velocity_correspondence (η : ℝ) :
    LorentzGroup.γ (Real.tanh η) = Real.cosh η :=
  γ_tanh_eq_cosh η

/-! ## §4 — Hyperbolic GR escape orbit -/

/-- **Hyperbolic GR escape orbit structure.**  Holds the scale parameter
`a > 0`, the eccentricity `e > 1` (hyperbolic / open regime), and the
orbit radius `r(θ) = a(e² − 1)/(1 + e cos θ)`.

In an entropic statistical reading the eccentricity acts as a
correlation-length parameter: `e > 1` is the open / decoherent regime
where causal correlations escape mutual-information bounds. -/
structure HyperbolicOrbit where
  /-- Scale parameter. -/
  a : ℝ
  /-- Eccentricity, `> 1` for hyperbolic escape. -/
  e : ℝ
  /-- `a` strictly positive. -/
  a_pos : 0 < a
  /-- Hyperbolic regime. -/
  e_gt_one : 1 < e

namespace HyperbolicOrbit

variable (O : HyperbolicOrbit)

/-- Orbit radius as a function of the polar angle `θ`:
`r(θ) = a(e² − 1)/(1 + e cos θ)`. -/
def r (θ : ℝ) : ℝ := O.a * (O.e ^ 2 - 1) / (1 + O.e * Real.cos θ)

/-- The eccentricity is positive (since `e > 1 > 0`). -/
theorem e_pos : 0 < O.e := lt_trans zero_lt_one O.e_gt_one

/-- `e² − 1 > 0` (hyperbolic regime). -/
theorem e_sq_minus_one_pos : 0 < O.e ^ 2 - 1 := by
  have h := O.e_gt_one
  nlinarith

/-- **Eccentricity decoherence interpretation.**  `e > 1` corresponds to
the open / decoherent regime in the entropic statistical framework
(causal correlations escaping mutual-information bounds). -/
theorem eccentricity_decoherent : 1 < O.e := O.e_gt_one

/-- Trivial existence: `a = 1, e = 2` (hyperbolic). -/
theorem exists_trivial : ∃ _ : HyperbolicOrbit, True :=
  ⟨{ a := 1, e := 2, a_pos := by norm_num, e_gt_one := by norm_num }, trivial⟩

end HyperbolicOrbit

end Physlib.Relativity.Special

end
