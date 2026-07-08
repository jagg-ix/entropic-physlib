/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dimensional scaling: the dimension → length → volume functor tower

A self-contained dimensional-bookkeeping kernel: to each dimension `D` one attaches a scaling factor
`λ_D = √D`, a characteristic length `L_D = a·λ_D` at scale `a`, and a volume `V_D = (L_D)^D`, tied
together by the length → volume map `η_D(L) = L^D`. Organised as a functor tower:

 * `F_L : Dim → Length`, `D ↦ L_D = a√D` (`lengthFunctor`);
 * `η_D : Length → Volume`, `L ↦ L^D` (`volumeMap`, the length → volume component);
 * `F_V ∘ F_L : Dim → Volume`, `D ↦ V_D` (`volumeComposite`),

with the coherence `V_D = η_D(L_D)` (`volumeComposite_eq_dimVolume`) and the closed form
`V_D = a^D · D^{D/2}` (`dimVolume_eq_rpow`).

* **§A — the scaling factor `λ_D = √D`.** `scalingFactor`, with `λ_D² = D` (`scalingFactor_sq`),
 `λ_1 = 1` (`scalingFactor_one`), and monotonicity in the dimension (`scalingFactor_mono`).
* **§B — length `L_D`, volume `V_D`, and the closed forms.** `dimLength`, `dimVolume`;
 `dimVolume_eq_length_pow` (`V_D = (L_D)^D`, the naturality of `η`) and `dimVolume_eq_rpow`
 (`V_D = a^D · D^{D/2}`). The cross-dimensional transformation rule
 `L_{D+1} = L_D·√((D+1)/D)` (`dimLength_succ`) is the *consistent* step of the tower.
* **§C — the functor tower.** `lengthFunctor`, `volumeMap`, `volumeComposite`, and the coherence
 `volumeComposite_eq_dimVolume`.
* **§D — the cross-dimensional ratio.** `scalingFactor_ratio` and `dimLength_ratio`: the ratio between
 dimensions `R_{M→N} = L_N/L_M = √(N/M)` (the exponent-`1` case of `R = (λ_N/λ_M)^k`).
* **§E — cross-dimensional functoriality.** `scalingTransition D D' L = L·√(D'/D)` with the identity
 `scalingTransition D D = id` (`scalingTransition_id`) and the composition law
 `T_{D'→D''} ∘ T_{D→D'} = T_{D→D''}` (`scalingTransition_comp`) — the cocycle making the transitions a
 functor; `scalingTransition_dimLength` confirms `T_{D→D'}(L_D) = L_{D'}`.

Proven: all of the algebraic scaling identities, the monotonicity, the
transformation-rule step, and the tower coherence. Interpretive: the "functor / natural
transformation" language names the bookkeeping — the objects are the scaling values and the arrows are
the maps between the `Dim`, `Length`, `Volume` levels. Note that the transformation rule consistent
with `L_D = a√D` is `L_{D+1} = L_D·√((D+1)/D)`, not the exponent form sometimes quoted in the source
notes (which does not close against the `√D` law).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Mathematics.DimensionalScaling

/-! ## §A — the dimensional scaling factor `λ_D = √D` -/

/-- **The dimensional scaling factor** `λ_D = √D`: the object map of the scaling level. -/
noncomputable def scalingFactor (D : ℕ) : ℝ := Real.sqrt D

/-- **`λ_D² = D`**: the defining property of the scaling factor. -/
theorem scalingFactor_sq (D : ℕ) : scalingFactor D ^ 2 = (D : ℝ) := by
  unfold scalingFactor
  exact Real.sq_sqrt (by positivity)

/-- **`λ_1 = 1`**: the one-dimensional scaling factor is the unit. -/
theorem scalingFactor_one : scalingFactor 1 = 1 := by
  unfold scalingFactor
  simp

/-- **`0 ≤ λ_D`**. -/
theorem scalingFactor_nonneg (D : ℕ) : 0 ≤ scalingFactor D := Real.sqrt_nonneg _

/-- **`0 < λ_D` for `D ≥ 1`**: positive scaling factor above dimension zero. -/
theorem scalingFactor_pos {D : ℕ} (hD : 1 ≤ D) : 0 < scalingFactor D := by
  unfold scalingFactor
  apply Real.sqrt_pos.mpr
  exact_mod_cast hD

/-- **`λ` is monotone in the dimension** `D ≤ D' → λ_D ≤ λ_{D'}`: more dimensions, larger scaling. -/
theorem scalingFactor_mono {D D' : ℕ} (h : D ≤ D') : scalingFactor D ≤ scalingFactor D' := by
  unfold scalingFactor
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)

/-! ## §B — length `L_D`, volume `V_D`, and the closed forms -/

/-- **The dimensional length** `L_D = a·λ_D = a√D`: the object map `F_L : Dim → Length` at scale `a`. -/
noncomputable def dimLength (a : ℝ) (D : ℕ) : ℝ := a * scalingFactor D

/-- **The dimensional volume** `V_D = a^D · (√D)^D` (`= a^D · D^{D/2}`): the object at the volume
level, in closed form. -/
noncomputable def dimVolume (a : ℝ) (D : ℕ) : ℝ := a ^ D * scalingFactor D ^ D

/-- **`L_1 = a`**: in one dimension the length is the scale itself. -/
theorem dimLength_one (a : ℝ) : dimLength a 1 = a := by
  unfold dimLength
  rw [scalingFactor_one]; ring

/-- **`V_D = (L_D)^D`**: the volume is the length raised to the dimension — the naturality of the
length → volume map `η_D`. This is what makes the tower `Dim → Length → Volume` coherent. -/
theorem dimVolume_eq_length_pow (a : ℝ) (D : ℕ) : dimVolume a D = dimLength a D ^ D := by
  unfold dimVolume dimLength
  rw [mul_pow]

/-- **`(√D)^D = D^{D/2}`**: the scaling factor's `D`-th power in `rpow` closed form. -/
theorem scalingFactor_pow_eq_rpow (D : ℕ) :
    scalingFactor D ^ D = (D : ℝ) ^ ((D : ℝ) / 2) := by
  have h0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  rw [scalingFactor, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((D : ℝ) ^ (1 / (2 : ℝ))) D,
    ← Real.rpow_mul h0]
  rw [show (1 / (2 : ℝ)) * (D : ℝ) = (D : ℝ) / 2 from by ring]

/-- **The closed form `V_D = a^D · D^{D/2}`**: the dimensional volume in standard closed form. -/
theorem dimVolume_eq_rpow (a : ℝ) (D : ℕ) :
    dimVolume a D = a ^ D * (D : ℝ) ^ ((D : ℝ) / 2) := by
  unfold dimVolume
  rw [scalingFactor_pow_eq_rpow]

/-- **The cross-dimensional transformation rule** `L_{D+1} = L_D · √((D+1)/D)` (for `D ≥ 1`): the step
of the tower lifting a length from dimension `D` to `D+1`, consistent with `L_D = a√D`. -/
theorem dimLength_succ (a : ℝ) {D : ℕ} (hD : 1 ≤ D) :
    dimLength a (D + 1) = dimLength a D * Real.sqrt (((D : ℝ) + 1) / (D : ℝ)) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  unfold dimLength scalingFactor
  rw [mul_assoc, ← Real.sqrt_mul (le_of_lt hDpos)]
  rw [show (D : ℝ) * (((D : ℝ) + 1) / (D : ℝ)) = ((D : ℝ) + 1) from by field_simp]
  push_cast
  ring_nf

/-- **`0 < V_D` for `a > 0`, `D ≥ 1`**: positive dimensional volume. -/
theorem dimVolume_pos (a : ℝ) {D : ℕ} (ha : 0 < a) (hD : 1 ≤ D) : 0 < dimVolume a D := by
  unfold dimVolume
  exact mul_pos (pow_pos ha D) (pow_pos (scalingFactor_pos hD) D)

/-! ## §C — the functor tower -/

/-- **`F_L : Dim → Length`** at scale `a` — the length functor's object map, `D ↦ L_D`. -/
noncomputable def lengthFunctor (a : ℝ) (D : ℕ) : ℝ := dimLength a D

/-- **`η_D : Length → Volume`**, `L ↦ L^D` — the natural transformation component that raises a length
to its dimension power. -/
def volumeMap (D : ℕ) (L : ℝ) : ℝ := L ^ D

/-- **`F_V ∘ F_L : Dim → Volume`**, `D ↦ η_D(L_D)` — the composite of the tower. -/
noncomputable def volumeComposite (a : ℝ) (D : ℕ) : ℝ := volumeMap D (lengthFunctor a D)

/-- **Tower coherence** `(F_V ∘ F_L)(D) = V_D`: composing the length functor with the length → volume
map reproduces the closed-form dimensional volume. -/
theorem volumeComposite_eq_dimVolume (a : ℝ) (D : ℕ) :
    volumeComposite a D = dimVolume a D := by
  unfold volumeComposite volumeMap lengthFunctor
  rw [dimVolume_eq_length_pow]

/-! ## §D — the cross-dimensional scaling ratio `R_{M→N}` -/

/-- **The scaling-factor ratio** `λ_N / λ_M = √(N/M)`: the cross-dimensional ratio `R_{M→N}` at the
scaling-factor level. -/
theorem scalingFactor_ratio (M N : ℕ) :
    scalingFactor N / scalingFactor M = Real.sqrt ((N : ℝ) / (M : ℝ)) := by
  unfold scalingFactor
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (N : ℝ))]

/-- **The length ratio equals the scaling ratio** `L_N / L_M = √(N/M)` (for `a ≠ 0`): the
characteristic length transforms across dimensions by `R_{M→N} = √(N/M)` — the exponent-`1` case of the
general cross-dimensional ratio `R = (λ_N/λ_M)^k`. -/
theorem dimLength_ratio (a : ℝ) (M N : ℕ) (ha : a ≠ 0) :
    dimLength a N / dimLength a M = Real.sqrt ((N : ℝ) / (M : ℝ)) := by
  unfold dimLength
  rw [mul_div_mul_left _ _ ha, scalingFactor_ratio]

/-! ## §E — cross-dimensional functoriality (the composition law) -/

/-- **The length transition** `D → D'`, `L ↦ L·√(D'/D)`: the map that sends a characteristic length
from dimension `D` to dimension `D'` (so `dimLength a D ↦ dimLength a D'`). -/
noncomputable def scalingTransition (D D' : ℕ) (L : ℝ) : ℝ := L * Real.sqrt ((D' : ℝ) / (D : ℝ))

/-- **Identity** `scalingTransition D D = id` (for `D ≥ 1`): the transition from a dimension to itself
is the identity. -/
theorem scalingTransition_id {D : ℕ} (hD : 1 ≤ D) (L : ℝ) : scalingTransition D D L = L := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  unfold scalingTransition
  rw [div_self hDpos.ne', Real.sqrt_one, mul_one]

/-- **Functorial composition** `T_{D'→D''} ∘ T_{D→D'} = T_{D→D''}` (for `D, D' ≥ 1`): scaling a length
through `D → D' → D''` equals scaling it directly `D → D''` — the cocycle/functoriality of the
cross-dimensional transition (`√(D''/D')·√(D'/D) = √(D''/D)`). -/
theorem scalingTransition_comp {D D' D'' : ℕ} (hD : 1 ≤ D) (hD' : 1 ≤ D') (L : ℝ) :
    scalingTransition D' D'' (scalingTransition D D' L) = scalingTransition D D'' L := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD'pos : (0 : ℝ) < D' := by exact_mod_cast hD'
  unfold scalingTransition
  have harg : ((D' : ℝ) / (D : ℝ)) * ((D'' : ℝ) / (D' : ℝ)) = (D'' : ℝ) / (D : ℝ) := by
    field_simp
  rw [mul_assoc, ← Real.sqrt_mul (by positivity), harg]

/-- **The transition acts as advertised** `T_{D→D'}(L_D) = L_{D'}`: the length transition really sends
the dimension-`D` length to the dimension-`D'` length (for `D ≥ 1`). -/
theorem scalingTransition_dimLength (a : ℝ) {D : ℕ} (hD : 1 ≤ D) (D' : ℕ) :
    scalingTransition D D' (dimLength a D) = dimLength a D' := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  unfold scalingTransition dimLength scalingFactor
  rw [mul_assoc, ← Real.sqrt_mul hDpos.le]
  rw [show (D : ℝ) * ((D' : ℝ) / (D : ℝ)) = (D' : ℝ) from by field_simp]

end Physlib.Mathematics.DimensionalScaling
