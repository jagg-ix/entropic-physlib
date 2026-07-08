/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Physlib.Thermodynamics.SecondLaw

/-!
# Twin-paradox extremals and acceleration-bounded minima

Appendix-A quantitative content of the twin paradox in special relativity:

* **(a) Maximal proper time is inertial.**  Jensen's inequality on the
  concave function `f(u) = √(1 − u²)` gives `Δτ ≤ T`, with equality only at
  `v ≡ 0`.  The symmetric round-trip case is in
  `Physlib.Relativity.Special.TwinParadox.Basic`
  (`travelingProperTime_le_earthCoordinateTime`).
* **(b) Arbitrarily small proper time** with unconstrained acceleration:
  `Δτ ≈ T/γ → 0` as `v → c`.
* **(c) Minimal proper time with comfort bound `|α| ≤ g`** — the bang-bang
  trajectory in `1+1`-D yields
  `Δτ_min(T; g) = (4 c / g) · arsinh(g T / (4 c))`.

## Main results

* `twinTauMin T g c` — Appendix-A eq. (39): comfort-bounded minimum.
* `twinTauMin_zero` — `Δτ_min(0; g) = 0`.
* `twinTauMin_pos` — strict positivity for positive `T, g, c`.
* `twinTauMin_le_T` — the bang-bang minimum is at most coordinate time.
* `arsinh_le_self_of_nonneg` — the underlying Mathlib helper.
* `AccelerationBoundedTwinParadox` — composite structure holding the
  parameters `(T, g, c)` and the proven `≤ T` bound exposed as a method.
* `GeometricEntropicTimeDistinction` — structure-level statement of the
  paper's "accelerated motion that minimises `τ_geo` need not maximise
  `τ_ent`": geometric and entropic proper time are independent clock
  variables in general.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.TwinParadox

open Real

/-! ## §1 — Mathlib helper: `arsinh u ≤ u` for `u ≥ 0` -/

/-- **`arsinh u ≤ u` for `u ≥ 0`.**  Proof:
`arsinh u ≤ u ↔ sinh (arsinh u) ≤ sinh u ↔ u ≤ sinh u ↔ 0 ≤ u`. -/
theorem arsinh_le_self_of_nonneg (u : ℝ) (hu : 0 ≤ u) :
    Real.arsinh u ≤ u := by
  rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
  exact Real.self_le_sinh_iff.mpr hu

/-! ## §2 — Comfort-bounded minimum proper time -/

/-- **Comfort-bounded minimum proper time** (Appendix A, eq. 39).
A bang-bang proper-acceleration trajectory in `1+1`-D with `|α| ≤ g`
yields the minimum traveling-twin proper time
`Δτ_min(T; g) = (4 c / g) · arsinh(g T / (4 c))`. -/
def twinTauMin (T g c : ℝ) : ℝ :=
  (4 * c / g) * Real.arsinh (g * T / (4 * c))

/-- **At zero coordinate time**: `Δτ_min(0; g) = 0`. -/
theorem twinTauMin_zero (g c : ℝ) : twinTauMin 0 g c = 0 := by
  unfold twinTauMin
  simp [Real.arsinh_zero]

/-- **Strict positivity** when all three parameters are positive. -/
theorem twinTauMin_pos
    (T g c : ℝ) (hT : 0 < T) (hg : 0 < g) (hc : 0 < c) :
    0 < twinTauMin T g c := by
  unfold twinTauMin
  have h1 : 0 < 4 * c / g := div_pos (by linarith) hg
  have h2 : 0 < g * T / (4 * c) := div_pos (mul_pos hg hT) (by linarith)
  have h3 : 0 < Real.arsinh (g * T / (4 * c)) := Real.arsinh_pos_iff.mpr h2
  exact mul_pos h1 h3

/-- **Non-negativity** under `T ≥ 0, g > 0, c > 0`. -/
theorem twinTauMin_nonneg
    (T g c : ℝ) (hT : 0 ≤ T) (hg : 0 < g) (hc : 0 < c) :
    0 ≤ twinTauMin T g c := by
  unfold twinTauMin
  have h1 : 0 ≤ 4 * c / g := div_nonneg (by linarith) hg.le
  have h2 : 0 ≤ g * T / (4 * c) := div_nonneg (mul_nonneg hg.le hT) (by linarith)
  have h3 : 0 ≤ Real.arsinh (g * T / (4 * c)) := Real.arsinh_nonneg_iff.mpr h2
  exact mul_nonneg h1 h3

/-- **Bang-bang minimum is at most coordinate time**: `Δτ_min(T; g) ≤ T`.

Mechanism: substitute `u = g T / (4 c)`, then
`(4 c / g) · arsinh(u) ≤ (4 c / g) · u = T`, using
`arsinh_le_self_of_nonneg` for `u ≥ 0`. -/
theorem twinTauMin_le_T
    (T g c : ℝ) (hT : 0 ≤ T) (hg : 0 < g) (hc : 0 < c) :
    twinTauMin T g c ≤ T := by
  unfold twinTauMin
  have hcoeff_nn : 0 ≤ 4 * c / g := div_nonneg (by linarith) hg.le
  have hu_nn : 0 ≤ g * T / (4 * c) := div_nonneg (mul_nonneg hg.le hT) (by linarith)
  have harsinh_le : Real.arsinh (g * T / (4 * c)) ≤ g * T / (4 * c) :=
    arsinh_le_self_of_nonneg _ hu_nn
  calc (4 * c / g) * Real.arsinh (g * T / (4 * c))
      ≤ (4 * c / g) * (g * T / (4 * c)) :=
          mul_le_mul_of_nonneg_left harsinh_le hcoeff_nn
    _ = T := by
        have hg_ne : g ≠ 0 := ne_of_gt hg
        have hc_ne : c ≠ 0 := ne_of_gt hc
        field_simp

/-! ## §3 — Acceleration-bounded composite structure -/

/-- **Composite structure** for the acceleration-bounded twin-paradox
configuration: inertial twin's coordinate time `T`, comfort-acceleration
bound `g`, speed of light `c`, all strictly positive. -/
structure AccelerationBoundedTwinParadox where
  /-- Inertial twin's coordinate time. -/
  T : ℝ
  /-- Comfort-acceleration bound `|α| ≤ g`. -/
  g : ℝ
  /-- Speed of light. -/
  c : ℝ
  T_pos : 0 < T
  g_pos : 0 < g
  c_pos : 0 < c

namespace AccelerationBoundedTwinParadox

variable (P : AccelerationBoundedTwinParadox)

/-- **Extraction**: the bang-bang minimum proper time for this configuration. -/
def tauMin : ℝ := twinTauMin P.T P.g P.c

/-- The bang-bang minimum is strictly positive. -/
theorem tauMin_pos : 0 < P.tauMin :=
  twinTauMin_pos P.T P.g P.c P.T_pos P.g_pos P.c_pos

/-- The bang-bang minimum is at most the inertial twin's coordinate time. -/
theorem tauMin_le_T : P.tauMin ≤ P.T :=
  twinTauMin_le_T P.T P.g P.c P.T_pos.le P.g_pos P.c_pos

end AccelerationBoundedTwinParadox

/-! ## §4 — Geometric vs entropic proper-time distinction -/

/-- **structure-level statement** of the paper's observation that geometric
and entropic proper times are *independent* clock variables.

Appendix B states:

> "Geometric proper time is extremised purely kinematically, while
>  entropic proper time `τ_ent` depends on local openness and detector
>  thermalisation.  Thus, accelerated motion that minimises `τ_geo` need
>  not maximise `τ_ent`."

This structure records the default *separation*: there exists at least one
parameter where the two clocks differ.  Consumers that need the
identification (e.g. closed isolated systems) supply
`IdentifySRProperTimeWithEntropicProperTime`. -/
structure GeometricEntropicTimeDistinction where
  /-- Geometric proper-time clock. -/
  tauGeo : ℝ → ℝ
  /-- Entropic proper-time clock (`τ_ent = S_I / ℏ`). -/
  tauEnt : ℝ → ℝ
  /-- Default separation: the two clocks differ somewhere. -/
  default_separation : ∃ s : ℝ, tauGeo s ≠ tauEnt s

namespace GeometricEntropicTimeDistinction

variable (D : GeometricEntropicTimeDistinction)

/-- Extraction: the witness parameter and the inequality. -/
theorem tauGeo_ne_tauEnt :
    ∃ s : ℝ, D.tauGeo s ≠ D.tauEnt s := D.default_separation

end GeometricEntropicTimeDistinction

/-- **Trivial existence** of the geometric-entropic distinction: take
`τ_geo ≡ 0` and `τ_ent = id`; they differ at any non-zero parameter. -/
theorem GeometricEntropicTimeDistinction.exists_trivial :
    ∃ _ : GeometricEntropicTimeDistinction, True :=
  ⟨{ tauGeo := fun _ => 0
   , tauEnt := fun s => s
   , default_separation := ⟨1, by norm_num⟩ }, trivial⟩

/-- **Trivial existence** of an acceleration-bounded structure (`T = g = c = 1`). -/
theorem AccelerationBoundedTwinParadox.exists_trivial :
    ∃ _ : AccelerationBoundedTwinParadox, True :=
  ⟨{ T := 1, g := 1, c := 1
   , T_pos := one_pos, g_pos := one_pos, c_pos := one_pos }, trivial⟩

/-! ## §4 — Strengthening `GeometricEntropicTimeDistinction.tauEnt`
    to come from an `EntropyArrowWorldline`

The current `tauEnt : ℝ → ℝ` field of `GeometricEntropicTimeDistinction`
is a *bare function*: no second-law constraint, no monotonicity, no
relationship to `S_I`.  This section provides the strengthened form
where `tauEnt` is exactly `EntropyArrowWorldline.τ_ent_along`, so the
entropic-clock side automatically inherits the second-law monotonicity
from `SecondLaw.lean`.
-/

open Physlib.Thermodynamics.SecondLaw

/-- **Strengthened distinction**: the entropic-clock side is supplied by
an `EntropyArrowWorldline`, so `tauEnt` includes the second-law
monotonicity (`tau_ent_monotone`) automatically.

The default-separation field still asserts that geometric and entropic
clocks differ at *some* parameter; consumers that want pointwise
identification use the `BridgeSRandEntropic` pattern from
`TwinParadox/Entropic.lean`. -/
structure GeometricEntropicTimeDistinctionFromWorldline where
  /-- The entropic worldline supplying `τ_ent`. -/
  worldline : EntropyArrowWorldline
  /-- Geometric proper-time clock (bare function — no second-law
  constraint). -/
  tauGeo : ℝ → ℝ
  /-- Default separation: the two clocks differ somewhere. -/
  default_separation :
    ∃ s : ℝ, tauGeo s ≠ worldline.τ_ent_along s

namespace GeometricEntropicTimeDistinctionFromWorldline

variable (D : GeometricEntropicTimeDistinctionFromWorldline)

/-- The entropic-clock readout is the worldline's `τ_ent`. -/
def tauEnt : ℝ → ℝ := D.worldline.τ_ent_along

/-- **Projection to the bare `GeometricEntropicTimeDistinction`.**
Strips the second-law structure to recover the weaker structure. -/
def toGeometricEntropicTimeDistinction : GeometricEntropicTimeDistinction where
  tauGeo := D.tauGeo
  tauEnt := D.tauEnt
  default_separation := D.default_separation

/-- **The entropic clock is monotone non-decreasing** — automatic
inheritance from the second-law `S_I_monotone` field on the worldline.
This was *not* provable in the bare `GeometricEntropicTimeDistinction`;
here it comes for free. -/
theorem tauEnt_monotone : Monotone D.tauEnt :=
  fun _ _ h => D.worldline.tau_ent_monotone h

/-- **The entropic clock is non-negative along forward parameters** —
inherited from `tau_ent_nonneg_along_worldline`. -/
theorem tauEnt_nonneg_along (t : ℝ) (h : 0 ≤ t) :
    0 ≤ D.tauEnt t :=
  D.worldline.tau_ent_nonneg_along_worldline h

/-- Extraction: the witness parameter and the inequality. -/
theorem tauGeo_ne_tauEnt :
    ∃ s : ℝ, D.tauGeo s ≠ D.tauEnt s := D.default_separation

end GeometricEntropicTimeDistinctionFromWorldline

/-- **Trivial existence** of the strengthened distinction.  Construct a
worldline with `S_I_along ≡ id` (linear entropy production) and
`τ_geo ≡ 0`; they differ at any non-zero parameter. -/
theorem GeometricEntropicTimeDistinctionFromWorldline.exists_trivial :
    ∃ _ : GeometricEntropicTimeDistinctionFromWorldline, True := by
  refine ⟨{
    worldline := {
      ℏ := 1
      ℏ_pos := one_pos
      S_I_along := id
      τ_ent_along := id
      τ_ent_eq := by intro t; simp
      S_I_monotone := by intro _ _ h; exact h
      S_I_at_zero_nonneg := le_refl 0
    }
    tauGeo := fun _ => 0
    default_separation := ⟨1, by simp⟩ }, trivial⟩

end Physlib.Relativity.Special.TwinParadox

end
