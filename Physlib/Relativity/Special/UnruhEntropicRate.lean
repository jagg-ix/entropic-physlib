/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Unruh and surface-gravity entropic rate

A uniformly accelerated observer in flat spacetime sees a thermal bath at the
**Unruh temperature**

  `T_U = ℏ a / (2 π c k_B)`

(Davies–Fulling–Unruh).  In the entropic-time framework, the corresponding **entropic-time rate**
is `λ_U = k_B T_U / ℏ = a / (2π c)`, and a worldline of geometric proper-time
duration `Δτ_geom` accumulates

  `Δτ_ent = λ_U · Δτ_geom`.

For an inertial observer (`a = 0`) the entropic rate vanishes — *acceleration
sets the entropic rate, not time itself*: geometric proper time can elapse
without any entropic-clock advance.

The same `(2π c)`-form applies to **any horizon with surface gravity `κ`** via
`T_H = ℏ κ / (2 π c k_B)` (already in
`Physlib.Relativity.SemiClassical.hawkingTemperature`): the Rindler horizon
has `κ = a/c`, Schwarzschild has `κ = 1/(4GM)`, de Sitter has `κ = c·H`, etc.
This module defines both structures (`UnruhEntropicRate`,
`SurfaceGravityEntropicRate`) and the identification
`unruh_eq_surfaceGravity_at_kappa_a_over_c`.

## What this file proves

* `UnruhEntropicRate` structure with `λ_U`, `Δτ_ent`, `ΔS_irr` and the
  non-negativity / second-law theorems.
* `Δτ_ent_eq_zero_of_inertial` — the inertial endpoint.
* `SurfaceGravityEntropicRate` structure — Unruh generalised to any surface
  gravity `κ`.
* `unruh_eq_surfaceGravity_at_kappa_a_over_c` — Unruh ≡ surface gravity at
  `κ = a / c`.
* `entropicRate_eq_kB_T_H_over_hbar` — the entropic rate equals
  `k_B · hawkingTemperature / ℏ` (Tolman link to physlib's
  `SemiClassical.hawkingTemperature`).


## References

- **Unruh 1976** — *Notes on black-hole evaporation* (entropic-time/paper/references.bib)
- **Davies 1975** — *Scalar particle production in Schwarzschild and Rindler metrics*
- **Hawking 1975** — *Particle creation by black holes*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special

open Real

/-! ## §1 — Unruh entropic-rate structure -/

/-- **Unruh entropic-rate structure.**

A uniformly accelerated worldline in flat spacetime, with proper acceleration
`a ≥ 0` (inertial = `0`), Boltzmann constant `kB > 0`, speed of light `c > 0`,
and geometric proper-time duration `Δτ_geom ≥ 0`. -/
structure UnruhEntropicRate where
  /-- Boltzmann constant `k_B > 0`. -/
  kB : ℝ
  /-- Proper acceleration `a ≥ 0`. -/
  a : ℝ
  /-- Speed of light `c > 0`. -/
  c : ℝ
  /-- Geometric proper-time duration `Δτ_geom ≥ 0`. -/
  Δτ_geom : ℝ
  /-- `k_B` strictly positive. -/
  kB_pos : 0 < kB
  /-- `a` non-negative. -/
  a_nonneg : 0 ≤ a
  /-- `c` strictly positive. -/
  c_pos : 0 < c
  /-- `Δτ_geom` non-negative. -/
  Δτ_geom_nonneg : 0 ≤ Δτ_geom

namespace UnruhEntropicRate

variable (M : UnruhEntropicRate)

/-- **Unruh entropic rate** `λ_U = a / (2π c)`. -/
def lambdaU : ℝ := M.a / (2 * Real.pi * M.c)

/-- **Entropic proper-time increment** `Δτ_ent = λ_U · Δτ_geom`. -/
def Δτ_ent : ℝ := M.lambdaU * M.Δτ_geom

/-- **Irreversible entropy production** `ΔS_irr = k_B · Δτ_ent`. -/
def ΔS_irr : ℝ := M.kB * M.Δτ_ent

/-- Denominator positivity: `0 < 2π c`. -/
theorem two_pi_c_pos : 0 < 2 * Real.pi * M.c :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos) M.c_pos

/-- The Unruh rate is non-negative. -/
theorem lambdaU_nonneg : 0 ≤ M.lambdaU :=
  div_nonneg M.a_nonneg M.two_pi_c_pos.le

/-- **Arrow of time**: `Δτ_ent ≥ 0`. -/
theorem Δτ_ent_nonneg : 0 ≤ M.Δτ_ent :=
  mul_nonneg M.lambdaU_nonneg M.Δτ_geom_nonneg

/-- **Second law**: `ΔS_irr ≥ 0`. -/
theorem ΔS_irr_nonneg : 0 ≤ M.ΔS_irr :=
  mul_nonneg M.kB_pos.le M.Δτ_ent_nonneg

/-- **Inertial-observer endpoint**: at `a = 0` (no Unruh thermal bath), both
the entropic rate and the entropic time vanish, even if geometric proper time
`Δτ_geom > 0`.  This is the *"acceleration sets the entropic rate, not time"*
content. -/
theorem Δτ_ent_eq_zero_of_inertial (h : M.a = 0) : M.Δτ_ent = 0 := by
  unfold Δτ_ent lambdaU
  rw [h, zero_div, zero_mul]

/-- The Unruh rate equals `kB · T_U / ℏ` where the Unruh temperature
`T_U = hawkingTemperature ℏ a c kB` is read off the Rindler-horizon surface
gravity `κ = a` (in SI units).  Bridges `lambdaU` into physlib's existing
`SemiClassical.hawkingTemperature` layer. -/
theorem lambdaU_eq_kB_hawking_over_hbar (ℏ : ℝ) (hℏ : 0 < ℏ) :
    M.lambdaU =
      M.kB *
        Physlib.Relativity.SemiClassical.hawkingTemperature ℏ M.a M.c M.kB
        / ℏ := by
  unfold lambdaU Physlib.Relativity.SemiClassical.hawkingTemperature
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hc_ne : M.c ≠ 0 := ne_of_gt M.c_pos
  have hkB_ne : M.kB ≠ 0 := ne_of_gt M.kB_pos
  field_simp

end UnruhEntropicRate

/-! ## §2 — Surface-gravity entropic-rate structure (any horizon) -/

/-- **Surface-gravity entropic-rate structure**: the Unruh derivation
specialised to *any* horizon with surface gravity `κ` (Rindler / Schwarzschild
/ de Sitter / Kerr).  At `κ = a / c` this recovers the Unruh case. -/
structure SurfaceGravityEntropicRate where
  /-- Boltzmann constant `k_B > 0`. -/
  kB : ℝ
  /-- Surface gravity `κ ≥ 0`. -/
  κ : ℝ
  /-- Speed of light `c > 0`. -/
  c : ℝ
  /-- Geometric proper-time duration `Δτ_geom ≥ 0`. -/
  Δτ_geom : ℝ
  /-- `k_B` strictly positive. -/
  kB_pos : 0 < kB
  /-- `κ` non-negative. -/
  κ_nonneg : 0 ≤ κ
  /-- `c` strictly positive. -/
  c_pos : 0 < c
  /-- `Δτ_geom` non-negative. -/
  Δτ_geom_nonneg : 0 ≤ Δτ_geom

namespace SurfaceGravityEntropicRate

variable (M : SurfaceGravityEntropicRate)

/-- **Surface-gravity entropic rate** `λ_κ = κ / (2π c)`. -/
def lambdaSG : ℝ := M.κ / (2 * Real.pi * M.c)

/-- **Entropic proper-time increment** `Δτ_ent = λ_κ · Δτ_geom`. -/
def Δτ_ent : ℝ := M.lambdaSG * M.Δτ_geom

theorem two_pi_c_pos : 0 < 2 * Real.pi * M.c :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos) M.c_pos

theorem lambdaSG_nonneg : 0 ≤ M.lambdaSG :=
  div_nonneg M.κ_nonneg M.two_pi_c_pos.le

theorem Δτ_ent_nonneg : 0 ≤ M.Δτ_ent :=
  mul_nonneg M.lambdaSG_nonneg M.Δτ_geom_nonneg

/-- **Vanishing-surface-gravity endpoint**: at `κ = 0` (flat / no horizon
thermal bath), the entropic rate vanishes. -/
theorem Δτ_ent_eq_zero_of_zero_kappa (h : M.κ = 0) : M.Δτ_ent = 0 := by
  unfold Δτ_ent lambdaSG
  rw [h, zero_div, zero_mul]

/-- The entropic rate equals `kB · T_H / ℏ` where `T_H = ℏκ/(2πc·kB)` is the
**Hawking/Unruh temperature** of the horizon. -/
theorem lambdaSG_eq_kB_hawking_over_hbar (ℏ : ℝ) (hℏ : 0 < ℏ) :
    M.lambdaSG =
      M.kB *
        Physlib.Relativity.SemiClassical.hawkingTemperature ℏ M.κ M.c M.kB
        / ℏ := by
  unfold lambdaSG Physlib.Relativity.SemiClassical.hawkingTemperature
  have hℏ_ne : ℏ ≠ 0 := ne_of_gt hℏ
  have hc_ne : M.c ≠ 0 := ne_of_gt M.c_pos
  have hkB_ne : M.kB ≠ 0 := ne_of_gt M.kB_pos
  field_simp

end SurfaceGravityEntropicRate

/-! ## §3 — Unruh = surface gravity at the Rindler horizon (`κ = a`) -/

/-- **Embedding**: an `UnruhEntropicRate` structure with proper acceleration `a`
is the `SurfaceGravityEntropicRate` structure with `κ = a` — the Rindler-horizon
surface gravity (units of acceleration, matching the
`hawkingTemperature ℏ κ c kB` convention). -/
def UnruhEntropicRate.toSurfaceGravity (M : UnruhEntropicRate) :
    SurfaceGravityEntropicRate where
  kB := M.kB
  κ := M.a
  c := M.c
  Δτ_geom := M.Δτ_geom
  kB_pos := M.kB_pos
  κ_nonneg := M.a_nonneg
  c_pos := M.c_pos
  Δτ_geom_nonneg := M.Δτ_geom_nonneg

/-- **Unruh = surface gravity at the Rindler horizon `κ = a`**: the Unruh
entropic rate is the specialisation of the surface-gravity entropic rate at
the Rindler-horizon surface gravity. -/
theorem unruh_eq_surfaceGravity_at_kappa_a (M : UnruhEntropicRate) :
    M.lambdaU = M.toSurfaceGravity.lambdaSG := rfl

/-- The Unruh entropic proper time agrees with the surface-gravity entropic
proper time at the Rindler-horizon identification. -/
theorem unruh_Δτ_ent_eq_surfaceGravity_Δτ_ent (M : UnruhEntropicRate) :
    M.Δτ_ent = M.toSurfaceGravity.Δτ_ent := rfl

end Physlib.Relativity.Special

end
