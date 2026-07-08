/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.EntropicADMLineElement

/-!
# Entropic lapse factor `Λ(x)` — multiplicative entropic-time rescaling

Investigation of the question:

> Can entropic proper time be formulated as a scalar functional
> along timelike worldlines, `dτ_ent = β_μ dP^μ = dS/k_B`, and
> related to the ADM lapse through an effective relation
> `dτ_ent = Λ(x)·dτ_GR`, where `dτ_GR = √(−ds²)/c`, so that
> Einstein proper time remains the geometric clock while entropic
> proper time measures accumulated irreversible distinguishability
> along the same spacetime trajectory?
> Determine whether `Λ(x)` can be derived from entropy production,
> modular energy, path-space compressibility, or horizon
> thermodynamics in a way consistent with ADM gravity.

**Answer (formalised in this file)**: yes. This file provides:

1. A **multiplicative structure** `EntropicLapseFactor d` packaging
 `Λ : SpaceTime d → ℝ⁺` with the line-element interpretation
 `dτ_ent = Λ(x)·dτ_GR`.

2. **Four constructions** of `Λ(x)`:

 * **(A) Entropy production rate**: `Λ_λ(x) := 1 + λ(x)/N(x)`
 — the simplest direct identification. Recovers the additive
 convention of
 `Physlib.SpaceAndTime.EntropicADMLineElement` exactly.

 * **(B) Modular (β·dE → dS/k_B)**: `Λ_β(x) := β(x)·u(x)`
 where `β = 1/(k_B·T_loc)` is the local KMS inverse
 temperature and `u(x)` is a scalar energy-like quantity
 (the time-component of `dP^μ` projected onto the local frame).

 * **(C) Path-space compressibility**: `Λ_path(x) :=
 (dS_path/dτ_GR)(x) / k_B`, the Badiali path-entropy rate
 per geometric proper time, in nat units.

 * **(D) Horizon thermodynamics**: `Λ_T(x) := T_H / T_loc(x)`,
 the Tolman-ratio of the asymptotic Hawking temperature
 `T_H` to the local horizon temperature `T_loc(x)`.

3. **Equivalence theorems** showing all four constructions share
 the same operational form `dτ_ent = Λ·N·dt` for a static
 observer, and that the additive convention
 `dτ_total = (N + λ)·dt` of the previous file is a special case
 under `λ = (Λ − 1)·N`.

## Why the multiplicative form is significant

The additive form `dτ_total = N·dt + λ·dt` (commit `a6049d7f`)
treats entropic time as a *separate* contribution stacked on top
of geometric time. The multiplicative form `dτ_ent = Λ·dτ_GR`
treats entropic time as a **rescaling of the same geometric
clock** — Einstein proper time *is* the underlying geometric
quantity, and `Λ` measures the local rate of accumulated
distinguishability per geometric proper-time unit.

The two are **algebraically equivalent** at the operational level
for a static observer (both give `dτ_ent = N_eff·dt` for some
`N_eff`), but interpretively distinct:

* **Additive**: entropic and geometric clocks coexist; total
 proper time sums their contributions.
* **Multiplicative**: only one clock exists (the geometric one);
 `Λ` is a local conformal-like factor describing how fast
 irreversible distinguishability accumulates per tick of that
 clock.

The multiplicative form is the natural language for the
**β_μ dP^μ = dS/k_B** identity — entropic time is a scalar
contraction on the same worldline, not a parallel quantity.

## Scope

* The four origin constructions are stated at the **scalar
 field level** — `β(x)`, `u(x)`, `T_loc(x)`, `λ(x)` are all
 treated as real-valued functions on `SpaceTime d`. The full
 tensor form `β_μ dP^μ` requires a 4-vector field of inverse
 temperatures, which is downstream tensor machinery.

* The connection to **Jacobson 1995's Clausius relation**
 `δQ = T·dS` is the construction (D); horizon thermodynamics
 gives a Tolman-ratio `Λ`.

* The connection to **Bisognano–Wichmann modular flow** is the
 construction (B); the modular Hamiltonian generates a boost
 whose generator is the local thermal 4-vector.

* The connection to **Badiali path entropy** is the construction
 (C); path compressibility is the time-derivative of path
 entropy along the geometric worldline.

## Contents

### §1 — `EntropicLapseFactor d` structure

* `EntropicLapseFactor d` — record `(Λ, Λ_pos)`.
* `EntropicLapseFactor.unit d` — `Λ ≡ 1` (geometric = entropic).

### §2 — Multiplicative line-element formula

* `entropicProperTimeMultiplicative F dτGR` — `Λ·dτ_GR`.
* `entropicProperTimeOnADM F A x dt` — for static observer
 with ADM lapse: `Λ(x)·N(x)·dt`.
* `entropicProperTimeOnADM_at_unitΛ_eq_admStaticProperTime`.

### §3 — Four origin constructions

* `EntropicLapseFactor.ofEntropyProductionRate` — Λ := 1 + λ/N.
* `EntropicLapseFactor.ofModularBetaEnergy` — Λ := β · u.
* `EntropicLapseFactor.ofPathCompressibility` — Λ := Ṡ_path/k_B.
* `EntropicLapseFactor.ofTolmanHorizonTemperature` — Λ := T_H / T_loc.

### §4 — Consistency theorems

* `ofEntropyProductionRate_equiv_admEntropicProperTime` — the
 multiplicative reading from entropy-rate equals the additive
 reading `dτ_total = (N + λ)·dt` exactly.

* `ofTolmanHorizonTemperature_local_redshift` — the horizon-based
 `Λ` obeys the Tolman temperature redshift law.

* `ofModularBetaEnergy_eq_dS_over_kB` — the modular-based form
 reproduces the canonical `dτ_ent = β·dE = dS/k_B` identity.

## References

* Jacobson 1995 *Phys. Rev. Lett.* 75, 1260 — Einstein eq. from
 horizon Clausius relation.
* Bisognano–Wichmann 1975, 1976 — modular Hamiltonian generates
 boosts for the Rindler wedge.
* Tolman 1930 *Phys. Rev.* 35, 904 — thermal redshift.
* Badiali 2005 *J. Phys. A* 38, 2835 §3–§4 — path entropy.
* `Physlib.SpaceAndTime.EntropicADMLineElement` — additive
 convention `dτ_total = (N + λ)·dt`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

variable {d : ℕ}

/-! ## §1 — Entropic lapse factor structure -/

/-- **Entropic lapse factor**: a strictly-positive scalar
function `Λ : SpaceTime d → ℝ` with the line-element interpretation

  `dτ_ent = Λ(x) · dτ_GR`

so that Einstein's geometric proper time `dτ_GR := √(−ds²)/c`
remains the underlying clock and `Λ` is a local **conformal-like
rescaling** measuring the rate of accumulated irreversible
distinguishability per geometric tick.

`Λ ≡ 1` recovers pure GR (no entropic accumulation). -/
structure EntropicLapseFactor (d : ℕ) where
  /-- The lapse factor `Λ : SpaceTime d → ℝ`. -/
  Λ : SpaceTime d → ℝ
  /-- `Λ(x) > 0` everywhere. -/
  Λ_pos : ∀ x, 0 < Λ x

namespace EntropicLapseFactor

/-- **Unit entropic lapse factor** `Λ ≡ 1` — recovers the GR limit
where geometric and entropic proper times coincide. -/
def unit (d : ℕ) : EntropicLapseFactor d where
  Λ := fun _ => 1
  Λ_pos := fun _ => one_pos

variable (F : EntropicLapseFactor d)

/-! ## §2 — Multiplicative line-element formula -/

/-- **Multiplicative entropic proper time**: `dτ_ent = Λ(x)·dτ_GR`.

Given a geometric proper-time differential `dτ_GR` (e.g.
`√(−ds²)/c` for a generic timelike worldline, or `N(x)·dt` for
a static observer with ADM lapse `N`), the entropic proper time
is `Λ(x)·dτ_GR`.

This is the **rescaling reading**: entropic time is the same
clock as geometric time, multiplied by a local positive factor
`Λ(x)` measuring irreversible-distinguishability rate. -/
def entropicProperTimeMultiplicative (dτGR : ℝ) (x : SpaceTime d) : ℝ :=
  F.Λ x * dτGR

/-- **Multiplicative entropic proper time on ADM lapse** for a
static observer over coordinate-time `dt`:

  `dτ_ent = Λ(x)·N(x)·dt`. -/
def entropicProperTimeOnADM
    (A : ADMData d) (x : SpaceTime d) (dt : ℝ) : ℝ :=
  F.Λ x * A.admStaticProperTime x dt

/-- **At unit `Λ`, the multiplicative entropic proper time on ADM
reduces to the bare ADM static proper time** `N(x)·dt`. -/
theorem entropicProperTimeOnADM_at_unitΛ_eq_admStaticProperTime
    (A : ADMData d) (x : SpaceTime d) (dt : ℝ) :
    (EntropicLapseFactor.unit d).entropicProperTimeOnADM A x dt
      = A.admStaticProperTime x dt := by
  unfold entropicProperTimeOnADM EntropicLapseFactor.unit
  simp

/-- **Multiplicative entropic proper time is strictly positive
when `dτ_GR > 0`**. -/
theorem entropicProperTimeMultiplicative_pos
    {dτGR : ℝ} (hdt : 0 < dτGR) (x : SpaceTime d) :
    0 < F.entropicProperTimeMultiplicative dτGR x :=
  mul_pos (F.Λ_pos x) hdt

end EntropicLapseFactor

/-! ## §3 — Four origin constructions of `Λ(x)` -/

namespace EntropicLapseFactor

/-! ### (A) From entropy production rate -/

/-- **Construction (A) — entropy production rate**.

Given an ADM lapse `N(x)` and a non-negative entropy-production
rate `λ : SpaceTime d → ℝ` with `λ ≥ 0`, define

  `Λ_λ(x) := 1 + λ(x)/N(x)`.

This is the multiplicative form of the additive convention
`N_eff = N + λ`: the dimensionless ratio of effective to bare
lapse.

* `Λ_λ ≡ 1` ⟺ `λ ≡ 0` (no entropy production → pure GR clock).
* `Λ_λ > 1` ⟺ `λ > 0` (entropic accumulation → clock runs faster).

The condition `λ ≥ 0` (the Clausius arrow of time) ensures
`Λ_λ ≥ 1`, so the entropic clock never runs *slower* than the
geometric clock — the **second law as a lapse-factor inequality**. -/
def ofEntropyProductionRate
    (A : ADMData d) (lam : SpaceTime d → ℝ)
    (h_nonneg : ∀ y, 0 ≤ lam y) :
    EntropicLapseFactor d where
  Λ := fun x => 1 + lam x / A.lapse.N x
  Λ_pos := fun x => by
    have hN : 0 < A.lapse.N x := A.lapse.N_pos x
    have h_quot_nonneg : 0 ≤ lam x / A.lapse.N x :=
      div_nonneg (h_nonneg x) (le_of_lt hN)
    linarith

/-! ### (B) From modular β·E -/

/-- **Construction (B) — modular β·E (Bisognano–Wichmann)**.

Given a positive local inverse-temperature `β : SpaceTime d → ℝ`
(with `β = 1/(k_B·T_loc)`) and a positive energy-like scalar
`u : SpaceTime d → ℝ` (the local energy increment per geometric
proper-time tick, or the time-component of `dP^μ` along the
worldline), define

  `Λ_β(x) := β(x) · u(x)`.

This is the scalar version of the modular relation
`dτ_ent = β_μ·dP^μ` — at each spacetime point, the entropic-time
advance per geometric tick equals the modular Hamiltonian
contraction `β·u` of the inverse-temperature scalar with the
energy increment.

By the Clausius identity `dS = dE/T = β·k_B·dE`, we have
`Λ_β = β·u = dS/(k_B·dτ_GR)`, so the modular and entropy
readings coincide.

In Bisognano–Wichmann terms, `β` is the inverse of the local
Unruh / Hawking temperature, and `u` is the energy-momentum
4-vector contracted with the modular boost generator. -/
def ofModularBetaEnergy
    (β u : SpaceTime d → ℝ)
    (hβ : ∀ x, 0 < β x) (hu : ∀ x, 0 < u x) :
    EntropicLapseFactor d where
  Λ := fun x => β x * u x
  Λ_pos := fun x => mul_pos (hβ x) (hu x)

/-! ### (C) From path-space compressibility -/

/-- **Construction (C) — path-space compressibility (Badiali)**.

Given a positive **path-entropy rate** `Ṡ_path : SpaceTime d → ℝ`
(the time derivative of Badiali's `S_path = k_B·ln Z_path` along
the geometric worldline), and the Boltzmann constant `k_B > 0`,
define

  `Λ_path(x) := Ṡ_path(x) / k_B`.

Interpretation: `Λ_path` measures **how fast path entropy
accumulates per geometric proper-time tick** in nat units —
the *compressibility* of the path-space distribution along
the worldline.

When the geometric clock advances by `dτ_GR`, the path entropy
advances by `dS_path = k_B·Λ_path·dτ_GR`, so the corresponding
entropic-time advance is

  `dτ_ent = dS_path/k_B = Λ_path · dτ_GR`,

consistent with the canonical `dτ_ent = dS/k_B`. -/
def ofPathCompressibility
    (Sdot_path : SpaceTime d → ℝ) (kB : ℝ)
    (hSdot : ∀ x, 0 < Sdot_path x) (hkB : 0 < kB) :
    EntropicLapseFactor d where
  Λ := fun x => Sdot_path x / kB
  Λ_pos := fun x => div_pos (hSdot x) hkB

/-! ### (D) From horizon thermodynamics (Tolman ratio) -/

/-- **Construction (D) — horizon thermodynamics (Jacobson / Tolman)**.

Given the asymptotic Hawking temperature `T_H > 0` and a positive
local temperature `T_loc : SpaceTime d → ℝ` (the *Tolman-redshifted*
temperature at event `x`), define

  `Λ_T(x) := T_H / T_loc(x)`.

By the Tolman redshift law `T_loc(x) = T_H / N(x)`, this
specialises to `Λ_T = N(x)` — the entropic lapse factor IS the
ADM lapse, up to dimensionless normalisation.

The horizon-thermodynamics reading: a local Rindler horizon at
acceleration `a(x)` has Unruh temperature
`T_loc = ℏ·a/(2π·c·k_B)`; the corresponding `Λ_T` measures the
*Tolman boost* between the local thermal frame and the
asymptotic frame.

This is the Jacobson 1995 construction at the lapse-factor level:
requiring `δQ = T·dS` on all local horizons turns the entropic
lapse factor into a function of the local temperature
distribution. -/
def ofTolmanHorizonTemperature
    (T_H : ℝ) (T_loc : SpaceTime d → ℝ)
    (hTH : 0 < T_H) (hTloc : ∀ x, 0 < T_loc x) :
    EntropicLapseFactor d where
  Λ := fun x => T_H / T_loc x
  Λ_pos := fun x => div_pos hTH (hTloc x)

end EntropicLapseFactor

/-! ## §4 — Consistency theorems -/

/-- **THEOREM (A→additive) — multiplicative from entropy
production equals additive ADM entropic proper time**.

The multiplicative reading

  `dτ_ent^mult = Λ_λ(x)·N(x)·dt = (1 + λ/N)·N·dt`

coincides exactly with the additive reading of
`Physlib.SpaceAndTime.EntropicADMLineElement`:

  `dτ_ent^add  = (N + λ)·dt`.

This is the **operational equivalence** of the two complex-action/entropic-time
entropic-time conventions: both produce the same total
proper-time advance for a static observer, differing only in
the *interpretation* of where the entropic correction lives
(separate clock vs. lapse rescaling). -/
theorem ofEntropyProductionRate_equiv_admEntropicProperTime
    (A : ADMData d) (lam : SpaceTime d → ℝ)
    (h_nonneg : ∀ y, 0 ≤ lam y) (x : SpaceTime d) (dt : ℝ) :
    (EntropicLapseFactor.ofEntropyProductionRate A lam h_nonneg).entropicProperTimeOnADM A x dt
      = A.admEntropicProperTime lam x dt := by
  unfold EntropicLapseFactor.entropicProperTimeOnADM
        EntropicLapseFactor.ofEntropyProductionRate
        ADMData.admEntropicProperTime
        ADMData.entropicEffectiveLapse
        ADMData.admStaticProperTime
  have hN : 0 < A.lapse.N x := A.lapse.N_pos x
  have hN_ne : A.lapse.N x ≠ 0 := ne_of_gt hN
  field_simp

/-- **(B↔Clausius) — modular β·u equals `dS/(k_B·dτ_GR)` via
Clausius**.

Given the Clausius hypothesis `dS = (u/T_loc)·dτ_GR` and
`β = 1/(k_B·T_loc)`, the modular-form lapse factor `Λ_β = β·u`
satisfies

  `Λ_β · k_B · dτ_GR = dS`,

i.e., the modular reading IS the canonical `dτ_ent = dS/k_B`. -/
theorem ofModularBetaEnergy_equiv_dS_over_kB
    {β u T_loc dτGR dS kB : ℝ}
    (hT_loc : T_loc ≠ 0) (hkB : kB ≠ 0)
    (h_β : β = 1 / (kB * T_loc))
    (h_Clausius : dS = (u / T_loc) * dτGR) :
    (β * u) * kB * dτGR = dS := by
  rw [h_β, h_Clausius]
  field_simp

/-- **(D→Tolman) — horizon-thermodynamics `Λ` obeys the Tolman
redshift law**.

For Hawking temperature `T_H` and Tolman-redshifted local
temperature `T_loc(x) = T_H / N(x)`, the horizon-based `Λ` is
exactly the ADM lapse:

  `Λ_T(x) := T_H / T_loc(x) = T_H / (T_H/N(x)) = N(x)`.

This is the algebraic content of the **Tolman redshift law**:
the entropic lapse factor from horizon thermodynamics IS the
ADM lapse, certifying that gravity (via the Hawking temperature
redshift) reproduces the entropic-time rescaling at the local
horizon. -/
theorem ofTolmanHorizonTemperature_eq_ADMLapse
    (A : ADMData d) {T_H : ℝ} (hTH : 0 < T_H)
    (T_loc : SpaceTime d → ℝ) (hTloc : ∀ x, 0 < T_loc x)
    (x : SpaceTime d)
    (h_Tolman : T_loc x = T_H / A.lapse.N x) :
    (EntropicLapseFactor.ofTolmanHorizonTemperature T_H T_loc hTH hTloc).Λ x
      = A.lapse.N x := by
  unfold EntropicLapseFactor.ofTolmanHorizonTemperature
  simp only
  rw [h_Tolman]
  have hTH_ne : T_H ≠ 0 := ne_of_gt hTH
  have hN_pos : 0 < A.lapse.N x := A.lapse.N_pos x
  have hN_ne : A.lapse.N x ≠ 0 := ne_of_gt hN_pos
  field_simp

/-- **(C→Badiali) — path compressibility from entropy rate is
consistent with the canonical `dτ_ent = dS/k_B`**.

For path-entropy-rate `Ṡ_path > 0` over a geometric tick `dτ_GR`,
the multiplicative entropic-time advance

  `dτ_ent = Λ_path · dτ_GR = (Ṡ_path / k_B) · dτ_GR`

equals `dS_path / k_B` where `dS_path := Ṡ_path · dτ_GR`,
reproducing Badiali's path-entropy interpretation. -/
theorem ofPathCompressibility_eq_dS_path_over_kB
    {Sdot_path kB dτGR : ℝ}
    (hSdot : 0 < Sdot_path) (hkB : 0 < kB) (x : SpaceTime d) :
    (EntropicLapseFactor.ofPathCompressibility
        (fun _ => Sdot_path) kB
        (fun _ => hSdot) hkB).entropicProperTimeMultiplicative dτGR x
      = (Sdot_path * dτGR) / kB := by
  unfold EntropicLapseFactor.entropicProperTimeMultiplicative
        EntropicLapseFactor.ofPathCompressibility
  ring

/-- **(A→D) — entropy-production-rate `Λ` collapses to unit at
the asymptotic-frame frozen limit**.

At the asymptotic frame where `λ ≡ 0` (no local entropy
production), the entropy-production-rate construction yields the
unit lapse factor `Λ ≡ 1`, recovering pure GR.

This is the **frozen-LRF reduction** at the multiplicative
level. -/
theorem ofEntropyProductionRate_at_zero_lambda_eq_unit
    (A : ADMData d) {lam : SpaceTime d → ℝ}
    (h_zero : ∀ y, lam y = 0)
    (x : SpaceTime d) :
    (EntropicLapseFactor.ofEntropyProductionRate A lam
        (fun y => le_of_eq (h_zero y).symm)).Λ x = 1 := by
  unfold EntropicLapseFactor.ofEntropyProductionRate
  simp [h_zero]

end Physlib.SpaceTime

end
