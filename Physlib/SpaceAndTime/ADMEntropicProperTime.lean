/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.EntropicADMLineElement
public import Physlib.SpaceAndTime.EntropicProperTime

/-!
# Bridge: ADM entropic line element ↔ `totalProperTimeMetric`

Companion to:
* `Physlib.SpaceAndTime.EntropicADMLineElement` —
  `admEntropicProperTime`, ADM `dτ_total = (N + λ)·dt`.
* `Physlib.SpaceAndTime.EntropicProperTime` —
  `totalProperTimeMetric U q p ρ σ
   := geometricInterval q p + entropicProperTimeMetric U ρ σ`.

These two files use **different conventions** for the entropic
correction:

* **Rate-based** (ADM file): `dτ_ent = λ(x(t))·dt` along a
  worldline, where `λ : SpaceTime d → ℝ` is the local
  entropy-production rate.
* **State-based** (EntropicProperTime file):
  `τ_ent = scale · D(ρ‖σ)` between two quantum states `ρ, σ`,
  using `EntropicTimeUnits.scale = ℏ/(k_B·T_∞)`.

This bridge file formalises their **algebraic equivalence** for a
static observer at fixed event `x` over a coordinate-time
interval `dt`:

  `admEntropicProperTime A lam x dt = totalProperTimeMetric U q p ρ σ`

when

* `A.admStaticProperTime x dt = geometricInterval q p`  (ADM
  static proper time matches the Minkowski interval), and
* `lam x · dt = entropicProperTimeMetric U ρ σ`  (rate-integrated
  entropic advance matches state-relative-entropy-gap advance).

This is the **identification** of the two complex-action/entropic-time entropic-time
formulations at the level of the ADM line-element decomposition.

## Why this matters

The complex-action/entropic-time framework supports two physically distinct
entropic-time readings:

1. **Rate reading** (Badiali, Jacobson Clausius): an
   instantaneous `λ(x)` integrated over coordinate time.
2. **State reading** (quantum information, Petz / KL divergence):
   a relative-entropy gap `D(ρ‖σ)` between two quantum states.

The ADM line-element decomposition

  `dτ_total = N·dt + λ·dt`

is the rate reading.  The `totalProperTimeMetric` decomposition

  `τ_total = geometricInterval + scale · D(ρ‖σ)`

is the state reading.  This bridge certifies that, *when the
rate-integral matches the entropy-gap*, the two readings give
the **same number**.

In ADM language: **the entropy-production rate `λ(x)` acts as a
modification of the lapse function `N(x)`**.  The effective
lapse `N_eff := N + λ` is what an entropically dissipating
observer experiences as the rate of proper time per coordinate
time.

## Contents

### §1 — Matching identity

* **`admEntropicProperTime_eq_totalProperTimeMetric`** — the
  load-bearing bridge identity.

### §2 — Frozen-LRF case

* `admEntropicProperTime_eq_geometricInterval_at_zero_lambda_frozenLRF` —
  at `λ ≡ 0` and `ρ = σ`, the ADM and state readings both
  collapse to `geometricInterval`.

### §3 — Effective-lapse Tolman identification

* `entropicEffectiveLapse_local_tolman` — the effective lapse
  obeys the same Tolman local-asymptotic identity as the bare
  lapse (lifted from `EntropicADMLineElement`).

## References

* Arnowitt–Deser–Misner 1962 *Phys. Rev.* 124, 1595.
* Tolman 1930 *Phys. Rev.* 35, 904 — temperature redshift.
* `Physlib.SpaceAndTime.EntropicADMLineElement` —
  `admEntropicProperTime`.
* `Physlib.SpaceAndTime.EntropicProperTime` —
  `totalProperTimeMetric`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

open QuantumInfo.Finite

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {sd : ℕ}

/-! ## §1 — Matching identity -/

/-- **Bridge identity**: ADM entropic proper time matches
`totalProperTimeMetric` under matching hypotheses.

Given an ADM data structure `A`, an entropy-production rate
`λ : SpaceTime sd → ℝ`, entropic time units `U`, two spacetime
events `q, p`, two quantum states `ρ, σ`, an event `x`, and a
coordinate-time interval `dt`, the **ADM total proper time
equals the state-based total proper time** provided

* the ADM geometric piece matches the Minkowski interval:
  `A.admStaticProperTime x dt = geometricInterval q p`,
* the rate-integrated entropic advance matches the
  relative-entropy-gap advance:
  `λ x · dt = entropicProperTimeMetric U ρ σ`.

**Algebraic core**: linearity of the additive decomposition. -/
theorem admEntropicProperTime_eq_totalProperTimeMetric
    (A : ADMData sd) (lam : SpaceTime sd → ℝ)
    (U : EntropicTimeUnits) (q p : SpaceTime sd)
    (ρ σ : MState d) (x : SpaceTime sd) (dt : ℝ)
    (h_geom : A.admStaticProperTime x dt = geometricInterval q p)
    (h_ent  : lam x * dt = entropicProperTimeMetric U ρ σ) :
    A.admEntropicProperTime lam x dt
      = totalProperTimeMetric U q p ρ σ := by
  rw [A.admEntropicProperTime_decomposes lam x dt]
  rw [h_geom, h_ent]
  rfl

/-! ## §2 — Frozen-LRF case -/

/-- **Frozen-LRF collapse**: at `λ ≡ 0` and `ρ = σ`, both ADM
and state-based total proper times collapse to `geometricInterval`.

This is the **double frozen condition**:
* No entropy production rate (`λ = 0`),
* No relative-entropy gap (`ρ = σ`).

In complex-action/entropic-time language: the **geometric proper time emerges as the
frozen-LRF residue** when the system is fully thermalised. -/
theorem admEntropicProperTime_eq_geometricInterval_at_zero_lambda_frozenLRF
    (A : ADMData sd) (lam : SpaceTime sd → ℝ)
    (U : EntropicTimeUnits) (q p : SpaceTime sd)
    (ρ : MState d) (x : SpaceTime sd) (dt : ℝ)
    (h_zero_lam : ∀ y, lam y = 0)
    (h_geom : A.admStaticProperTime x dt = geometricInterval q p) :
    A.admEntropicProperTime lam x dt
      = totalProperTimeMetric U q p ρ ρ := by
  rw [totalProperTimeMetric_at_frozen]
  rw [A.admEntropicProperTime_eq_admStaticProperTime_at_zero_lambda
        h_zero_lam x dt]
  exact h_geom

/-! ## §3 — Effective-lapse Tolman identification -/

/-- **Effective-lapse local-asymptotic Tolman identity**.

For non-negative entropy-production rate `λ ≥ 0`, the
entropic-effective lapse `N_eff = N + λ` obeys the same algebraic
Tolman identity as the bare lapse:

  `(O_∞ / N_eff(x; λ)) · N_eff(x; λ) = O_∞`.

Direct corollary of `entropicEffectiveLapse_tolman_invariant`. -/
theorem effectiveLapse_local_tolman
    (A : ADMData sd) {lam : SpaceTime sd → ℝ}
    (h_lam_nonneg : ∀ y, 0 ≤ lam y)
    (O_inf : ℝ) (x : SpaceTime sd) :
    (O_inf / A.entropicEffectiveLapse lam x)
        * A.entropicEffectiveLapse lam x
      = O_inf :=
  A.entropicEffectiveLapse_tolman_invariant h_lam_nonneg O_inf x

end Physlib.SpaceTime

end
