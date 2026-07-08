/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Lapse

/-!
# ADM 3+1 line element with entropic proper-time correction

The Arnowitt–Deser–Misner (ADM, 1962) **3+1 decomposition** of a
Lorentzian spacetime metric writes the line element in the form

 `ds² = −N²·dt² + γ_ij·(dx^i + N^i·dt)·(dx^j + N^j·dt)`

with

* **`N(x)`** the **lapse function** — converts coordinate-time
 `dt` to proper-time `dτ` at event `x`,
* **`N^i(x)`** the **shift vector** — three spatial functions
 encoding how the spatial coordinates flow with coordinate time,
* **`γ_ij(x)`** the **spatial metric** — Riemannian 3-metric on
 the constant-`t` hypersurface.

For an observer at rest in the spatial coordinates (`dx^i = 0`),
the line element reduces to

 `ds² = −N²·dt²`, `dτ_geom = N(x)·dt`.

## Entropic proper-time correction

The complex-action/entropic-time entropic proper-time framework (already in physlib —
`Physlib.SpaceAndTime.EntropicProperTime`,
`Physlib.StatisticalMechanics.DiscreteEntropicTimeTrinity`) defines
the entropic-time advance

 `dτ_ent = λ(x(t))·dt`

along an observer's worldline, where `λ ≥ 0` is the local
entropy-production rate. The **total proper time** integrating
both contributions is (additive convention, matching
`Physlib.SpaceAndTime.EntropicProperTime.totalProperTimeMetric`):

 `dτ_total = dτ_geom + dτ_ent = (N(x) + λ(x))·dt`.

This file formalises:

1. The **ADM data** `(N, N^i, γ_ij)` as a structural structure.
2. The **ADM line element** `ds²` as a scalar pointwise quantity
 on the differentials `(dt, dx^i)`.
3. The **static-observer reduction** `dτ_geom = N·dt`.
4. The **entropic-effective lapse**
 `N_eff(x, λ) := N(x) + λ(x)` and the corresponding total
 proper-time advance `dτ_total = N_eff·dt`.
5. The **frozen-LRF reduction**: at `λ = 0` (no entropy
 production), `N_eff = N` and total proper time = geometric
 proper time.

## Scope

* The lapse, shift, and spatial-metric are treated as **arbitrary
 functions of spacetime point** — no Einstein-equation
 constraints (Hamiltonian / momentum constraints) are imposed
 here. Those constraints are downstream physics.
* The line element is treated **pointwise on differentials**,
 not as an integrated arc-length functional. Arc-length
 integration would require the path-integral machinery of
 `Physlib.QFT.PathIntegral.MeasureModel` (Bochner) and is left
 for a follow-up.
* The entropic correction is taken in the **additive convention**
 (matching `totalProperTimeMetric`) for compatibility with the
 existing physlib `EntropicProperTime` infrastructure.

## Contents

### §1 — ADM data structure

* `ADMData d` — lapse, shift, spatial metric (with positivity).

### §2 — ADM line element

* `admLineElementSquared` — full ADM `ds²` on differentials.
* `admLineElementSquared_static` — static-observer specialisation
 (`dx^i = 0`).
* `admStaticProperTime` — `dτ_geom = N·dt`.

### §3 — Entropic-effective lapse

* `entropicEffectiveLapse` — `N_eff(x, λ) := N(x) + λ(x)`.
* `entropicEffectiveLapse_pos`.
* `admEntropicProperTime` — `dτ_total = N_eff·dt`.

### §4 — Bridge identities

* `admEntropicProperTime_eq_admStaticProperTime_at_zero_lambda` —
 at `λ = 0`, total = geometric.
* **`admEntropicProperTime_decomposes`** — the central bridge:
 total proper-time advance splits as
 `dτ_total = dτ_geom + dτ_ent`,
 realising the `totalProperTimeMetric = geometricInterval +
 entropicProperTimeMetric` of
 `Physlib.SpaceAndTime.EntropicProperTime` at the ADM
 differential level.

## References

* Arnowitt, Deser, Misner 1962 *Phys. Rev.* 124, 1595 — the ADM
 3+1 decomposition.
* Misner, Thorne, Wheeler *Gravitation* §21.4 — modern ADM.
* `Physlib.SpaceAndTime.SpaceTime.Lapse` — `Lapse d` structure.
* `Physlib.SpaceAndTime.EntropicProperTime` —
 `totalProperTimeMetric`.
* `Physlib.StatisticalMechanics.DiscreteEntropicTimeTrinity` —
 discrete entropic-time accumulation.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

variable {d : ℕ}

/-! ## §1 — ADM data structure -/

/-- **ADM 3+1 decomposition data** on `SpaceTime d`.

Packages:

* `lapse  : Lapse d`              — the lapse `N(x) > 0`,
* `shift  : SpaceTime d → Fin d → ℝ`  — the shift `N^i(x)`,
* `spatialMetric : SpaceTime d → Fin d → Fin d → ℝ`
                                  — the spatial 3-metric `γ_ij(x)`.

The spatial metric is unconstrained at this layer (no symmetry or
positive-definite hypothesis); downstream consumers may add them
as separate structures. -/
structure ADMData (d : ℕ) where
  /-- Lapse function `N(x)`. -/
  lapse : Lapse d
  /-- Shift vector `N^i(x)`. -/
  shift : SpaceTime d → Fin d → ℝ
  /-- Spatial metric `γ_ij(x)`. -/
  spatialMetric : SpaceTime d → Fin d → Fin d → ℝ

namespace ADMData

variable (A : ADMData d)

/-! ## §2 — ADM line element on differentials -/

/-- **ADM line element on differentials**:

  `ds² := −N(x)²·dt² + γ_ij(x)·(dx^i + N^i·dt)·(dx^j + N^j·dt)`.

At spacetime event `x`, given a coordinate-time differential `dt`
and spatial differentials `dx : Fin d → ℝ`, returns the scalar
`ds²`.  Uses `Finset.sum` over the spatial indices for the
double contraction. -/
def admLineElementSquared
    (x : SpaceTime d) (dt : ℝ) (dx : Fin d → ℝ) : ℝ :=
  -(A.lapse.N x)^2 * dt^2
    + ∑ i : Fin d, ∑ j : Fin d,
        A.spatialMetric x i j
          * (dx i + A.shift x i * dt)
          * (dx j + A.shift x j * dt)

/-- **Static-observer specialisation**: when `dx^i = 0` (observer
at rest in the spatial coordinates), the ADM line element reduces
to a function of `dt` alone.

  `ds²_static = −N²·dt² + γ_ij·(N^i·dt)·(N^j·dt)
              = (−N² + γ_ij·N^i·N^j)·dt²`. -/
def admLineElementSquared_static
    (x : SpaceTime d) (dt : ℝ) : ℝ :=
  admLineElementSquared A x dt (fun _ => 0)

/-! ## §3 — Static geometric proper time `dτ_geom = N·dt` -/

/-- **Geometric proper-time advance for a static observer**:

  `dτ_geom := N(x)·dt`.

This is the **standard ADM proper-time** for an observer at rest
in the spatial coordinates.  When the shift vanishes (or is
negligible at the chosen event), this coincides with the
positive square root of `−ds²_static` modulo the contribution of
`γ_ij·N^i·N^j`. -/
def admStaticProperTime (x : SpaceTime d) (dt : ℝ) : ℝ :=
  A.lapse.N x * dt

/-- **Static geometric proper time positivity** (for positive `dt`). -/
theorem admStaticProperTime_pos
    {x : SpaceTime d} {dt : ℝ} (hdt : 0 < dt) :
    0 < A.admStaticProperTime x dt :=
  mul_pos (A.lapse.N_pos x) hdt

/-- **In the Minkowski limit `N ≡ 1`**, `dτ_geom = dt`. -/
theorem admStaticProperTime_at_unit_lapse_eq_dt
    (x : SpaceTime d) (dt : ℝ)
    (h_unit : ∀ y, A.lapse.N y = 1) :
    A.admStaticProperTime x dt = dt := by
  unfold admStaticProperTime
  rw [h_unit x]
  ring

/-! ## §4 — Entropic-effective lapse + total proper time -/

/-- **Entropic-effective lapse**:

  `N_eff(x; λ) := N(x) + λ(x)`,

where `λ : SpaceTime d → ℝ` is the **local entropy-production
rate** along the observer's worldline.

The effective lapse converts coordinate-time differential `dt`
into the *total* proper-time differential `dτ_total = N_eff·dt`
combining geometric and entropic contributions.

This is the additive convention, matching
`Physlib.SpaceAndTime.EntropicProperTime.totalProperTimeMetric`. -/
def entropicEffectiveLapse
    (lam : SpaceTime d → ℝ) (x : SpaceTime d) : ℝ :=
  A.lapse.N x + lam x

/-- **Entropic-effective lapse is strictly positive** when
`λ ≥ 0`. -/
theorem entropicEffectiveLapse_pos
    {lam : SpaceTime d → ℝ} (h_lam_nonneg : ∀ y, 0 ≤ lam y) (x : SpaceTime d) :
    0 < A.entropicEffectiveLapse lam x := by
  unfold entropicEffectiveLapse
  have : 0 < A.lapse.N x := A.lapse.N_pos x
  linarith [h_lam_nonneg x]

/-- **ADM entropic total proper time** for a static observer:

  `dτ_total := N_eff(x; λ)·dt = (N(x) + λ(x))·dt`.

Combines the geometric (ADM lapse) and entropic
(rate `λ`) contributions to the worldline proper time. -/
def admEntropicProperTime
    (lam : SpaceTime d → ℝ) (x : SpaceTime d) (dt : ℝ) : ℝ :=
  A.entropicEffectiveLapse lam x * dt

/-! ## §5 — Bridge identities -/

/-- **At zero entropy-production rate `λ ≡ 0`, the total proper
time reduces to the geometric proper time** —  the
**frozen-LRF** condition of physlib's `EntropicProperTime` lifted
to the ADM differential level.

`dτ_total = dτ_geom` ⟺ `λ(x) = 0` (at the chosen event). -/
theorem admEntropicProperTime_eq_admStaticProperTime_at_zero_lambda
    {lam : SpaceTime d → ℝ}
    (h_zero : ∀ y, lam y = 0)
    (x : SpaceTime d) (dt : ℝ) :
    A.admEntropicProperTime lam x dt = A.admStaticProperTime x dt := by
  unfold admEntropicProperTime entropicEffectiveLapse admStaticProperTime
  rw [h_zero x]
  ring

/-- **:additive decomposition of the total proper time**:

  `dτ_total = dτ_geom + dτ_ent`,

where `dτ_geom := N(x)·dt` (ADM lapse) and
`dτ_ent := λ(x)·dt` (entropic-rate accumulation).

This is the **ADM differential lift** of the
`totalProperTimeMetric = geometricInterval +
entropicProperTimeMetric` identity in
`Physlib.SpaceAndTime.EntropicProperTime`.

The decomposition shows that the entropic correction enters the
GR line element **additively at the lapse level** — the
effective lapse `N_eff = N + λ` is what an entropically
dissipating observer experiences as the rate of proper time per
coordinate time. -/
theorem admEntropicProperTime_decomposes
    (lam : SpaceTime d → ℝ) (x : SpaceTime d) (dt : ℝ) :
    A.admEntropicProperTime lam x dt
      = A.admStaticProperTime x dt + lam x * dt := by
  unfold admEntropicProperTime entropicEffectiveLapse admStaticProperTime
  ring

/-! ## §6 — Tolman-style entropic redshift -/

/-- **Tolman-style local-asymptotic identity for the effective lapse**:

  `(N_eff(x; λ))·(asymptotic / N_eff(x; λ)) = asymptotic`.

The entropic-effective lapse obeys the same algebraic Tolman
identity as the bare lapse — the entropic correction does not
spoil the local-asymptotic-frame structure used throughout
physlib. -/
theorem entropicEffectiveLapse_tolman_invariant
    {lam : SpaceTime d → ℝ} (h_lam_nonneg : ∀ y, 0 ≤ lam y)
    (O_inf : ℝ) (x : SpaceTime d) :
    (O_inf / A.entropicEffectiveLapse lam x) * A.entropicEffectiveLapse lam x
      = O_inf := by
  have hN_eff_pos : 0 < A.entropicEffectiveLapse lam x :=
    A.entropicEffectiveLapse_pos h_lam_nonneg x
  field_simp

end ADMData

end Physlib.SpaceTime

end
