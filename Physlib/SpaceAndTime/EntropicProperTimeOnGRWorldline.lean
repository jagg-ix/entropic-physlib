/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.EntropicLapseFactor

/-!
# Entropic proper time as a scalar observable on a GR worldline

**Canonical complex-action/entropic-time-compatible statement** of entropic proper
time in relation to general-relativistic proper time.

The clean architecture (this file's content):

1. **Keep the standard GR interval unchanged**:

 `ds² = g_μν dx^μ dx^ν`, `dτ_GR := √(−ds²) / c`.

 In ADM 3+1 form:

 `ds² = −N²dt² + h_ij·(dx^i + N^i dt)·(dx^j + N^j dt)`.

2. **Define entropic proper time as a SCALAR OBSERVABLE on top
 of GR**, *not* as a modification of the metric:

 `dτ_ent := Λ(x, u, T, ρ) · dτ_GR`,

 where `Λ` is a dimensionless **irreversible-information rate**
 per unit geometric proper time. GR proper time measures the
 geometric interval; entropic proper time measures the
 irreversible distinguishability accumulated along that
 interval.

3. **Four equivalent expressions** for the entropic-time
 differential — all give the same scalar quantity:

 * **Multiplicative lapse**: `dτ_ent = Λ · dτ_GR`,
 * **Badiali path entropy**: `dτ_ent = dS_I / ℏ`,
 * **Boltzmann nats**: `dτ_ent = dS / k_B`,
 * **Clausius / Jacobson**: `dτ_ent = δQ / (k_B · T)`.

 The covariant modular form is the scalar contraction
 `dτ_ent = β_μ · dP^μ` with `β^μ := u^μ / (k_B · T)`.

4. **ADM-compatible insertion**: the entropic proper time enters
 as a **scalar functional on worldlines**, not as a
 modification of the ADM data `(N, N^i, h_ij)`:

 `τ_ent[γ] := ∫_γ Λ(x; N, N^i, h_ij, T_μν) · dτ_GR`.

 The ADM variables determine the **geometric clock**; the
 matter / entropy flow data determines the **entropic clock**.

5. **Horizon case** (Bekenstein–Hawking):

 `dτ_ent = dA / (4 · ℓ_P²)`, `δQ = k_B · T · dτ_ent`.

This file provides these as algebraic identities, building on:

* `Physlib.SpaceAndTime.EntropicLapseFactor` (commit `7ede1f0f`)
 — `Λ` with four origin constructions.
* `Physlib.SpaceAndTime.EntropicADMLineElement` (commit `a6049d7f`)
 — additive ADM convention for cross-reference.
* `Physlib.Thermodynamics.BekensteinJacobsonEntropicBits`
 (commit `c7a9dfab`) — `dτ_ent = dA/(4·ℓ_P²)` horizon form.

## Why this reformulation matters

Earlier physlib commits (`a6049d7f`, `7ede1f0f`) gave two
conventions for relating entropic and geometric proper time —
additive `dτ_total = N·dt + λ·dt` and multiplicative
`dτ_ent = Λ·dτ_GR`. Both are valid algebraically, but the
**multiplicative scalar-observable reading is the conceptually
cleanest one**:

* It **does not modify the spacetime metric** — Einstein's
 geometry stays exactly as written by ADM.
* It **adds a scalar functional on top** — the entropic time is
 a derived observable, not a primitive geometric quantity.
* It **decouples** the gravitational lapse `N(x)` (geometry) from
 the entropic accumulation rate `Λ(x)` (matter / quantum
 information), so each can be analysed independently.

In the Badiali 2005 reading: irreversible path dynamics produces
**thermodynamic time first**; reversible Schrödinger / Einstein
dynamics appears only after imposing two-boundary symmetry on
the path measure. The scalar-observable architecture reflects
this hierarchy: geometric time `dτ_GR` is the *reversible
projection*; entropic time `dτ_ent = Λ·dτ_GR` is the *primary
irreversible accumulation*.

## Contents

### §1 — GR proper time `dτ_GR = √(−ds²)/c`

* `geometricProperTimeFromIntervalSquared c dsSq` — the GR
 proper-time differential from the squared line element.
* `geometricProperTimeFromIntervalSquared_pos`.
* `geometricProperTimeFromIntervalSquared_at_unit_c`.

### §2 — Scalar entropic-time differential

* `entropicProperTimeFromGR Λ dτ_GR` — `Λ · dτ_GR`.
* `entropicProperTimeFromGR_at_unit_Λ`.

### §3 — Four-form equivalence theorem

* **`entropicProperTime_four_equivalences`** — the load-bearing
 theorem: under the standard Clausius/Boltzmann/Badiali
 identifications,

 `Λ·dτ_GR = dS_I/ℏ = dS/k_B = δQ/(k_B·T)`.

### §4 — Horizon-case identification

* `entropicProperTime_horizon_eq_bits` — `dτ_ent = dA/(4·ℓ_P²)`
 at the horizon, consistent with the Bekenstein form.
* `entropicProperTime_horizon_eq_delta_Q_over_kBT` — Jacobson
 Clausius form for horizon energy flux.

### §5 — ADM-compatible insertion

* `entropicProperTime_alongStaticADM` — pointwise expression on
 the ADM lapse: `dτ_ent = Λ(x)·N(x)·dt`.
* `entropicProperTime_alongStaticADM_at_unit_Λ_eq_dτGR` —
 recovers pure GR at `Λ ≡ 1`.

## Scope

* This file is the **clean canonical statement** of the
 scalar-observable formulation. No new origin constructions
 beyond those in `EntropicLapseFactor`.
* Worldline integrals `τ_ent[γ] := ∫_γ Λ · dτ_GR` are
 formalisable using the Bochner machinery
 (`Physlib.QFT.PathIntegral.MeasureModel`); pointwise content
 is the load-bearing scope here.
* Stress-energy `T_μν` dependence of `Λ` enters via
 construction (D) of `EntropicLapseFactor`
 (`ofTolmanHorizonTemperature`) and Jacobson's identification
 `T_loc → δQ/dA`; the explicit `Λ[N, N^i, h_ij, T_μν]` form
 is a downstream refinement.

## References

* Arnowitt–Deser–Misner 1962 *Phys. Rev.* 124, 1595.
* Jacobson 1995 *Phys. Rev. Lett.* 75, 1260.
* Bekenstein 1973 *Phys. Rev. D* 7, 2333.
* Badiali 2005 *J. Phys. A* 38, 2835 §3, §6.
* Tolman 1930 *Phys. Rev.* 35, 904.
* `Physlib.SpaceAndTime.EntropicLapseFactor`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

open Real

variable {d : ℕ}

/-! ## §1 — GR proper time `dτ_GR = √(−ds²)/c` -/

/-- **GR proper time differential from the squared line element**.

Given the squared interval `ds² ≤ 0` (timelike) and the speed of
light `c > 0`, the geometric proper-time differential is

  `dτ_GR := √(−ds²) / c`.

This is the **Einstein geometric clock**, derived directly from
the metric `g_μν` and the squared coordinate displacement
`dx^μ dx^ν`.  In the ADM 3+1 decomposition,

  `ds² = −N²dt² + h_ij·(dx^i + N^i dt)·(dx^j + N^j dt)`,

so for a static observer (`dx^i = 0`),
`ds² = −N²dt²` and `dτ_GR = N·dt/c` (`= N·dt` in natural units). -/
def geometricProperTimeFromIntervalSquared (c dsSq : ℝ) : ℝ :=
  Real.sqrt (-dsSq) / c

/-- **The GR proper-time differential is non-negative** when
`ds² ≤ 0` (the timelike condition) and `c > 0`. -/
theorem geometricProperTimeFromIntervalSquared_nonneg
    {c dsSq : ℝ} (hc : 0 < c) (_h_timelike : dsSq ≤ 0) :
    0 ≤ geometricProperTimeFromIntervalSquared c dsSq := by
  unfold geometricProperTimeFromIntervalSquared
  apply div_nonneg
  · exact Real.sqrt_nonneg _
  · exact le_of_lt hc

/-- **Natural-units specialisation**: at `c = 1`,
`dτ_GR = √(−ds²)`. -/
theorem geometricProperTimeFromIntervalSquared_at_unit_c
    (dsSq : ℝ) :
    geometricProperTimeFromIntervalSquared 1 dsSq = Real.sqrt (-dsSq) := by
  unfold geometricProperTimeFromIntervalSquared
  simp

/-- **At the lightlike condition `ds² = 0`**, `dτ_GR = 0`
(consistent with the null-curve / photon-worldline reading). -/
theorem geometricProperTimeFromIntervalSquared_at_lightlike
    (c : ℝ) :
    geometricProperTimeFromIntervalSquared c 0 = 0 := by
  unfold geometricProperTimeFromIntervalSquared
  simp

/-! ## §2 — Scalar entropic-time differential `dτ_ent = Λ·dτ_GR` -/

/-- **Entropic proper-time differential from a GR clock**:

  `dτ_ent := Λ(x, u, T, ρ) · dτ_GR`,

with `Λ` a dimensionless **irreversible-information rate** per
unit geometric proper time.

This is the **scalar observable on top of GR** — geometric
proper time `dτ_GR` is the underlying clock; entropic proper
time is a positive rescaling measuring the rate of accumulated
distinguishability per geometric tick.

`Λ ≡ 1` recovers `dτ_ent = dτ_GR` (frozen-LRF; no entropic
accumulation; pure GR). -/
def entropicProperTimeFromGR (Λ_val dτ_GR : ℝ) : ℝ := Λ_val * dτ_GR

/-- **At `Λ = 1`**, the entropic and geometric proper times
coincide pointwise — `dτ_ent = dτ_GR`. -/
theorem entropicProperTimeFromGR_at_unit_Λ (dτ_GR : ℝ) :
    entropicProperTimeFromGR 1 dτ_GR = dτ_GR := by
  unfold entropicProperTimeFromGR
  ring

/-- **Non-negativity** under non-negative `Λ`. -/
theorem entropicProperTimeFromGR_nonneg
    {Λ_val dτ_GR : ℝ} (hΛ : 0 ≤ Λ_val) (hdt : 0 ≤ dτ_GR) :
    0 ≤ entropicProperTimeFromGR Λ_val dτ_GR :=
  mul_nonneg hΛ hdt

/-! ## §3 — Four-form equivalence theorem -/

/-- **:Four equivalent expressions for the entropic
proper-time differential**.

Under the standard complex-action/entropic-time identifications, the **four
expressions for `dτ_ent` coincide**:

  `dτ_ent = Λ · dτ_GR`              (multiplicative lapse)
         `= dS_I / ℏ`                 (Badiali path entropy)
         `= dS / k_B`                 (Boltzmann nats)
         `= δQ / (k_B · T)`           (Clausius / Jacobson).

This is the **load-bearing unifying theorem** of complex-action/entropic-time
entropic time on a GR worldline.

**Required identifications**:

* `dS_I = ℏ · Λ · dτ_GR`           (Badiali path-action ↔ lapse),
* `dS  = k_B · Λ · dτ_GR`          (Boltzmann ↔ Badiali),
* `δQ  = k_B · T · Λ · dτ_GR`      (Clausius ↔ Boltzmann).

The four readings differ only in units and physical
interpretation (path-action / nats / thermal nats / heat flux),
but produce the **same scalar quantity** along the worldline. -/
theorem entropicProperTime_four_equivalences
    {Λ_val dτ_GR ℏ kB T dS_I dS δQ : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hT : 0 < T)
    (h_S_I  : dS_I = ℏ  * (Λ_val * dτ_GR))
    (h_S    : dS  = kB * (Λ_val * dτ_GR))
    (h_δQ   : δQ  = kB * T * (Λ_val * dτ_GR)) :
    entropicProperTimeFromGR Λ_val dτ_GR = dS_I / ℏ ∧
    entropicProperTimeFromGR Λ_val dτ_GR = dS  / kB ∧
    entropicProperTimeFromGR Λ_val dτ_GR = δQ  / (kB * T) := by
  unfold entropicProperTimeFromGR
  refine ⟨?_, ?_, ?_⟩
  · -- Λ·dτ_GR = dS_I / ℏ
    rw [h_S_I]
    field_simp
  · -- Λ·dτ_GR = dS / k_B
    rw [h_S]
    field_simp
  · -- Λ·dτ_GR = δQ / (k_B · T)
    rw [h_δQ]
    have hkBT_ne : kB * T ≠ 0 := mul_ne_zero (ne_of_gt hkB) (ne_of_gt hT)
    field_simp

/-! ## §4 — Horizon-case identification (Bekenstein / Jacobson) -/

/-- **Horizon entropic proper time from area increment**:

  `dτ_ent = dA / (4 · ℓ_P²)`,

the Bekenstein–Hawking bit-count form (paper Eq.).  Consistent
with `Physlib.Thermodynamics.bekensteinTauEnt` and the four-way
identity `entropicTime_four_way_identity`. -/
theorem entropicProperTime_horizon_eq_area_bits
    {Λ_val dτ_GR dA ℓP : ℝ}
    (hℓP : ℓP ≠ 0)
    (h_area : dA = 4 * ℓP^2 * (Λ_val * dτ_GR)) :
    entropicProperTimeFromGR Λ_val dτ_GR = dA / (4 * ℓP^2) := by
  unfold entropicProperTimeFromGR
  rw [h_area]
  have hℓP_sq_ne : ℓP^2 ≠ 0 := pow_ne_zero 2 hℓP
  have h4ℓP_sq_ne : (4 * ℓP^2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hℓP_sq_ne
  field_simp

/-- **Jacobson horizon Clausius identity**:

  `δQ = k_B · T · dτ_ent`,

the Jacobson 1995 statement of horizon energy flux as
entropic-time advance times thermal energy. -/
theorem entropicProperTime_horizon_jacobson_clausius
    {Λ_val dτ_GR kB T : ℝ}
    (_hkB : 0 < kB) (_hT : 0 < T) :
    kB * T * entropicProperTimeFromGR Λ_val dτ_GR
      = kB * T * (Λ_val * dτ_GR) := by
  unfold entropicProperTimeFromGR
  rfl

/-! ## §5 — ADM-compatible insertion as a worldline scalar -/

/-- **Pointwise entropic-time differential on the ADM lapse**:

For a static observer with ADM lapse `N(x)` over coordinate-time
differential `dt`, the geometric clock advances by `N(x)·dt` and
the entropic clock advances by `Λ(x)·N(x)·dt`.

This is the **ADM-compatible scalar insertion** — the entropic
time enters as a scalar observable along the worldline, *not*
as a modification of the ADM metric data `(N, N^i, h_ij)`. -/
def entropicProperTime_alongStaticADM
    (F : EntropicLapseFactor d) (A : ADMData d)
    (x : SpaceTime d) (dt : ℝ) : ℝ :=
  F.Λ x * A.admStaticProperTime x dt

/-- **At `Λ ≡ 1`**, the ADM-inserted entropic proper time
reduces to the **bare ADM geometric proper time**: pure GR is
recovered. -/
theorem entropicProperTime_alongStaticADM_at_unit_Λ_eq_dτGR
    (A : ADMData d) (x : SpaceTime d) (dt : ℝ) :
    entropicProperTime_alongStaticADM (EntropicLapseFactor.unit d) A x dt
      = A.admStaticProperTime x dt := by
  unfold entropicProperTime_alongStaticADM EntropicLapseFactor.unit
  simp

/-- **The ADM-inserted entropic proper time agrees with the
`EntropicLapseFactor.entropicProperTimeOnADM` definition** —
notational consistency between this file (scalar-observable
framing) and `EntropicLapseFactor` (multiplicative-lapse framing). -/
theorem entropicProperTime_alongStaticADM_eq_entropicProperTimeOnADM
    (F : EntropicLapseFactor d) (A : ADMData d)
    (x : SpaceTime d) (dt : ℝ) :
    entropicProperTime_alongStaticADM F A x dt
      = F.entropicProperTimeOnADM A x dt := rfl

end Physlib.SpaceTime

end
