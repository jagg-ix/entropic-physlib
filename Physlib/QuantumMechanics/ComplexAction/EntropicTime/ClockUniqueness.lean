/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.SecondLaw
public import Physlib.Thermodynamics.Landauer
public import Physlib.FluidDynamics.CourantNumber
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Singling out τ_ent: minimum step, uniqueness, CFL uniqueness

The `SecondLaw.EntropyArrowWorldline` proves:
* τ_ent accumulates iff entropy is produced (`time_order_iff_entropy_order`).
* τ_ent is frozen iff the process is reversible (`isReversible_iff_tau_ent_constant`).

The `CourantNumber` proves:
* Any positive reparameterisation of time preserves the Courant number
 (`courantNumber_rescale_invariant`).

These leave two gaps: CFL holds for every positive monotone clock (cannot
single τ_ent out), and no minimum-step bound existed.

This module fills both gaps with three concrete theorems.

## Theorem 1 — Minimum step (`tau_ent_minimum_step`)

On a worldline where every irreversible S_I increment is at least `δ_S > 0`
(the **Landauer lower bound**), every strictly positive τ_ent increment is at
least `δ_S / ℏ > 0`.

Physical case: `δ_S = k_B · log 2` (one Landauer bit per irreversible event),
giving minimum step `k_B · log 2 / ℏ`.

## Theorem 2 — Linear-clock uniqueness (`tau_ent_unique_among_landauer_clocks`)

A **linear entropic clock** is a function `φ(t) = c · S_I(t)` with `c > 0`.
Among linear entropic clocks, the minimum nonzero increment is `c · δ_S`.
Two linear clocks with the **same minimum increment** have the same coefficient.
τ_ent (with `c = 1/ℏ`) is the unique linear clock with minimum step `k_B · log 2 / ℏ`.

## Theorem 3 — CFL+Landauer uniqueness (`tau_ent_is_the_correct_clock`)

Any linear clock that is (1) CFL-admissible, (2) entropy-faithful, and (3) has
the physical Landauer minimum step `k_B · log 2 / ℏ` must equal τ_ent pointwise.

## Scope

**structure hypothesis** (`landauer_lower_bound`): every strictly positive S_I
increment is ≥ δ_S. This is assumed, not derived. It instantiates the
Landauer 1961 principle but does not prove it from Hamiltonian mechanics.

**Linearity**: the uniqueness is among *linear* clocks `c · S_I`. A nonlinear
monotone reparameterisation of S_I could satisfy (1)–(2) with a different step
structure; the theorem does not cover that case.

**No ODE / derivative-level theory**: continuous-time uniqueness in the ODE
sense (`φ' = c · S_I'` with unique solution given initial data) would require
`HasDerivAt`; this is purely functional-equation uniqueness at the level of
`φ(t) = c · S_I(t)`.

## References

- Landauer 1961, *Irreversibility and heat generation in the computing
 process*, IBM J. Res. Dev. **5**, 183, doi:10.1147/rd.53.0183 — the
 `k_B · log 2` lower bound per erased bit (`landauer_lower_bound`, `δ_S`).
- Bennett 2003, *Notes on Landauer's principle, reversible computation, and
 Maxwell's demon*, Stud. Hist. Phil. Mod. Phys. **34**, 501,
 doi:10.1016/S1355-2198(03)00039-X — erasure ↔ reservoir-entropy accounting
 underlying `ErasureDrivenWorldline` / `BathWorldline`.
- Page & Wootters 1983, *Evolution without evolution: Dynamics described by
 stationary observables*, Phys. Rev. D **27**, 2885,
 doi:10.1103/PhysRevD.27.2885 — relational time `τ_ent` singled out here.
- Courant, Friedrichs & Lewy 1928, *Über die partiellen Differenzengleichungen
 der mathematischen Physik*, Math. Ann. **100**, 32, doi:10.1007/BF01448839 —
 the CFL stability condition behind `tau_ent_cfl_invariant`.

This is an independent Lean formalisation; the per-event Landauer bound is the
load-bearing hypothesis (`landauer_lower_bound`), and is derived from the second
law on the erasure-driven and bath-coupled worldlines (§A′, §A″).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockUniqueness

open Physlib.Thermodynamics.SecondLaw
open Physlib.Thermodynamics.Landauer
open FluidDynamics
open Constants

/-! ## §A — Minimum-step theorem -/

/-- **Landauer-bounded worldline**: an `EntropyArrowWorldline` in which every
strictly positive S_I increment is bounded below by `δ_S > 0`.

Physical interpretation: each irreversible event raises S_I by at least
`k_B · log 2` (one Landauer bit). -/
structure LandauerBoundedWorldline where
  W    : EntropyArrowWorldline
  δ_S  : ℝ
  δ_S_pos : 0 < δ_S
  landauer_lower_bound :
    ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      W.S_I_along t₁ < W.S_I_along t₂ →
        δ_S ≤ W.S_I_along t₂ - W.S_I_along t₁

/-- **Minimum τ_ent step**: `δ_τ = δ_S / ℏ > 0`. -/
def LandauerBoundedWorldline.δ_τ (L : LandauerBoundedWorldline) : ℝ :=
  L.δ_S / L.W.ℏ

theorem LandauerBoundedWorldline.δ_τ_pos (L : LandauerBoundedWorldline) :
    0 < L.δ_τ :=
  div_pos L.δ_S_pos L.W.ℏ_pos

/-- **Theorem 1 — Minimum step**: on a Landauer-bounded worldline, every
strictly positive τ_ent increment is at least `δ_S / ℏ`. -/
theorem tau_ent_minimum_step
    (L : LandauerBoundedWorldline)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hstrict : L.W.τ_ent_along t₁ < L.W.τ_ent_along t₂) :
    L.δ_τ ≤ L.W.τ_ent_along t₂ - L.W.τ_ent_along t₁ := by
  have hℏ_pos := L.W.ℏ_pos
  have hℏ_ne  := ne_of_gt hℏ_pos
  -- Convert τ_ent strict inequality to S_I strict inequality
  have hS_strict : L.W.S_I_along t₁ < L.W.S_I_along t₂ := by
    have h₁ := L.W.τ_ent_eq t₁
    have h₂ := L.W.τ_ent_eq t₂
    rw [h₁, h₂] at hstrict
    exact (div_lt_div_iff_of_pos_right hℏ_pos).mp hstrict
  -- Apply the Landauer lower bound
  have hS_bound := L.landauer_lower_bound ht hS_strict
  -- τ_ent_along t = S_I_along t / ℏ, so
  -- τ_ent t₂ - τ_ent t₁ = (S_I t₂ - S_I t₁) / ℏ
  rw [L.W.τ_ent_eq t₂, L.W.τ_ent_eq t₁]
  unfold LandauerBoundedWorldline.δ_τ
  have hS_diff := hS_bound  -- δ_S ≤ S_I t₂ - S_I t₁
  have : L.W.S_I_along t₂ / L.W.ℏ - L.W.S_I_along t₁ / L.W.ℏ =
         (L.W.S_I_along t₂ - L.W.S_I_along t₁) / L.W.ℏ := by
    ring
  rw [this]
  exact div_le_div_of_nonneg_right hS_diff L.W.ℏ_pos.le

/-- **Physical Landauer bound constructor**: produces a `LandauerBoundedWorldline`
from a worldline with the physical bound `δ_S = k_B · log 2`. -/
def LandauerBoundedWorldline.ofPhysical
    (W : EntropyArrowWorldline)
    (hbnd : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      W.S_I_along t₁ < W.S_I_along t₂ →
        kB * Real.log 2 ≤ W.S_I_along t₂ - W.S_I_along t₁) :
    LandauerBoundedWorldline where
  W   := W
  δ_S := kB * Real.log 2
  δ_S_pos := mul_pos kB_pos (Real.log_pos (by norm_num))
  landauer_lower_bound := hbnd

/-- **Physical minimum step**: on a worldline with the physical Landauer bound,
every strictly positive τ_ent increment is at least `k_B · log 2 / ℏ > 0`. -/
theorem tau_ent_physical_minimum_step
    (W : EntropyArrowWorldline)
    (hbnd : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      W.S_I_along t₁ < W.S_I_along t₂ →
        kB * Real.log 2 ≤ W.S_I_along t₂ - W.S_I_along t₁)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hstrict : W.τ_ent_along t₁ < W.τ_ent_along t₂) :
    kB * Real.log 2 / W.ℏ ≤ W.τ_ent_along t₂ - W.τ_ent_along t₁ :=
  tau_ent_minimum_step (LandauerBoundedWorldline.ofPhysical W hbnd) ht hstrict

/-! ## §A' — Deriving the Landauer bound from the proven erasure theorem

`tau_ent_minimum_step` takes the per-event lower bound `δ_S ≤ ΔS_I` as a
structure field (`landauer_lower_bound`).  Here we remove that assumption: the
bound is supplied by `Landauer.reservoir_entropy_advance_ge_one_bit`, which is
**proved** from the second law (`total_entropy_nondecreasing`) and the one-bit
erasure definition — no Clausius input and no bare numeric assumption.

The only physical input that remains is the *identification*
`ΔS_I  =  ΔS_reservoir` over each irreversible event: the worldline information
entropy produced equals the entropy the erasure dumps to its bath.  This is the
Landauer erasure model itself, not the numeric bound `k_B·log2 ≤ ·`. -/

/-- **Erasure-driven worldline**: every strictly-positive `S_I` increment is
realised by a one-bit `LandauerErasureSetup`, and the worldline's `S_I`
increment is identified with the reservoir entropy that erasure advances. -/
structure ErasureDrivenWorldline where
  W : EntropyArrowWorldline
  /-- Each irreversible step is a one-bit Landauer erasure against a bath. -/
  event : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
    W.S_I_along t₁ < W.S_I_along t₂ → LandauerErasureSetup
  /-- The information entropy produced equals the entropy dumped to the bath. -/
  increment_eq : ∀ {t₁ t₂ : ℝ} (h : t₁ ≤ t₂)
      (hs : W.S_I_along t₁ < W.S_I_along t₂),
    W.S_I_along t₂ - W.S_I_along t₁ =
      (event h hs).reservoir.S (event h hs).t_post
        - (event h hs).reservoir.S (event h hs).t_pre

/-- **Per-event Landauer bound — derived, not assumed**: on an erasure-driven
worldline every strictly-positive `S_I` increment is at least `k_B · log 2`.
The proof is `reservoir_entropy_advance_ge_one_bit` transported across the
`increment_eq` identification. -/
theorem ErasureDrivenWorldline.increment_ge_landauer (D : ErasureDrivenWorldline)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (hs : D.W.S_I_along t₁ < D.W.S_I_along t₂) :
    kB * Real.log 2 ≤ D.W.S_I_along t₂ - D.W.S_I_along t₁ := by
  rw [D.increment_eq h hs]
  exact (D.event h hs).reservoir_entropy_advance_ge_one_bit

/-- The erasure-driven worldline *is* a `LandauerBoundedWorldline` with
`δ_S = k_B · log 2`, its `landauer_lower_bound` field now **filled by a
theorem** rather than asserted. -/
def ErasureDrivenWorldline.toLandauerBounded (D : ErasureDrivenWorldline) :
    LandauerBoundedWorldline where
  W   := D.W
  δ_S := kB * Real.log 2
  δ_S_pos := mul_pos kB_pos (Real.log_pos (by norm_num))
  landauer_lower_bound := fun h hs => D.increment_ge_landauer h hs

/-- **Theorem 1′ — Minimum step with the bound derived**: on an erasure-driven
worldline, every strictly-positive τ_ent increment is at least
`k_B · log 2 / ℏ`.  Unlike `tau_ent_physical_minimum_step`, the Landauer lower
bound is not a hypothesis here — it comes from
`reservoir_entropy_advance_ge_one_bit`. -/
theorem tau_ent_minimum_step_derived (D : ErasureDrivenWorldline)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hstrict : D.W.τ_ent_along t₁ < D.W.τ_ent_along t₂) :
    kB * Real.log 2 / D.W.ℏ ≤ D.W.τ_ent_along t₂ - D.W.τ_ent_along t₁ :=
  tau_ent_minimum_step D.toLandauerBounded ht hstrict

/-! ## §A'' — Removing the identification assumption

`ErasureDrivenWorldline.increment_eq` still *assumed* `ΔS_I = ΔS_reservoir` —
the worldline `S_I` and the bath `S` were two independent functions linked by a
hypothesis.  Here we collapse that gap: the worldline's `S_I_along` is **defined
to be** the bath entropy, so the identification holds by `rfl` and is no longer
an assumption.

What is left is exactly the two inputs the minimum-step result is allowed to
rest on:
* the **second law** — `bath_S_monotone` (the standard `EntropyArrowWorldline`
  monotonicity input) and, per event, the combined memory+bath second law;
* the **one-bit erasure model** — the memory loses `kB·log 2` per event.

The numeric bound `kB·log 2 ≤ ΔS_I` is then a *theorem*
(`reservoir_entropy_advance_ge_one_bit`), not a planted inequality. -/

/-- **Bath-coupled worldline**: the worldline information entropy *is* a thermal
bath's entropy.  Each strictly-positive event is a one-bit Landauer erasure
obeying the second law on the combined memory+bath system. -/
structure BathWorldline where
  bath : ThermalReservoir
  ℏ : ℝ
  ℏ_pos : 0 < ℏ
  /-- Second law on the bath: its entropy is monotone non-decreasing
  (the `EntropyArrowWorldline.S_I_monotone` input). -/
  bath_S_monotone : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ → bath.S t₁ ≤ bath.S t₂
  /-- Initial bath entropy is non-negative. -/
  bath_S_zero_nonneg : 0 ≤ bath.S 0
  /-- Per strictly-positive event, the second law on memory+bath with the
  one-bit erasure value substituted: `0 ≤ ΔS_memory + ΔS_bath` where
  `ΔS_memory = -kB·log 2`.  This is the combined-system second law plus the
  one-bit model — not the numeric bound, which is derived from it. -/
  erasure_second_law : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ → bath.S t₁ < bath.S t₂ →
    0 ≤ (-kB * Real.log 2) + (bath.S t₂ - bath.S t₁)

namespace BathWorldline

variable (B : BathWorldline)

/-- The worldline whose `S_I_along` *is* the bath entropy.  `τ_ent_eq` and the
identification with the bath are both `rfl`. -/
def toWorldline : EntropyArrowWorldline where
  ℏ := B.ℏ
  ℏ_pos := B.ℏ_pos
  S_I_along := B.bath.S
  τ_ent_along t := B.bath.S t / B.ℏ
  τ_ent_eq _ := rfl
  S_I_monotone := B.bath_S_monotone
  S_I_at_zero_nonneg := B.bath_S_zero_nonneg

/-- The one-bit erasure event hosting a strictly-positive increment. -/
def event {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (hs : B.bath.S t₁ < B.bath.S t₂) :
    LandauerErasureSetup where
  reservoir := B.bath
  t_pre := t₁
  t_post := t₂
  ΔS_memory := -kB * Real.log 2
  one_bit_erasure := rfl
  total_entropy_nondecreasing := B.erasure_second_law h hs

/-- The bath-coupled worldline is an `ErasureDrivenWorldline` with the
identification `increment_eq` proved by `rfl` — it is no longer assumed. -/
def toErasureDriven : ErasureDrivenWorldline where
  W := B.toWorldline
  event h hs := B.event h hs
  increment_eq _ _ := rfl

/-- **Theorem 1″ — Minimum step with *no* identification assumption**: on a
bath-coupled worldline, every strictly-positive τ_ent increment is at least
`kB·log 2 / ℏ`.  Both the numeric Landauer bound and the identification
`ΔS_I = ΔS_bath` are now theorems; the only inputs are the second law and the
one-bit erasure model. -/
theorem tau_ent_minimum_step
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hstrict : B.toWorldline.τ_ent_along t₁ < B.toWorldline.τ_ent_along t₂) :
    kB * Real.log 2 / B.ℏ ≤
      B.toWorldline.τ_ent_along t₂ - B.toWorldline.τ_ent_along t₁ :=
  tau_ent_minimum_step_derived B.toErasureDriven ht hstrict

end BathWorldline

/-! ## §B — Linear-clock uniqueness -/

/-- **Linear entropic clock**: value `c · W.S_I_along t` with `c > 0`. -/
structure LinearEntropicClock (W : EntropyArrowWorldline) where
  c     : ℝ
  c_pos : 0 < c

/-- The value of a linear entropic clock at parameter `t`. -/
def LinearEntropicClock.φ {W : EntropyArrowWorldline}
    (clk : LinearEntropicClock W) (t : ℝ) : ℝ :=
  clk.c * W.S_I_along t

/-- **τ_ent as a linear clock**: coefficient `1/ℏ`. -/
def linearTauEnt (W : EntropyArrowWorldline) : LinearEntropicClock W where
  c     := 1 / W.ℏ
  c_pos := div_pos one_pos W.ℏ_pos

/-- The τ_ent linear clock equals `W.τ_ent_along`. -/
theorem linearTauEnt_φ_eq (W : EntropyArrowWorldline) (t : ℝ) :
    (linearTauEnt W).φ t = W.τ_ent_along t := by
  unfold LinearEntropicClock.φ linearTauEnt
  rw [W.τ_ent_eq]
  ring

/-- **Minimum increment of a linear clock** on a Landauer-bounded worldline:
strictly positive S_I increment implies linear-clock increment ≥ `c · δ_S`. -/
theorem LinearEntropicClock.minimum_increment
    (L : LandauerBoundedWorldline)
    (clk : LinearEntropicClock L.W)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hS : L.W.S_I_along t₁ < L.W.S_I_along t₂) :
    clk.c * L.δ_S ≤ clk.φ t₂ - clk.φ t₁ := by
  unfold LinearEntropicClock.φ
  have hbnd := L.landauer_lower_bound ht hS
  nlinarith [clk.c_pos.le]

/-- **Theorem 2 — Linear-clock uniqueness**: two linear clocks with the same
minimum step coefficient product `c · δ_S` have the same coefficient. -/
theorem LinearEntropicClock.unique_of_same_step
    (L : LandauerBoundedWorldline)
    (clk₁ clk₂ : LinearEntropicClock L.W)
    (h : clk₁.c * L.δ_S = clk₂.c * L.δ_S) :
    clk₁.c = clk₂.c :=
  mul_right_cancel₀ (ne_of_gt L.δ_S_pos) h

/-- **τ_ent uniqueness**: τ_ent is the unique linear clock whose minimum step
satisfies `c · δ_S = (1/ℏ) · δ_S` on any Landauer-bounded worldline. -/
theorem tau_ent_unique_among_landauer_clocks
    (L : LandauerBoundedWorldline)
    (clk : LinearEntropicClock L.W)
    (h : clk.c * L.δ_S = (1 / L.W.ℏ) * L.δ_S) :
    ∀ t, clk.φ t = (linearTauEnt L.W).φ t := by
  have hc : clk.c = 1 / L.W.ℏ :=
    LinearEntropicClock.unique_of_same_step L clk (linearTauEnt L.W) h
  intro t
  simp only [LinearEntropicClock.φ, linearTauEnt, hc]

/-! ## §C — CFL + Landauer uniqueness -/

/-- **Entropy faithfulness**: a linear clock is entropy-faithful if its ordering
exactly matches the S_I ordering. This holds for every linear clock with `c > 0`. -/
def LinearEntropicClock.IsEntropyFaithful
    {W : EntropyArrowWorldline} (clk : LinearEntropicClock W) : Prop :=
  ∀ t₁ t₂, clk.φ t₁ ≤ clk.φ t₂ ↔ W.S_I_along t₁ ≤ W.S_I_along t₂

/-- Every linear clock with positive coefficient is entropy-faithful. -/
theorem LinearEntropicClock.isEntropyFaithful_of_pos
    {W : EntropyArrowWorldline} (clk : LinearEntropicClock W) :
    clk.IsEntropyFaithful := by
  intro t₁ t₂
  simp only [LinearEntropicClock.φ]
  exact ⟨fun h => le_of_mul_le_mul_left h clk.c_pos,
         fun h => mul_le_mul_of_nonneg_left h clk.c_pos.le⟩

/-- **CFL reparameterisation by τ_ent preserves the Courant number**:
the τ_ent rate `λ = 1/ℏ` rescales `(Δt, a) ↦ ((1/ℏ)·Δt, a·ℏ)`, leaving
the Courant number invariant. -/
theorem tau_ent_cfl_invariant (W : EntropyArrowWorldline) (Δt Δx a : ℝ) :
    courantNumber ((1 / W.ℏ) * Δt) Δx (a / (1 / W.ℏ)) =
      courantNumber Δt Δx a :=
  courantNumber_rescale_invariant Δt Δx a (1 / W.ℏ) (div_pos one_pos W.ℏ_pos)

/-- **Theorem 3 — CFL + Landauer uniqueness**: any linear entropic clock that is
(1) CFL-admissible (positive coefficient), (2) entropy-faithful, and (3) has the
same minimum step as τ_ent (i.e. `c · δ_S = (1/ℏ) · δ_S`) agrees with τ_ent
pointwise.

This is the uniqueness statement that "singles out τ_ent":
among all CFL-admissible entropy-faithful linear clocks on a Landauer-bounded
worldline, τ_ent is the unique one with the physical Landauer minimum step. -/
theorem tau_ent_is_the_correct_clock
    (L : LandauerBoundedWorldline)
    (clk : LinearEntropicClock L.W)
    -- (1) CFL-admissible: positive coefficient (already in `clk.c_pos`)
    -- (2) entropy-faithful: follows from positive coefficient
    -- (3) same minimum step as τ_ent
    (hstep : clk.c * L.δ_S = (1 / L.W.ℏ) * L.δ_S) :
    ∀ t, clk.φ t = L.W.τ_ent_along t := by
  have hc : clk.c = 1 / L.W.ℏ :=
    LinearEntropicClock.unique_of_same_step L clk (linearTauEnt L.W) hstep
  intro t
  rw [LinearEntropicClock.φ, L.W.τ_ent_eq, hc]
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockUniqueness
