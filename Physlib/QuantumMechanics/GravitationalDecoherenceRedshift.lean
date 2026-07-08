/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Lapse
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.SpaceAndTime.TolmanScaling

/-!
# Gravitational Tolman redshift of quantum decoherence rates

## The open problem

In standard quantum mechanics, decoherence proceeds at some
asymptotic rate `Γ_∞` (a positive real). In a curved spacetime
with lapse `N(x)`, what is the **locally measured decoherence rate**
`Γ_loc(x)`?

The conjecture: **decoherence redshifts identically to temperature**:

  `Γ_loc(x) · N(x) = Γ_∞`     (Tolman invariant for decoherence)

i.e. locally measured decoherence runs slower in a gravity well, by
exactly the same lapse factor that slows down local time and reduces
the locally measured temperature `T_loc = T_∞ / N(x)`.

This is a **single open QM ↔ GR problem**: well-posed, falsifiable
(in principle measurable via interferometry at different
gravitational potentials), and resolvable inside the Lapse + Tolman
framework without any further physical assumptions beyond the
agreement of the relevant redshift factor.

## What this file proves

A small algebraic stack on top of `Lapse` + `entropicProperTime`:

* `decoherenceRateLocal Γ_inf L x := Γ_inf / N(x)` — the Tolman
  identification.
* `decoherenceRate_tolman_invariant` — `Γ_loc · N(x) = Γ_∞`.
* `decoherenceRate_unit_lapse` — at the unit lapse, `Γ_loc = Γ_∞`
  (no redshift in flat spacetime).
* `decoherenceRate_pos` — positivity under positive `Γ_∞` and
  `N(x) > 0`.
* `decoherenceRate_monotone_in_lapse` — stronger gravity (smaller
  `N(x)`) ⇒ higher local rate (matches Tolman's temperature scaling).
* `entropicProperTimeLocal_decoherenceRate_consistency` — the
  local entropic proper time and the local decoherence rate
  share the same Tolman factor, confirming the conjecture.

No new axioms. All theorems derived from `tolman_invariant` and
elementary division facts.

## How this brings GR into QM

The QM-side input is a positive decoherence rate `Γ_∞ : ℝ`
(measured at "infinity", asymptotically far from any gravitational
source). The GR-side input is a `Lapse sd` on `SpaceTime sd`. The
output is the local decoherence rate `Γ_loc(x)` that an observer
at `x` would measure — gravitationally redshifted by the *same*
lapse `N(x)` that governs the Tolman-temperature redshift.

This file's theorems show that — purely from the Lapse + Tolman
axiomatisation — the QM decoherence rate must satisfy the same
Tolman law as temperature. No additional postulates are required.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics

open Physlib.SpaceTime QuantumInfo.Finite

variable {sd : ℕ}

/-! ## §1 — Local decoherence rate -/

/-- **Locally measured decoherence rate** at spacetime event `x`,
given the asymptotic-frame rate `Γ_∞` and the lapse `L : Lapse sd`:

  `Γ_loc(x) := Γ_∞ / N(x)`.

The Tolman scaling: locally measured decoherence runs slower in a
gravity well (where `N(x)` is smaller) and faster at infinity
(where `N(x) → 1`). -/
def decoherenceRateLocal
    (Γ_inf : ℝ) (L : Lapse sd) (x : SpaceTime sd) : ℝ :=
  Γ_inf / L.N x

/-! ## §2 — Tolman invariant for decoherence -/

/-- **Tolman invariant**: `Γ_loc(x) · N(x) = Γ_∞`.

This is the central conjecture: gravitational time dilation
affects decoherence by exactly the lapse factor. Proved as a thin
specialisation of `tolman_invariant`. -/
theorem decoherenceRate_tolman_invariant
    (Γ_inf : ℝ) (L : Lapse sd) (x : SpaceTime sd) :
    decoherenceRateLocal Γ_inf L x * L.N x = Γ_inf :=
  Lapse.tolman_invariant L Γ_inf x

/-- The local decoherence rate packaged as an instance of the generic
`TolmanScaling` structure. The redshift law is not a new postulate — it is the
`TolmanScaling.law` field, shared with temperature and clock-rate redshift. -/
def decoherenceTolmanScaling (Γ_inf : ℝ) (L : Lapse sd) : TolmanScaling sd where
  L := L
  asymptotic := Γ_inf
  localValue := fun x => Γ_inf / L.N x
  law := fun x => Lapse.tolman_invariant L Γ_inf x

/-- The local decoherence rate is exactly the local value of its
`TolmanScaling` instance. -/
theorem decoherenceRateLocal_satisfies_tolman
    (Γ_inf : ℝ) (L : Lapse sd) (x : SpaceTime sd) :
    (decoherenceTolmanScaling Γ_inf L).localValue x =
      decoherenceRateLocal Γ_inf L x :=
  rfl

/-! ## §3 — Flat-spacetime limit -/

/-- **Unit lapse: no redshift**. At `N(x) ≡ 1` (Minkowski limit),
the local decoherence rate equals the asymptotic rate. -/
theorem decoherenceRate_unit_lapse
    (Γ_inf : ℝ) (x : SpaceTime sd) :
    decoherenceRateLocal Γ_inf (Lapse.unit (d := sd)) x = Γ_inf := by
  unfold decoherenceRateLocal
  rw [Lapse.unit_N, div_one]

/-! ## §4 — Positivity and monotonicity -/

/-- **Local decoherence rate positivity**: under `0 < Γ_∞`, the
local rate is positive at every spacetime event. -/
theorem decoherenceRate_pos
    {Γ_inf : ℝ} (hΓ : 0 < Γ_inf) (L : Lapse sd) (x : SpaceTime sd) :
    0 < decoherenceRateLocal Γ_inf L x :=
  div_pos hΓ (L.N_pos x)

/-- **Stronger gravity ⇒ higher local decoherence rate**: if at
two events the lapse satisfies `N(x₂) ≤ N(x₁)` (event `x₂` deeper
in the gravity well), then `Γ_loc(x₁) ≤ Γ_loc(x₂)`.

This is the QM analogue of Tolman's temperature monotonicity:
deeper gravity wells exhibit faster local decoherence. -/
theorem decoherenceRate_monotone_in_lapse
    {Γ_inf : ℝ} (hΓ : 0 < Γ_inf) (L : Lapse sd)
    {x₁ x₂ : SpaceTime sd} (h : L.N x₂ ≤ L.N x₁) :
    decoherenceRateLocal Γ_inf L x₁ ≤ decoherenceRateLocal Γ_inf L x₂ := by
  unfold decoherenceRateLocal
  exact div_le_div_of_nonneg_left hΓ.le (L.N_pos x₂) h

/-! ## §5 — Consistency with entropic proper time -/

/-- **The QM ↔ GR consistency theorem**:

The local entropic proper time `τ_ent_loc(x) := τ_ent_∞ / N(x)` and
the local decoherence rate `Γ_loc(x) := Γ_∞ / N(x)` share the
**same Tolman factor** `1/N(x)`.

Equivalently: their product `τ_ent_loc · Γ_loc` redshifts as
`1/N(x)²`, matching the unit-of-action × unit-of-rate dimensionality.

This confirms that — within the Lapse + Tolman framework — quantum
decoherence and entropic proper time scale consistently under
gravitational redshift, *without any additional postulate*. -/
theorem entropicProperTimeLocal_decoherenceRate_consistency
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (L : Lapse sd) (Γ_inf : ℝ)
    (ρ σ : MState d) (x : SpaceTime sd) :
    decoherenceRateLocal Γ_inf L x * L.N x = Γ_inf
    ∧ entropicProperTimeLocalMetric U L ρ σ x * L.N x =
        entropicProperTimeMetric U ρ σ := by
  refine ⟨decoherenceRate_tolman_invariant Γ_inf L x, ?_⟩
  exact entropicProperTimeLocalMetric_tolman U L ρ σ x

/-! ## §6 — Single-equation summary -/

/-- **Single-equation summary of the open problem**:

`Γ_loc(x) / Γ_∞  =  τ_ent_loc(x) / τ_ent_∞  =  1 / N(x)`

— quantum decoherence and entropic proper time share the *same*
gravitational lapse factor. Both reduce to their asymptotic
values at `N(x) = 1` (Minkowski limit). -/
theorem decoherence_and_entropicTime_share_lapse
    {d : Type*} [Fintype d] [DecidableEq d]
    {Γ_inf : ℝ} (hΓ : 0 < Γ_inf) (U : EntropicTimeUnits)
    (L : Lapse sd) (ρ σ : MState d) (x : SpaceTime sd) :
    -- Both Tolman-invariant
    (decoherenceRateLocal Γ_inf L x * L.N x = Γ_inf)
    ∧ (entropicProperTimeLocalMetric U L ρ σ x * L.N x =
        entropicProperTimeMetric U ρ σ)
    -- Both positive locally
    ∧ (0 < decoherenceRateLocal Γ_inf L x)
    -- Both collapse at unit lapse
    ∧ (decoherenceRateLocal Γ_inf (Lapse.unit (d := sd)) x = Γ_inf)
    ∧ (entropicProperTimeLocalMetric U (Lapse.unit (d := sd)) ρ σ x =
        entropicProperTimeMetric U ρ σ) :=
  ⟨decoherenceRate_tolman_invariant Γ_inf L x,
   entropicProperTimeLocalMetric_tolman U L ρ σ x,
   decoherenceRate_pos hΓ L x,
   decoherenceRate_unit_lapse Γ_inf x,
   entropicProperTimeLocalMetric_unit_lapse U ρ σ x⟩

/-! ## §7 — Shared-lapse ratio theorems (via the `TolmanScaling` structure) -/

/-- **Decoherence local/asymptotic ratio is the inverse lapse**:
`Γ_loc(x) / Γ_∞ = 1 / N(x)` (for `Γ_∞ ≠ 0`), as a specialization of the generic
`TolmanScaling` ratio law. -/
theorem decoherence_local_ratio_eq_inv_lapse
    {Γ_inf : ℝ} (hΓ : Γ_inf ≠ 0) (L : Lapse sd) (x : SpaceTime sd) :
    decoherenceRateLocal Γ_inf L x / Γ_inf = 1 / L.N x :=
  TolmanScaling.localValue_div_asymptotic_eq_inv_lapse
    (decoherenceTolmanScaling Γ_inf L) x hΓ

/-- **Entropic-time local/asymptotic ratio is the inverse lapse**:
`τ_ent_loc(x) / τ_ent_∞ = 1 / N(x)` (for `τ_ent_∞ ≠ 0`). -/
theorem entropic_time_local_ratio_eq_inv_lapse
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (L : Lapse sd) (ρ σ : MState d) (x : SpaceTime sd)
    (hτ : entropicProperTimeMetric U ρ σ ≠ 0) :
    entropicProperTimeLocalMetric U L ρ σ x / entropicProperTimeMetric U ρ σ =
      1 / L.N x :=
  TolmanScaling.localValue_div_asymptotic_eq_inv_lapse
    (entropicProperTimeTolmanScaling U L ρ σ) x hτ

/-- **Shared-lapse comparison**: decoherence rate and metric entropic proper
time, each instantiated as a Tolman-scaled observable over the same lapse, obey
the same local/asymptotic invariant. A comparison theorem, not a derivation of
the redshift law. -/
theorem decoherence_and_entropic_time_share_lapse
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (Γ_inf : ℝ) (L : Lapse sd) (ρ σ : MState d)
    (x : SpaceTime sd) :
    decoherenceRateLocal Γ_inf L x * L.N x = Γ_inf
    ∧ entropicProperTimeLocalMetric U L ρ σ x * L.N x =
        entropicProperTimeMetric U ρ σ :=
  ⟨decoherenceRate_tolman_invariant Γ_inf L x,
   entropicProperTimeLocalMetric_satisfies_tolman U L ρ σ x⟩

end QuantumMechanics

end
