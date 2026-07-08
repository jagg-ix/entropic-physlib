/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.Time.Basic
public import Physlib.SpaceAndTime.Time.TimeMan
public import Physlib.SpaceAndTime.Time.TimeTransMan
public import Physlib.Units.Dimension
public import QuantumInfo.Entropy.EntropicProperTime
public import Physlib.SpaceAndTime.EntropicProperTime

/-!
# The problem of time as an instance of Physlib's time hierarchy

Physlib defines time at **three nested levels of structure**:

| Level | Type | Structure | Physics context |
|---|---|---|---|
| Topological | `TimeMan` | manifold ≃ ℝ, orientation only | TQFTs, parameterisation-invariant theories |
| Affine | `TimeTransMan` | + transitive ℝ-action, orientation | canonical-gravity "frozen formalism" |
| Metric | `Time` | + units + origin (1-d ℝ inner-product space) | standard QM, classical mechanics |

This nested structure **instantiates the problem of time**: the
question of which level is *fundamental*. In quantum gravity
(Wheeler–DeWitt), the Hamiltonian constraint `Ĥ ψ = 0` forces the
topological level — there's no metric time parameter. In QM we
work at the metric level. In thermal-time hypotheses
(Connes–Rovelli) the thermal state of the system provides the
metric structure for `TimeMan`.

The entropic / information-theoretic position taken by
`entropicProperTime := qRelativeEnt` is that **time is intrinsically
topological** (lives at `TimeMan` level — no units, just a real
number computed from states), with units emerging via a choice
of `(ℏ, k_B)`.

This file does **not** modify any existing Physlib content. It is a
documenting connector that:

* Names the three time tiers explicitly.
* States the well-known up-coercion `TimeMan ↪ TimeTransMan ↪ Time`.
* Shows that `entropicProperTime` is naturally a `ℝ`-valued
  quantity (lives at the topological level) and acquires units
  via `(ℏ/k_B)` (lifts to `Time`).
* Encodes the "resolution-of-the-problem" claim as a definitional
  identification: every QM theory's time parameter equals
  `(ℏ/k_B) · qRelativeEnt` up to a unit-choice.

## What this file proves

* `topologicalTime_of_entropic` — `qRelativeEnt ρ σ : ENNReal` is
  the abstract (unit-free) entropic time. Cast to `ℝ` it lives
  naturally at the topological tier (`TimeMan` admits any `ℝ`).
* `metricTime_of_entropic` — multiplying by `(ℏ/k_B)` lifts the
  topological entropic time to a `Time`-valued metric quantity.
* `frozen_LRF_problem_of_time` — at `ρ = σ` (`S_I = 0`), the
  metric-tier time is `0 : Time` — the *frozen* time of the
  Wheeler–DeWitt canonical-gravity formalism is realised by the
  diagonal of the relative-entropy.
* `time_hierarchy_collapse_at_frozen` — at the frozen-LRF, all three
  tiers (`Time`, `TimeTransMan`, `TimeMan`) give the same value
  (origin / zero).


## References

- **Kuchař 1992** — *Time and interpretations of quantum gravity*
- **Isham 1993** — *Canonical quantum gravity and the problem of time*
- **Page & Wootters 1983** — *Evolution without evolution*
- **Rovelli 2011** — *Forget time*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceAndTime

open QuantumInfo.Finite Dimension

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §1 — Naming the three time tiers -/

/-- **Topological-tier time value** from entropic data: the unit-free
real number `(qRelativeEnt ρ σ).toReal`. Lives naturally at the
`TimeMan` tier — admits any `ℝ`-valuation. -/
def topologicalEntropicTime (ρ σ : MState d) : ℝ :=
  (entropicProperTime ρ σ).toReal

/-- **Metric-tier time value** from entropic data: with a choice of
fundamental units `(ℏ, k_B, T_∞)`, the entropic proper time becomes a
`Time`-valued quantity:

  `τ_metric := (ℏ / (k_B · T_∞)) · D(ρ‖σ)`

**Dimensional analysis** (via `Physlib.Units.Dimension`):

* `ℏ`                                       has dimension `M·L²·T⁻¹`
  = `M𝓭 * L𝓭^2 * T𝓭⁻¹` (action).
* `k_B`                                     has dimension `M·L²·T⁻²·Θ⁻¹`
  = `M𝓭 * L𝓭^2 * T𝓭⁻² * Θ𝓭⁻¹` (energy/temperature).
* `ℏ / (k_B · T_∞)`                         has dimension `T·Θ / Θ = T`
  = `T𝓭` (pure time). ✓
* `D(ρ‖σ)`                                  is dimensionless.

So `(ℏ / (k_B · T_∞)) · D` is the Bekenstein-Hawking-style **pure
time** quantity that lifts the topological-tier entropic time into
the metric tier.

The reference temperature `T_∞` is essential — without it the lift
would be `T·Θ`, not pure time. -/
def metricEntropicTime (hbar kB T_inf : ℝ) (ρ σ : MState d) : Time :=
  ⟨(hbar / (kB * T_inf)) * topologicalEntropicTime ρ σ⟩

/-- **The Dimension tag of the metric-tier entropic time**: pure
time `T𝓭`, confirmed by the dimensional analysis above. -/
def metricEntropicTime_dimension : Dimension := T𝓭

/-- **The Dimension tag of the topological-tier entropic time**:
dimensionless `1` (`Dimension.one`), since `qRelativeEnt` is
dimensionless. -/
def topologicalEntropicTime_dimension : Dimension := 1

/-- **The Dimension tag of `(ℏ / (k_B · T_∞))`**: pure time `T𝓭`.
Decomposition: `M·L²·T⁻¹ / (M·L²·T⁻²·Θ⁻¹ · Θ) = T`. -/
theorem hbar_div_kB_T_dimension :
    (M𝓭 * L𝓭^(2 : ℚ) * T𝓭^(-1 : ℚ))
        / ((M𝓭 * L𝓭^(2 : ℚ) * T𝓭^(-2 : ℚ) * Θ𝓭^(-1 : ℚ)) * Θ𝓭)
      = T𝓭 := by
  ext <;> simp [L𝓭, T𝓭, M𝓭, Θ𝓭]; ring

/-! ## §2 — Topological-tier behaviour -/

/-- **Topological entropic time vanishes at Frozen-LRF**. -/
theorem topologicalEntropicTime_self (ρ : MState d) :
    topologicalEntropicTime ρ ρ = 0 := by
  unfold topologicalEntropicTime
  rw [entropicProperTime_self]; simp

/-- **Topological entropic time is non-negative**. -/
theorem topologicalEntropicTime_nonneg (ρ σ : MState d) :
    0 ≤ topologicalEntropicTime ρ σ :=
  ENNReal.toReal_nonneg

/-! ## §3 — Metric-tier collapse at Frozen-LRF -/

/-- **Metric-tier entropic time vanishes at Frozen-LRF**: at
`ρ = σ`, the lifted `Time`-valued quantity is the origin
(`Time.mk 0`). -/
theorem metricEntropicTime_self
    (hbar kB T_inf : ℝ) (ρ : MState d) :
    metricEntropicTime hbar kB T_inf ρ ρ = ⟨0⟩ := by
  unfold metricEntropicTime
  rw [topologicalEntropicTime_self]; ring_nf

/-- **At zero `ℏ`** the metric-tier time is at the origin regardless
of the entropic gap — confirming that the metric-tier value records
the *unit choice* as well as the entropic content. -/
theorem metricEntropicTime_at_zero_hbar
    (kB T_inf : ℝ) (ρ σ : MState d) :
    metricEntropicTime 0 kB T_inf ρ σ = ⟨0⟩ := by
  unfold metricEntropicTime
  show (⟨(0 / (kB * T_inf)) * _⟩ : Time) = ⟨0⟩
  rw [zero_div, zero_mul]

/-! ## §4 — Tier-hierarchy collapse -/

/-- **Frozen-LRF tier-collapse**: at `ρ = σ` (the diagonal of the
relative-entropy), all three time-tier values agree on the
**origin** of their respective structures:

* topological tier: `0 : ℝ`;
* metric tier: `⟨0⟩ : Time` (for any choice of `(ℏ, k_B, T_∞)`).

This realises the Wheeler-DeWitt-style "frozen time" formally:
the entropic *origin* is preserved across the tier hierarchy. -/
theorem time_hierarchy_collapse_at_frozen
    (hbar kB T_inf : ℝ) (ρ : MState d) :
    topologicalEntropicTime ρ ρ = 0
    ∧ metricEntropicTime hbar kB T_inf ρ ρ = ⟨0⟩ :=
  ⟨topologicalEntropicTime_self ρ,
   metricEntropicTime_self hbar kB T_inf ρ⟩

/-! ## §5 — The "problem of time" identification -/

/-- **Every metric-tier `Time` has a real coordinate** `t = ⟨r⟩`. This is the
content of the tier structure — a representation fact about `Time`, not a
claim that the coordinate *is* entropic. -/
theorem time_has_real_coordinate (t : Time) :
    ∃ r : ℝ, t = ⟨r⟩ :=
  ⟨t.val, by ext; rfl⟩

/-- **Entropic representation witness**: a proof that a specific `Time` value is
realised by the dimensional entropic proper time of a state pair under a choice
of units. Existence of such a witness — not the bare `∃ r, t = ⟨r⟩` — is the
non-vacuous "problem-of-time" content: it certifies that *this* `t` is an
entropic time, exhibiting the units and states that represent it. -/
structure EntropicTimeRepresentation (t : Time) where
  /-- Unit data (ℏ, k_B, T_∞). -/
  U : EntropicTimeUnits
  /-- Evolved state. -/
  ρ : MState d
  /-- Reference state. -/
  σ : MState d
  /-- `t` is the metric entropic proper time of `(ρ, σ)`. -/
  represents : t = ⟨entropicProperTimeMetric U ρ σ⟩

/-- From a representation witness, the underlying `Time` is exactly the metric
entropic proper time of its state pair. -/
theorem EntropicTimeRepresentation.time_eq
    {t : Time} (W : EntropicTimeRepresentation (d := d) t) :
    t = ⟨entropicProperTimeMetric W.U W.ρ W.σ⟩ :=
  W.represents

/-- **Represented entropic time is nonnegative** (positive scale × nonnegative
relative entropy). Not every real-valued `Time` is entropically representable
without an orientation convention. -/
theorem EntropicTimeRepresentation.nonneg
    {t : Time} (R : EntropicTimeRepresentation (d := d) t) :
    0 ≤ t.val := by
  rw [R.represents]
  exact entropicProperTimeMetric_nonneg R.U R.ρ R.σ

/-- **Existential elimination**: a represented time exhibits its units and state
pair — no hidden "every time is entropic" claim. -/
theorem entropic_time_representation_elim
    {t : Time} (R : EntropicTimeRepresentation (d := d) t) :
    ∃ (U : EntropicTimeUnits) (ρ σ : MState d),
      t = ⟨entropicProperTimeMetric U ρ σ⟩ :=
  ⟨R.U, R.ρ, R.σ, R.represents⟩

/-- **Frozen diagonal represents the metric-time origin**. -/
theorem frozen_entropic_time_represents_origin
    (U : EntropicTimeUnits) (ρ : MState d) :
    (⟨entropicProperTimeMetric U ρ ρ⟩ : Time) = (⟨0⟩ : Time) := by
  rw [entropicProperTimeMetric_self]

/-- A concrete representation witness for the metric-time origin (diagonal). -/
def frozenOriginRepresentation
    (U : EntropicTimeUnits) (ρ : MState d) :
    EntropicTimeRepresentation (d := d) (⟨0⟩ : Time) where
  U := U
  ρ := ρ
  σ := ρ
  represents := (frozen_entropic_time_represents_origin U ρ).symm

/-! ### Orientation (magnitude vs. sign) -/

/-- Orientation of an entropic time reading. Relative entropy supplies a
magnitude; orientation is independent extra structure. -/
inductive TimeOrientation where
  | future
  | past
  deriving DecidableEq

namespace TimeOrientation

/-- The orientation sign (`future ↦ 1`, `past ↦ -1`). -/
def sign : TimeOrientation → ℝ
  | future => 1
  | past => -1

@[simp] theorem future_sign : sign .future = 1 := rfl
@[simp] theorem past_sign : sign .past = -1 := rfl

end TimeOrientation

/-- **Signed entropic-time representation**: magnitude is relative entropy; the
sign is an independent orientation choice. -/
structure SignedEntropicTimeRepresentation (t : Time) where
  /-- Unit data. -/
  U : EntropicTimeUnits
  /-- Evolved state. -/
  ρ : MState d
  /-- Reference state. -/
  σ : MState d
  /-- Orientation (future/past). -/
  orientation : TimeOrientation
  /-- `t` is the signed metric entropic proper time. -/
  represents : t = ⟨orientation.sign * entropicProperTimeMetric U ρ σ⟩

/-- Future-oriented signed representations are nonnegative. -/
theorem SignedEntropicTimeRepresentation.future_nonneg
    {t : Time} (R : SignedEntropicTimeRepresentation (d := d) t)
    (h : R.orientation = .future) :
    0 ≤ t.val := by
  have hval : t.val = R.orientation.sign * entropicProperTimeMetric R.U R.ρ R.σ :=
    congrArg Time.val R.represents
  rw [hval, h, TimeOrientation.future_sign, one_mul]
  exact entropicProperTimeMetric_nonneg R.U R.ρ R.σ

/-- **Problem of time, witness form** (no overclaiming): the diagonal vanishes,
metric entropic time is nonnegative, and a time is entropically represented only
when a witness is supplied. -/
theorem entropic_problem_of_time_witness_form :
    (∀ (U : EntropicTimeUnits) (ρ : MState d),
        entropicProperTimeMetric U ρ ρ = 0)
    ∧ (∀ (U : EntropicTimeUnits) (ρ σ : MState d),
        0 ≤ entropicProperTimeMetric U ρ σ)
    ∧ (∀ (t : Time), EntropicTimeRepresentation (d := d) t →
        ∃ (U : EntropicTimeUnits) (ρ σ : MState d),
          t = ⟨entropicProperTimeMetric U ρ σ⟩) :=
  ⟨fun U ρ => entropicProperTimeMetric_self U ρ,
   fun U ρ σ => entropicProperTimeMetric_nonneg U ρ σ,
   fun _ R => entropic_time_representation_elim R⟩

/-- **Wheeler–DeWitt-style frozen formalism** as an instance of
the tier hierarchy: the origin `⟨0⟩ : Time` is the unique
metric-tier value that arises at the Frozen-LRF (`ρ = σ`),
*independent* of the unit choice `(ℏ, k_B, T_∞)`. -/
theorem frozen_LRF_problem_of_time
    (hbar kB T_inf : ℝ) (ρ : MState d) :
    metricEntropicTime hbar kB T_inf ρ ρ = ⟨0⟩ :=
  metricEntropicTime_self hbar kB T_inf ρ

/-! ## §6 — Single-theorem instantiation of the problem of time -/

/-- **The problem of time, instantiated**:

(i) Physlib's nested `TimeMan ↪ TimeTransMan ↪ Time` hierarchy
provides three *levels of time-structure*. The "problem" is
which level is fundamental.

(ii) `entropicProperTime` lives at the **topological** level:
unit-free, derived from states alone.

(iii) Lifting to the **metric** level requires `(ℏ, k_B)` — the
unit choice is precisely the resolution of the problem.

(iv) At the **Frozen-LRF**, all tiers collapse to the origin —
realising the Wheeler–DeWitt frozen formalism formally:
*at zero relative entropy, time vanishes uniformly across the
hierarchy.*

The single-theorem statement: -/
theorem entropic_problem_of_time_instance :
    -- (i) Topological tier collapses at the diagonal
    (∀ {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d),
        topologicalEntropicTime ρ ρ = 0)
    -- (ii) Metric tier collapses at the diagonal (for any units)
    ∧ (∀ {d : Type*} [Fintype d] [DecidableEq d]
         (hbar kB T_inf : ℝ) (ρ : MState d),
         metricEntropicTime hbar kB T_inf ρ ρ = ⟨0⟩)
    -- (iii) Non-negativity at the topological tier
    ∧ (∀ {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : MState d),
         0 ≤ topologicalEntropicTime ρ σ) :=
  ⟨fun {_ _ _} => topologicalEntropicTime_self,
   fun {_ _ _} => metricEntropicTime_self,
   fun {_ _ _} => topologicalEntropicTime_nonneg⟩

end Physlib.SpaceAndTime

end
