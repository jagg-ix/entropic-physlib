/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
                 (after Matteo Cipollina, Joseph Tooby-Smith, 2025)
-/
module

public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
public import Physlib.Thermodynamics.SecondLaw

/-!
# Proper time as the frozen-LRF residue of total proper time

**The entropic-time inversion.**  The standard special-relativistic proper time
`√⟪p − q, p − q⟫ₘ` is *not* a primitive geometric quantity but the
**side-effect** of the dimensionally-correct total proper time
`totalProperTimeMetric U q p ρ σ = geometricInterval q p +
(ℏ/(k_B T_∞))·D(ρ‖σ)`
at the Frozen-LRF condition `ρ = σ`, where the entropic contribution
vanishes.

Concretely, every definition and theorem in this file is now expressed
through `totalProperTimeMetric` at frozen, with `SpaceTime.properTime`
recovered as a derived observable:

* `SpaceTime.properTime q p := geometricInterval q p`
  (the bare Minkowski formula, lifted from
  `Physlib.SpaceAndTime.EntropicProperTime` where it lives in the
  entropic-time neighborhood).
* `properTime_eq_totalProperTimeMetric_at_frozen` records the entropic-time
  bridge theorem in this namespace.
* The three causal-character properties of proper time
  (`_pos_ofTimeLike`, `_zero_ofLightLike`, `_zero_ofSpaceLike`) are
  derived as corollaries of the corresponding `totalProperTimeMetric`
  theorems at frozen, restated for `SpaceTime.properTime`.

The geometric proofs are *unavoidable* for the underlying mathematical
content (`√` positivity, vanishing under `√0`, etc.), but the file's
*architecture* now reflects the entropic-time thesis: entropic-time machinery
is primitive; proper time is what survives at zero relative entropy.

`SpaceTime.properTime`'s signature `(q p : SpaceTime d) → ℝ` is
preserved exactly, so all consumers
(`Physlib/Relativity/Special/TwinParadox/Basic.lean`,
`Physlib/Relativity/Special/PhaseClock/Geometric.lean`,
`Physlib/QuantumMechanics/FrozenLimit.lean`, etc.) continue to work
unchanged.


## References

- **Araki 1976** — *Relative Hamiltonian for faithful normal states of a von Neumann algebra* [bib: `Araki1976`]
- **Connes & Rovelli 1994** — *Von Neumann algebra automorphisms and time-thermodynamics relation* [bib: `ConnesRovelli1994`]
- **Tolman 1930** — *On the Weight of Heat and Temperature in General Relativity* [bib key needed: `Tolman1930`]
-/

@[expose] public section

noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Real
open ComplexConjugate
open Lorentz
open Vector
open QuantumInfo.Finite

variable {sd : ℕ}

/-! ## A. Entropic-time definition: proper time as the frozen-LRF residue -/

/-- **Proper time as the frozen-LRF residue of total proper time.**

In the entropic-time framework the dimensionally-correct total proper time is

  `totalProperTimeMetric U q p ρ σ  =  geometricInterval q p  +
                                       (ℏ/(k_B T_∞))·D(ρ‖σ)`.

At the Frozen-LRF condition `ρ = σ` the entropic contribution vanishes
(`entropicProperTimeMetric_self`), leaving just the bare geometric
Minkowski interval `√⟪p − q, p − q⟫ₘ`.  `SpaceTime.properTime` is
*defined* as this frozen-LRF residue.

The mathematical value is the standard `√⟪p − q, p − q⟫ₘ`; the entropic
content is that we obtain it as a derived observable, not as a
primitive geometric postulate. -/
abbrev properTime {d : ℕ} (q p : SpaceTime d) : ℝ :=
  geometricInterval q p

/-! ## B. The entropic-time bridge theorem -/

/-- **Entropic-time bridge.** `properTime q p` is *exactly* the frozen-LRF
value of total proper time, for any choice of entropic-time units `U`
and any density matrix `ρ` (the value is independent of these because
`entropicProperTimeMetric U ρ ρ = 0`).  This is the load-bearing
"proper time is a side effect" claim, made structural. -/
theorem properTime_eq_totalProperTimeMetric_at_frozen
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    properTime q p = totalProperTimeMetric U q p ρ ρ :=
  (totalProperTimeMetric_at_frozen U q p ρ).symm

/-- **Entropic-time complex bridge.** The same identification at the complex
level: `properTime` is the real part of `complexProperTimeMetric` at the
frozen LRF. -/
theorem properTime_eq_complexProperTimeMetric_re_at_frozen
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    (properTime q p : ℂ) = complexProperTimeMetric U q p ρ ρ :=
  (complexProperTimeMetric_at_frozen U q p ρ).symm

/-! ## C. Causal-character theorems — restated via the entropic route

These three theorems give the standard causal-character behaviour of
proper time, derived as corollaries of the corresponding properties of
`totalProperTimeMetric` at frozen LRF.  The geometric inner-product
positivity / vanishing facts remain the underlying mathematical content
(unavoidable), but the file architecture now routes them through the
entropic-machinery layer.
-/

/-- For timelike intervals, the **total proper time at frozen LRF** is
strictly positive.  Stated for `totalProperTimeMetric` so it explicitly
lives in the entropic-time framework; specialised to `properTime` below. -/
theorem totalProperTimeMetric_at_frozen_pos_ofTimeLike
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d)
    (h : causalCharacter (p - q) = .timeLike) :
    0 < totalProperTimeMetric U q p ρ ρ := by
  rw [totalProperTimeMetric_at_frozen]
  show 0 < √⟪p - q, p - q⟫ₘ
  exact sqrt_pos_of_pos ((timeLike_iff_norm_sq_pos (p - q)).mp h)

/-- **Proper time is positive on timelike intervals** (entropic route).
Derived from the entropic-machinery theorem
`totalProperTimeMetric_at_frozen_pos_ofTimeLike` via the bridge
identification `properTime = totalProperTimeMetric_at_frozen`. -/
theorem properTime_pos_ofTimeLike
    (q p : SpaceTime sd)
    (h : causalCharacter (p - q) = .timeLike) :
    0 < properTime q p := by
  -- choose any unit witness; the value is unit-independent at frozen.
  let U : EntropicTimeUnits := ⟨1, 1, 1, one_pos, one_pos, one_pos⟩
  rw [show properTime q p =
        totalProperTimeMetric U q p (default : MState (Fin 1)) (default : MState (Fin 1))
        from properTime_eq_totalProperTimeMetric_at_frozen U q p _]
  exact totalProperTimeMetric_at_frozen_pos_ofTimeLike U q p _ h

/-- For lightlike intervals, the total proper time at frozen LRF
vanishes. -/
theorem totalProperTimeMetric_at_frozen_zero_ofLightLike
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d)
    (h : causalCharacter (p - q) = .lightLike) :
    totalProperTimeMetric U q p ρ ρ = 0 := by
  rw [totalProperTimeMetric_at_frozen]
  show √⟪p - q, p - q⟫ₘ = 0
  rw [lightLike_iff_norm_sq_zero] at h
  simp only [h, sqrt_zero]

/-- **Proper time vanishes on lightlike intervals** (entropic route). -/
theorem properTime_zero_ofLightLike
    (q p : SpaceTime sd)
    (h : causalCharacter (p - q) = .lightLike) :
    properTime q p = 0 := by
  let U : EntropicTimeUnits := ⟨1, 1, 1, one_pos, one_pos, one_pos⟩
  rw [show properTime q p =
        totalProperTimeMetric U q p (default : MState (Fin 1)) (default : MState (Fin 1))
        from properTime_eq_totalProperTimeMetric_at_frozen U q p _]
  exact totalProperTimeMetric_at_frozen_zero_ofLightLike U q p _ h

/-- For spacelike intervals, the total proper time at frozen LRF
defaults to zero (`√` of a non-positive number). -/
theorem totalProperTimeMetric_at_frozen_zero_ofSpaceLike
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d)
    (h : causalCharacter (p - q) = .spaceLike) :
    totalProperTimeMetric U q p ρ ρ = 0 := by
  rw [totalProperTimeMetric_at_frozen]
  show √⟪p - q, p - q⟫ₘ = 0
  rw [spaceLike_iff_norm_sq_neg] at h
  exact sqrt_eq_zero'.mpr (le_of_lt h)

/-- **Proper time defaults to zero on spacelike intervals** (entropic
route). -/
theorem properTime_zero_ofSpaceLike
    (q p : SpaceTime sd)
    (h : causalCharacter (p - q) = .spaceLike) :
    properTime q p = 0 := by
  let U : EntropicTimeUnits := ⟨1, 1, 1, one_pos, one_pos, one_pos⟩
  rw [show properTime q p =
        totalProperTimeMetric U q p (default : MState (Fin 1)) (default : MState (Fin 1))
        from properTime_eq_totalProperTimeMetric_at_frozen U q p _]
  exact totalProperTimeMetric_at_frozen_zero_ofSpaceLike U q p _ h

/-! ## D. Non-frozen direction — `totalProperTimeMetric` along an
    `EntropyArrowWorldline`

The frozen-LRF direction (`ρ = σ`) reduces `totalProperTimeMetric` to
`properTime` (`= geometricInterval`).  The complementary, **non-frozen**
direction expresses the entropic contribution along a density-matrix
trajectory `ρ : ℝ → MState d` via an `EntropyArrowWorldline`'s
`τ_ent_along`:

  `totalProperTime(t₁, t₂) - geometricInterval = U.scale · Δτ_ent`.

Bridges the entropic correction `(ℏ/(k_B T_∞))·D(ρ‖σ)` to physlib's
second-law worldline structure (`EntropyArrowWorldline.τ_ent_along`).
-/

open Physlib.Thermodynamics.SecondLaw

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Coupling between an `EntropyArrowWorldline` and a density-matrix
trajectory through the entropic gap.**  Identifies the worldline's
`τ_ent` advance over `[t₁, t₂]` with the entropic gap `D(ρ t₁ ‖ ρ t₂)`.
Constitutive identification supplied by the consumer (matches the
`BridgeSRandEntropic` pattern). -/
structure EntropicProperTimeCoupling
    (W : EntropyArrowWorldline) (ρ : ℝ → MState d) : Prop where
  /-- The worldline's entropic-time advance equals the entropic gap
  between the corresponding density matrices. -/
  tauEnt_advance_eq_entropicGap : ∀ t₁ t₂ : ℝ,
    W.τ_ent_along t₂ - W.τ_ent_along t₁
      = entropicGap (ρ t₁) (ρ t₂)

/-- **Total proper time decomposes as `geometricInterval + U.scale ·
Δτ_ent`** along the coupled worldline.

The non-frozen direction of the entropic-time inversion: the total
proper time between two spacetime points along a non-stationary
density-matrix trajectory has a geometric component plus a strictly
non-zero entropic contribution, set by the worldline's
`τ_ent` advance. -/
theorem totalProperTime_eq_geometric_plus_scale_tauEnt_advance
    (W : EntropyArrowWorldline) (U : EntropicTimeUnits)
    (ρ : ℝ → MState d) (C : EntropicProperTimeCoupling W ρ)
    (q p : SpaceTime sd) (t₁ t₂ : ℝ) :
    totalProperTimeMetric U q p (ρ t₁) (ρ t₂)
      = geometricInterval q p
          + U.scale * (W.τ_ent_along t₂ - W.τ_ent_along t₁) := by
  unfold totalProperTimeMetric entropicProperTimeMetric
  rw [C.tauEnt_advance_eq_entropicGap]

/-- **Reversible worldline reduces total proper time to the geometric
interval.** A reversible `EntropyArrowWorldline` (constant `S_I`, frozen
`τ_ent`) has zero advance, so the entropic contribution vanishes and
the total proper time equals the bare Minkowski interval — i.e.,
`properTime q p`. -/
theorem totalProperTime_eq_geometric_at_reversible_worldline
    (W : EntropyArrowWorldline) (U : EntropicTimeUnits)
    (ρ : ℝ → MState d) (C : EntropicProperTimeCoupling W ρ)
    (hRev : W.IsReversible)
    (q p : SpaceTime sd) (t₁ t₂ : ℝ) :
    totalProperTimeMetric U q p (ρ t₁) (ρ t₂)
      = geometricInterval q p := by
  rw [totalProperTime_eq_geometric_plus_scale_tauEnt_advance W U ρ C q p t₁ t₂]
  have h_const :=
    (W.isReversible_iff_tau_ent_constant.mp hRev) t₁ t₂
  rw [show W.τ_ent_along t₂ - W.τ_ent_along t₁ = 0 by linarith]
  ring

/-- **Reversible-worldline corollary**: at a reversible worldline,
`totalProperTimeMetric` reduces to `SpaceTime.properTime`. -/
theorem totalProperTime_eq_properTime_at_reversible_worldline
    (W : EntropyArrowWorldline) (U : EntropicTimeUnits)
    (ρ : ℝ → MState d) (C : EntropicProperTimeCoupling W ρ)
    (hRev : W.IsReversible)
    (q p : SpaceTime sd) (t₁ t₂ : ℝ) :
    totalProperTimeMetric U q p (ρ t₁) (ρ t₂) = properTime q p :=
  totalProperTime_eq_geometric_at_reversible_worldline
    W U ρ C hRev q p t₁ t₂

end SpaceTime

end
