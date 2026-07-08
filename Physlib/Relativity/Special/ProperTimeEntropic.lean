/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.ProperTime
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.Thermodynamics.SecondLaw

/-!
# Proper time and the entropic proper time

Relates `SpaceTime.properTime` to the entropic proper time of
`Physlib.SpaceAndTime.EntropicProperTime`: `properTime q p` equals the total
proper time `totalProperTimeMetric U q p ρ σ = geometricInterval q p +
(ℏ/(k_B T_∞))·D(ρ‖σ)` at the frozen condition `ρ = σ`, where the entropic
contribution vanishes; along a non-stationary density-matrix trajectory coupled
to an `EntropyArrowWorldline` the total proper time decomposes as
`geometricInterval + U.scale · Δτ_ent`, reducing to `properTime` exactly on
reversible worldlines.

## References

- **Araki 1976** — *Relative Hamiltonian for faithful normal states of a von Neumann algebra* [bib: `Araki1976`]
- **Connes & Rovelli 1994** — *Von Neumann algebra automorphisms and time-thermodynamics relation* [bib: `ConnesRovelli1994`]
- **Tolman 1930** — *On the Weight of Heat and Temperature in General Relativity* [bib key needed: `Tolman1930`]
-/

@[expose] public section

noncomputable section

namespace SpaceTime

open Manifold Matrix Real ComplexConjugate Lorentz Vector

/-! ## Proper time as the frozen residue of total proper time

The entropic identifications: `properTime` coincides with `geometricInterval`
(definitionally), hence with `totalProperTimeMetric` at `ρ = σ`, where the
entropic contribution `(ℏ/(k_B T_∞))·D(ρ‖σ)` vanishes
(`entropicProperTimeMetric_self`).
-/

open QuantumInfo.Finite

variable {sd : ℕ}

/-- `properTime` is definitionally the geometric Minkowski interval
`geometricInterval` of `Physlib.SpaceAndTime.EntropicProperTime`. -/
theorem properTime_eq_geometricInterval (q p : SpaceTime sd) :
    properTime q p = geometricInterval q p := rfl

/-- **Frozen identification.** `properTime q p` is the value of the total
proper time at the frozen condition `ρ = σ`, for any choice of entropic-time
units `U` and any density matrix `ρ` (the value is independent of these
because `entropicProperTimeMetric U ρ ρ = 0`). -/
theorem properTime_eq_totalProperTimeMetric_at_frozen
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    properTime q p = totalProperTimeMetric U q p ρ ρ :=
  (totalProperTimeMetric_at_frozen U q p ρ).symm

/-- **Frozen identification, complex level.** `properTime` is the value of
`complexProperTimeMetric` at `ρ = σ`. -/
theorem properTime_eq_complexProperTimeMetric_re_at_frozen
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    (properTime q p : ℂ) = complexProperTimeMetric U q p ρ ρ :=
  (complexProperTimeMetric_at_frozen U q p ρ).symm

/-- For timelike intervals, the total proper time at the frozen condition is
strictly positive — `properTime_pos_ofTimeLike` transported through the frozen
identification. -/
theorem totalProperTimeMetric_at_frozen_pos_ofTimeLike
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d)
    (h : causalCharacter (p - q) = .timeLike) :
    0 < totalProperTimeMetric U q p ρ ρ := by
  rw [← properTime_eq_totalProperTimeMetric_at_frozen]
  exact properTime_pos_ofTimeLike q p h

/-- For lightlike intervals, the total proper time at the frozen condition
vanishes. -/
theorem totalProperTimeMetric_at_frozen_zero_ofLightLike
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d)
    (h : causalCharacter (p - q) = .lightLike) :
    totalProperTimeMetric U q p ρ ρ = 0 := by
  rw [← properTime_eq_totalProperTimeMetric_at_frozen]
  exact properTime_zero_ofLightLike q p h

/-- For spacelike intervals, the total proper time at the frozen condition
defaults to zero (`√` of a non-positive number). -/
theorem totalProperTimeMetric_at_frozen_zero_ofSpaceLike
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d)
    (h : causalCharacter (p - q) = .spaceLike) :
    totalProperTimeMetric U q p ρ ρ = 0 := by
  rw [← properTime_eq_totalProperTimeMetric_at_frozen]
  exact properTime_zero_ofSpaceLike q p h

/-! ## The non-frozen direction — `totalProperTimeMetric` along an
    `EntropyArrowWorldline`

The frozen direction (`ρ = σ`) reduces `totalProperTimeMetric` to
`properTime`. The complementary, non-frozen direction expresses the entropic
contribution along a density-matrix trajectory `ρ : ℝ → MState d` via an
`EntropyArrowWorldline`'s `τ_ent_along`:

  `totalProperTime(t₁, t₂) - geometricInterval = U.scale · Δτ_ent`.

This relates the entropic correction `(ℏ/(k_B T_∞))·D(ρ‖σ)` to the
second-law worldline structure (`EntropyArrowWorldline.τ_ent_along`).
-/

open Physlib.Thermodynamics.SecondLaw

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Coupling between an `EntropyArrowWorldline` and a density-matrix
trajectory through the entropic gap.**  Identifies the worldline's
`τ_ent` advance over `[t₁, t₂]` with the entropic gap `D(ρ t₁ ‖ ρ t₂)`.
Constitutive identification supplied by the consumer. -/
structure EntropicProperTimeCoupling
    (W : EntropyArrowWorldline) (ρ : ℝ → MState d) : Prop where
  /-- The worldline's entropic-time advance equals the entropic gap
  between the corresponding density matrices. -/
  tauEnt_advance_eq_entropicGap : ∀ t₁ t₂ : ℝ,
    W.τ_ent_along t₂ - W.τ_ent_along t₁
      = entropicGap (ρ t₁) (ρ t₂)

/-- **Total proper time decomposes as `geometricInterval + U.scale ·
Δτ_ent`** along the coupled worldline: a geometric component plus an
entropic contribution set by the worldline's `τ_ent` advance. -/
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
the total proper time equals the bare Minkowski interval. -/
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
