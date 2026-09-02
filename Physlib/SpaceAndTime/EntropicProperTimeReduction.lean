/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.ProperTime
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.Thermodynamics.SecondLaw.ClausiusEntropyArrow

/-!
# Reduction of the entropic total proper time to the geometric proper time

`SpaceAndTime.EntropicProperTime` defines the dimensionally consistent total proper time

  `totalProperTimeMetric U q p ρ σ = geometricInterval q p + (ℏ/(k_B T_∞))·D(ρ‖σ)`.

This file records how it reduces to the standard special-relativistic
`SpaceTime.properTime`:

* **At the frozen condition `ρ = σ`** the relative-entropy term vanishes
  (`entropicProperTimeMetric_self`), so the total proper time equals `properTime q p` for
  every choice of entropic-time units `U` and state `ρ`
  (`properTime_eq_totalProperTimeMetric_at_frozen`); at the complex level the metric
  reduces to the real geometric value
  (`properTime_eq_complexProperTimeMetric_re_at_frozen`).
* **Along a density-matrix trajectory** coupled to an `EntropyArrowWorldline`
  (`EntropicProperTimeCoupling` — an identification supplied by the consumer, on which
  the lemmas below are conditional), the total proper time decomposes as the geometric
  interval plus the scaled `τ_ent` advance
  (`totalProperTime_eq_geometric_plus_scale_tauEnt_advance`), and a reversible worldline
  (constant `τ_ent`) reduces it back to `properTime`
  (`totalProperTime_eq_properTime_at_reversible_worldline`).

The geometric content (positivity on timelike separations, vanishing on lightlike and
spacelike ones) is proved on `SpaceTime.properTime` in `Relativity.Special.ProperTime`;
via the frozen-condition identity those statements apply verbatim to
`totalProperTimeMetric` at `ρ = σ`.

## References

- **Araki 1976** — *Relative Hamiltonian for faithful normal states of a von Neumann
  algebra* [bib: `Araki1976`]
- **Connes & Rovelli 1994** — *Von Neumann algebra automorphisms and time-thermodynamics
  relation* [bib: `ConnesRovelli1994`]
-/

@[expose] public section

namespace SpaceTime

open QuantumInfo.Finite
open Physlib.Thermodynamics.SecondLaw

variable {sd : ℕ} {d : Type*} [Fintype d] [DecidableEq d]

/-! ## A. Reduction at the frozen condition -/

/-- At the frozen condition `ρ = σ` the relative-entropy term of the total proper time
vanishes, so the total proper time is the geometric proper time — for any units `U` and
any state `ρ`, since `D(ρ‖ρ) = 0`. -/
lemma properTime_eq_totalProperTimeMetric_at_frozen
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    properTime q p = totalProperTimeMetric U q p ρ ρ := by
  rw [totalProperTimeMetric_at_frozen]
  rfl

/-- The complex-level reduction: at the frozen condition the complex proper-time metric
is the (real) geometric proper time. -/
lemma properTime_eq_complexProperTimeMetric_re_at_frozen
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    (properTime q p : ℂ) = complexProperTimeMetric U q p ρ ρ := by
  rw [complexProperTimeMetric_at_frozen]
  rfl

/-! ## B. Decomposition along an entropy-arrow worldline -/

/-- Coupling between an `EntropyArrowWorldline` and a density-matrix trajectory: the
worldline's `τ_ent` advance over `[t₁, t₂]` equals the entropic gap `D(ρ t₁ ‖ ρ t₂)`.
This identification is supplied by the consumer; the lemmas below are conditional on
it. -/
structure EntropicProperTimeCoupling
    (W : EntropyArrowWorldline) (ρ : ℝ → MState d) : Prop where
  /-- The worldline's entropic-time advance equals the entropic gap
  between the corresponding density matrices. -/
  tauEnt_advance_eq_entropicGap : ∀ t₁ t₂ : ℝ,
    W.τ_ent_along t₂ - W.τ_ent_along t₁
      = entropicGap (ρ t₁) (ρ t₂)

/-- Along a coupled worldline the total proper time is the geometric interval plus the
scaled `τ_ent` advance. This is the definitional unfolding of `totalProperTimeMetric`
combined with the coupling identification. -/
lemma totalProperTime_eq_geometric_plus_scale_tauEnt_advance
    (W : EntropyArrowWorldline) (U : EntropicTimeUnits)
    (ρ : ℝ → MState d) (C : EntropicProperTimeCoupling W ρ)
    (q p : SpaceTime sd) (t₁ t₂ : ℝ) :
    totalProperTimeMetric U q p (ρ t₁) (ρ t₂)
      = geometricInterval q p
          + U.scale * (W.τ_ent_along t₂ - W.τ_ent_along t₁) := by
  unfold totalProperTimeMetric entropicProperTimeMetric
  rw [C.tauEnt_advance_eq_entropicGap]

/-- A reversible worldline (constant `S_I`, hence constant `τ_ent`) has zero advance, so
the entropic contribution vanishes and the total proper time equals the geometric
interval. -/
lemma totalProperTime_eq_geometric_at_reversible_worldline
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

/-- At a reversible worldline the total proper time is `SpaceTime.properTime`. -/
lemma totalProperTime_eq_properTime_at_reversible_worldline
    (W : EntropyArrowWorldline) (U : EntropicTimeUnits)
    (ρ : ℝ → MState d) (C : EntropicProperTimeCoupling W ρ)
    (hRev : W.IsReversible)
    (q p : SpaceTime sd) (t₁ t₂ : ℝ) :
    totalProperTimeMetric U q p (ρ t₁) (ρ t₂) = properTime q p := by
  rw [totalProperTime_eq_geometric_at_reversible_worldline W U ρ C hRev q p t₁ t₂]
  rfl

end SpaceTime

end
