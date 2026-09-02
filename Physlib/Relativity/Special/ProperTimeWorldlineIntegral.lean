/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.ProperTime
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

meta import Zil

/- Consolidated from Physlib.Relativity.Special.ProperTimeWorldlineIntegral -/

/-!
# Local Lorentz invariance as a theorem for the flat sector

The game-universe axiom set (gu.md Axiom 16) *assumes* the effective theory is locally
Lorentz invariant.  For the flat sector this is not an assumption but a theorem: the
physical invariants of a pair of events are all preserved by every Lorentz transformation.

* `intervalSq_lorentz_invariant` — the spacetime interval `⟪p−q, p−q⟫ₘ` is boost-invariant;
* `properTime_lorentz_invariant` — the proper time `τ = √⟪p−q, p−q⟫ₘ` is boost-invariant;
* `causalCharacter_sub_lorentz_invariant` — the causal character (timelike/null/spacelike)
  of the separation is boost-invariant, so *which* observers accumulate proper time is
  frame-independent.

Together with the rest-mass Casimir invariance
(`ComptonClock.PoincareCasimirMassShell.poincareRestMassSq_boost_invariant`) these retire
the standing "assumes locally Lorentz invariant" premise of gu.md Axiom 16 for the flat
sector: the tetrad/inertial frame is pure gauge, and only the interval, proper time, and
causal order are physical.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace SpaceTime

open Lorentz Vector

variable {d : ℕ}

/-- **The spacetime interval is Lorentz-invariant.** -/
@[zil_level physical_theorem]
theorem intervalSq_lorentz_invariant (Λ : LorentzGroup d) (q p : SpaceTime d) :
    ⟪(Λ • p) - (Λ • q), (Λ • p) - (Λ • q)⟫ₘ = ⟪p - q, p - q⟫ₘ := by
  rw [← smul_sub, minkowskiProduct_invariant]

/-- **Proper time is Lorentz-invariant** — every inertial observer assigns the same proper
time to a pair of events (gu.md Axiom 6/16, flat sector). -/
@[zil_level bridge_theorem]
theorem properTime_lorentz_invariant (Λ : LorentzGroup d) (q p : SpaceTime d) :
    properTime (Λ • q) (Λ • p) = properTime q p := by
  unfold properTime
  rw [← smul_sub, minkowskiProduct_invariant]

/-- **The causal character of a separation is Lorentz-invariant** — whether two events are
timelike, null, or spacelike separated (hence whether a proper time accrues between them)
is frame-independent. -/
@[zil_level physical_theorem]
theorem causalCharacter_sub_lorentz_invariant (Λ : LorentzGroup d) (q p : SpaceTime d) :
    causalCharacter ((Λ • p) - (Λ • q)) = causalCharacter (p - q) := by
  rw [← smul_sub, causalCharacter_invariant]

end SpaceTime

/- ZIL-BEGIN -/

open Zil
open SpaceTime

zil attach properTime_lorentz_invariant where
  formalizes @ "claim:proper-time-is-lorentz-invariant-every-inertial-observer-assigns-the-same-proper-time-to-a-pair-of-events-so-local-lorentz-invariance-is-a-theorem-not-an-assumption-for-the-flat-sector",
  supported_by @ "lean:SpaceTime.properTime",
  caveat @ "claim:this-is-the-flat-minkowski-sector-not-the-curved-locally-lorentz-invariant-effective-theory-assumed-in-general"

zil attach intervalSq_lorentz_invariant where
  supported_by @ "lean:Vector.minkowskiProduct_invariant",
  formalizes @ "claim:the-spacetime-interval-is-lorentz-invariant"

zil attach causalCharacter_sub_lorentz_invariant where
  supported_by @ "lean:Vector.causalCharacter_invariant",
  formalizes @ "claim:the-causal-character-of-a-separation-timelike-null-or-spacelike-is-lorentz-invariant-so-which-observers-accumulate-proper-time-is-frame-independent"

zil_file_contract physlib.properTimeLorentzInvariance where
  promises "For the flat sector, local Lorentz invariance is a theorem rather than the assumption of gu.md Axiom 16: the physical invariants of a pair of events are all preserved by every Lorentz transformation. The spacetime interval is boost-invariant, the proper time square root of the interval is boost-invariant so every inertial observer assigns the same proper time, and the causal character timelike null or spacelike of the separation is boost-invariant so which observers accumulate proper time is frame-independent. The tetrad inertial frame is pure gauge and only the interval, proper time, and causal order are physical."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:SpaceTime.properTime"
  ]
  forbids_substitutes [
    "reading the flat-sector invariance as the full curved locally-Lorentz-invariant effective theory",
    "treating the tetrad frame choice as physical rather than gauge"
  ]
  witnessed_by [
    intervalSq_lorentz_invariant,
    properTime_lorentz_invariant,
    causalCharacter_sub_lorentz_invariant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.properTimeLorentzInvariance

/- Consolidated from Physlib.Relativity.Special.ProperTimeWorldlineIntegral -/

/-!
# Proper time as a worldline arc-length integral

gu.md Axiom 6 defines the proper time along a timelike worldline `γ` as the arc-length integral of the
metric,
`τ[γ] = ∫ √(g_{μν} γ'^μ γ'^ν) dλ`
(in the repository's `+---` Minkowski convention, timelike vectors have positive `⟪·,·⟫ₘ`, so no extra
sign is needed).  The repository so far carries only the two-point interval proper time
`properTime q p = √⟪p − q, p − q⟫ₘ` (`Physlib.Relativity.Special.ProperTime`); this module adds the
worldline **integral** and shows it reduces to that two-point form on a straight (inertial) worldline.

* `properTimeIntegral` — the Lorentzian arc-length functional `∫₀ᵀ √⟪γ'(λ), γ'(λ)⟫ₘ dλ`.
* `properTimeIntegral_straight` — for the inertial worldline `γ(λ) = q + λ·v` (constant four-velocity),
  the integral equals the interval proper time `properTime q (q + T·v)`.
* `properTimeIntegral_straight_lorentz_invariant` — the inertial worldline proper time is Lorentz
  invariant.

Built on the existing `SpaceTime d = Lorentz.Vector d`, the continuous bilinear Minkowski product
`⟪·,·⟫ₘ = minkowskiProduct`, and `properTime` — same carrier, so the reduction is a short algebraic
computation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace SpaceTime

open Real MeasureTheory Lorentz Lorentz.Vector

/-- **The Lorentzian proper-time arc-length functional** `τ[γ] = ∫₀ᵀ √⟪γ'(λ), γ'(λ)⟫ₘ dλ`. -/
def properTimeIntegral {d : ℕ} (γ : ℝ → SpaceTime d) (T : ℝ) : ℝ :=
  ∫ lam in (0 : ℝ)..T, Real.sqrt ⟪deriv γ lam, deriv γ lam⟫ₘ

/-- **The worldline proper time reduces to the interval proper time on an inertial worldline.**  For
the straight worldline `γ(λ) = q + λ·v` with constant four-velocity `v`, the arc-length integral over
`[0, T]` (with `T ≥ 0`) equals `properTime q (q + T·v) = √⟪T·v, T·v⟫ₘ`. -/
@[zil_level bridge_theorem]
theorem properTimeIntegral_straight {d : ℕ} (q v : SpaceTime d) (T : ℝ) (hT : 0 ≤ T) :
    properTimeIntegral (fun lam => q + lam • v) T = properTime q (q + T • v) := by
  have hderiv : ∀ lam : ℝ, deriv (fun l : ℝ => q + l • v) lam = v := fun lam => by
    have h : HasDerivAt (fun l : ℝ => q + l • v) v lam := by
      simpa using ((hasDerivAt_id lam).smul_const v).const_add q
    exact h.deriv
  have hquad : ⟪T • v, T • v⟫ₘ = T ^ 2 * ⟪v, v⟫ₘ := by
    simp only [minkowskiProduct_apply, minkowskiProductMap_smul_fst, minkowskiProductMap_smul_snd]
    ring
  unfold properTimeIntegral properTime
  simp only [hderiv]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, add_sub_cancel_left, hquad,
    Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT]

/-- **The inertial-worldline proper time is Lorentz invariant.**  Boosting the straight worldline
`γ(λ) = q + λ·v` by `Λ ∈ LorentzGroup d` leaves its arc-length proper time unchanged. -/
@[zil_level physical_theorem]
theorem properTimeIntegral_straight_lorentz_invariant {d : ℕ} (Λ : LorentzGroup d)
    (q v : SpaceTime d) (T : ℝ) (hT : 0 ≤ T) :
    properTimeIntegral (fun lam => (Λ • q) + lam • (Λ • v)) T
      = properTimeIntegral (fun lam => q + lam • v) T := by
  rw [properTimeIntegral_straight (Λ • q) (Λ • v) T hT, properTimeIntegral_straight q v T hT]
  have hΛ : (Λ • q) + T • (Λ • v) = Λ • (q + T • v) := by rw [smul_add, smul_comm]
  rw [hΛ, properTime_lorentz_invariant]

end SpaceTime

/- ZIL-BEGIN -/

open Zil
open SpaceTime

zil attach properTimeIntegral_straight where
  supported_by @ "lean:Vector.minkowskiProductMap_smul_fst",
  supported_by @ "lean:Vector.minkowskiProductMap_smul_snd",
  formalizes @ "claim:the-lorentzian-proper-time-worldline-arc-length-integral-of-the-minkowski-metric-reduces-to-the-two-point-interval-proper-time-on-a-straight-inertial-worldline-with-constant-four-velocity"

zil attach properTimeIntegral_straight_lorentz_invariant where
  formalizes @ "claim:the-inertial-worldline-arc-length-proper-time-is-lorentz-invariant-a-boost-of-the-straight-worldline-leaves-its-proper-time-unchanged",
  supported_by @ "lean:SpaceTime.properTime_lorentz_invariant"

zil_file_contract physlib.properTimeWorldlineIntegral where
  promises "The Lorentzian proper time as a worldline arc-length integral, gu.md Axiom 6. The proper-time integral is the arc-length functional integral over zero to T of the square root of the Minkowski self-product of the worldline velocity. For the straight inertial worldline q plus lambda times v with constant four-velocity v, this arc-length integral equals the two-point interval proper time, properTime q of q plus T times v, equal to the square root of the Minkowski self-product of T times v. And the inertial-worldline arc-length proper time is Lorentz invariant: boosting the straight worldline by a Lorentz group element leaves its proper time unchanged. Built on the existing spacetime vector type, the continuous bilinear Minkowski product in the plus minus minus minus convention where timelike vectors have positive self-product, and the existing two-point interval proper time; scope is the straight inertial worldline reduction, not a general curved-worldline reparametrization."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:SpaceTime.properTime",
    "lean:Lorentz.Vector.minkowskiProduct",
    "lean:SpaceTime.properTime_lorentz_invariant"
  ]
  forbids_substitutes [
    "reading the straight-worldline reduction as a general curved-worldline arc-length reparametrization or a manifold geodesic-length functional"
  ]
  witnessed_by [
    properTimeIntegral_straight,
    properTimeIntegral_straight_lorentz_invariant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.properTimeWorldlineIntegral

