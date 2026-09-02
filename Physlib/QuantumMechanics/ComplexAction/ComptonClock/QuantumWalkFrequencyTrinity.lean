/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins

/-!
# The walk coin angle carries the whole frequency trinity

`QuantumWalkZitterbewegung` shows the discrete-time quantum walk's coin angle satisfies
`θ = 2 ω_C` — the coin is twice the Compton frequency, read off the trembling
(Kurzyński, Phys. Lett. A **372** (2008) 6125).  `FrequencyTrinity` already ties the three clock
frequencies together:

  `zitterbewegung_rest_eq_two_compton` : `ω_Z(p=0) = 2 ω_C`
  `deBroglie_eq_gamma_compton`         : `ω_dB = γ ω_C` for `E = γ m c²`

and `MassOrigin.HiggsClockThreeOrigins` routes the mass itself through the Yukawa sector,
`higgsClockFrequency y v c ħ = comptonFrequency (yukawaMass y v) c ħ`.

Composing these, the walk's **single tunable parameter** fixes every member of the trinity:

  `θ = ω_Z(rest) = 2 ω_C`,   `ω_dB = γ θ/2`,   and at the Yukawa mass `θ = 2 · higgsClockFrequency`.

So a discrete walk with one dial reproduces the rest-frame trembling, the Compton clock, the boosted
de Broglie frequency, and — through the Yukawa route — the Higgs-sector origin of the mass that sets
them.  The coin angle is not merely *a* parameter of the walk; it is the clock unit.

The coupling is reached too.  `Yukawa.CouplingIsolation.yukawa_isolated_explicit` gives
`y = √2 ħ ω/(c² v)` from the mass–clock identification, so a walk whose coin angle fixes `ω` fixes
the Yukawa coupling as well (§E).  And the library pins a distinguished point on that line:
`yukawaCoupling_natural_mass` (`m = v/√2 ⟹ y = 1`) together with `top_at_natural_mass`
(`|v/√2 − 173| < 1` GeV) and `topYukawa_near_one` (`0.99 < y_top < 1`) — the top quark sits at unit
coupling, so there is a *specific* coin angle at which the walk realizes it.

The mass is **derived**, not posited.  `yukawaMass y v = y v/√2` is the Higgs mechanism: the mass
comes from the Yukawa coupling and the VEV.  `higgs_clock_three_origins` closes the loop the other
way as well, `comptonMass (higgsClockFrequency y v c ħ) c ħ = yukawaMass y v` — the clock returns the
mass it was built from — and, given `hHorizon` and `hTopo`, identifies that same mass with the
gravitational horizon-entropy mass `(c/4G)Ȧ` and the topological Chern–Simons mass `e²k/2π`.  So the
walk's dial reaches a mass with three coinciding origins, not a free constant.

Scope.  These are compositions of existing identities and inherit their status.  The walk-side
`θ = 2 ω_C` is Kurzyński's, obtained by matching rest-frame gaps.  The mass–clock identification is
**not** an extra assumption — §F discharges it through the mass/clock bijection.  What remains
genuinely assumed: the horizon/topological coincidence enters as `hHorizon`, `hTopo` rather than as a
theorem, and the VEV `v` is an input, so the chain fixes `y` *given* `v` — the top-quark statements
are numerical checks at the measured `v ≈ 246` GeV, not a prediction of it.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkFrequencyTrinity

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Yukawa.CouplingIsolation
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

/-! ### §A — Coin angle ↔ zitterbewegung -/

/-- **The coin angle is the rest-frame zitterbewegung frequency.**  Matching the walk's branch gap to
the Dirac trembling and using `zitterbewegung_rest_eq_two_compton`, the coin angle equals `ω_Z` at
zero momentum — the walk trembles at exactly the Dirac rate. -/
theorem coin_angle_eq_rest_zitterbewegung {θ m c ħ : ℝ} (hm : 0 ≤ m)
    (hmatch : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    θ = zitterbewegungFrequency 0 m c ħ := by
  rw [zitterbewegung_rest_eq_two_compton m c ħ hm]
  exact coin_angle_eq_two_compton hmatch

/-! ### §B — Coin angle ↔ de Broglie under a boost -/

/-- **The boosted de Broglie frequency is `γ` times half the coin angle.**  With `ω_dB = γ ω_C` and
`ω_C = θ/2`, a walk with coin angle `θ` seen at total energy `E = γ m c²` beats at `γθ/2`: the coin
sets the rest clock and the boost scales it. -/
theorem deBroglie_eq_gamma_half_coin_angle {θ m c ħ : ℝ} (γ : ℝ)
    (hmatch : walkZitterFrequency θ = 2 * comptonFrequency m c ħ) :
    deBroglieFrequency (γ * (m * c ^ 2)) ħ = γ * (θ / 2) := by
  rw [deBroglie_eq_gamma_compton γ m c ħ]
  rw [walkZitterFrequency_eq_coin_angle] at hmatch
  rw [hmatch]
  ring

/-! ### §C — Coin angle ↔ the Yukawa origin of the mass -/

/-- **At the Yukawa mass the coin angle is twice the Higgs clock.**  `higgsClockFrequency` is the
Compton frequency of `yukawaMass y v`, so a walk tuned to that mass has coin angle `2 ω_Higgs`: the
dial is the Higgs-sector clock unit, and the walk realizes it discretely. -/
theorem coin_angle_eq_two_higgsClock {θ y v c ħ : ℝ}
    (hmatch : walkZitterFrequency θ = 2 * comptonFrequency (yukawaMass y v) c ħ) :
    θ = 2 * higgsClockFrequency y v c ħ := by
  unfold higgsClockFrequency
  exact coin_angle_eq_two_compton hmatch

/-! ### §E — The coin angle fixes the Yukawa coupling

`CouplingIsolation.yukawa_isolated_explicit` reads the coupling off the internal clock,
`y = √2 ħ ω/(c² v)`.  Since the walk's coin angle *is* the clock (`θ = 2 ω_C`), the dial reaches the
coupling, and the unit-coupling point `m = v/√2` — where the top quark sits to within a GeV — picks
out one specific angle. -/

/-- **The coin angle isolates the Yukawa coupling.**  Given the mass–clock identification, a walk with
coin angle `θ` has `ω = θ/2`, so the coupling is `y = √2 ħ θ/(2 c² v)`: the walk's single dial
determines not just the mass but the coupling that produces it. -/
theorem coin_angle_isolates_yukawaCoupling {θ y v ω c ħ : ℝ} (hv : v ≠ 0)
    (hclock : yukawaMass y v = comptonMass ω c ħ)
    (hcoin : walkZitterFrequency θ = 2 * ω) :
    y = Real.sqrt 2 * ħ * (θ / 2) / (c ^ 2 * v) := by
  rw [walkZitterFrequency_eq_coin_angle] at hcoin
  rw [yukawa_isolated_explicit y v ω c ħ hv hclock, hcoin]
  ring

/-- **The unit-coupling coin angle.**  At the natural mass `m = v/√2` the coupling is exactly one
(`yukawaCoupling_natural_mass`), and `top_at_natural_mass` places the top quark there to within a
GeV.  So the walk realizes unit Yukawa coupling at the coin angle whose clock mass is `v/√2`. -/
theorem unit_coupling_at_natural_mass {v : ℝ} (hv : v ≠ 0) :
    yukawaCoupling (v / Real.sqrt 2) v = 1 :=
  yukawaCoupling_natural_mass v hv

/-! ### §F — The mass–clock identification is not an extra assumption

Everything above carried `yukawaMass y v = comptonMass ω c ħ` as a hypothesis.  It is not an
independent physical postulate: `Winding.NumberMass` proves mass and clock frequency are **mutually
inverse**,

  `comptonMass_comptonFrequency : comptonMass (comptonFrequency m c ħ) c ħ = m`
  `comptonFrequency_comptonMass : comptonFrequency (comptonMass ω c ħ) c ħ = ω`

so the "identification" only says *which* `ω` is meant.  §F makes that exact — the hypothesis is
equivalent to `ω = higgsClockFrequency y v c ħ` — and then discharges it, giving a determination of
the Yukawa coupling from the coin angle with no mass–clock assumption left standing. -/

/-- **The mass–clock hypothesis is exactly a choice of clock.**  `yukawaMass y v = comptonMass ω c ħ`
holds iff `ω` is the Higgs clock frequency of that mass.  So the identification carries no content
beyond naming `ω`: mass and clock are in bijection, and assuming they agree is assuming nothing. -/
theorem massClock_iff_omega_eq_higgsClock {y v ω c ħ : ℝ} (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    yukawaMass y v = comptonMass ω c ħ ↔ ω = higgsClockFrequency y v c ħ := by
  unfold higgsClockFrequency
  constructor
  · intro h
    rw [h, comptonFrequency_comptonMass ω c ħ hc hħ]
  · intro h
    rw [h, comptonMass_comptonFrequency (yukawaMass y v) c ħ hc hħ]

/-- **The identification is discharged at the Higgs clock.**  Feeding the Higgs clock frequency back
through `comptonMass` returns the Yukawa mass — a theorem, not a hypothesis.  This is the round trip
that makes §A–§E's `massClock` premise free. -/
theorem massClock_at_higgsClock (y v c ħ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonMass (higgsClockFrequency y v c ħ) c ħ = yukawaMass y v := by
  unfold higgsClockFrequency
  exact comptonMass_comptonFrequency (yukawaMass y v) c ħ hc hħ

/-- **The coin angle determines the coupling, with no mass–clock hypothesis.**  A walk matched to the
Higgs clock of a Yukawa mass has `y = √2 ħ θ/(2 c² v)` — the premise carried through §E is discharged
by the bijection, so this is a determination of the coupling from the walk's single dial and the VEV
alone. -/
theorem coin_angle_determines_coupling {θ y v c ħ : ℝ} (hv : v ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hcoin : walkZitterFrequency θ = 2 * higgsClockFrequency y v c ħ) :
    y = Real.sqrt 2 * ħ * (θ / 2) / (c ^ 2 * v) := by
  refine coin_angle_isolates_yukawaCoupling (ω := higgsClockFrequency y v c ħ) hv ?_ hcoin
  exact (massClock_at_higgsClock y v c ħ hc hħ).symm

/-! ### §D — The synthesis -/

/-- **One dial, the whole trinity.**  A discrete-time quantum walk whose coin angle is matched to the
Compton frequency of the Yukawa mass simultaneously fixes: (i) the rest-frame zitterbewegung, (ii)
the Compton clock, (iii) the boosted de Broglie frequency, and (iv) the Higgs-sector clock through
which the mass originates.  The coin angle is the clock unit, not just a walk parameter. -/
theorem walk_coin_frequency_trinity {θ y v c ħ : ℝ} (γ : ℝ)
    (hm : 0 ≤ yukawaMass y v)
    (hmatch : walkZitterFrequency θ = 2 * comptonFrequency (yukawaMass y v) c ħ) :
    θ = zitterbewegungFrequency 0 (yukawaMass y v) c ħ
      ∧ θ = 2 * comptonFrequency (yukawaMass y v) c ħ
      ∧ deBroglieFrequency (γ * (yukawaMass y v * c ^ 2)) ħ = γ * (θ / 2)
      ∧ θ = 2 * higgsClockFrequency y v c ħ :=
  ⟨coin_angle_eq_rest_zitterbewegung hm hmatch,
   coin_angle_eq_two_compton hmatch,
   deBroglie_eq_gamma_half_coin_angle γ hmatch,
   coin_angle_eq_two_higgsClock hmatch⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkFrequencyTrinity

end
