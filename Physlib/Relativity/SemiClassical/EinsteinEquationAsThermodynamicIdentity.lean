/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity
public import Mathlib.Tactic.FieldSimp

meta import Zil

/-!
# Einstein's equation on a horizon is the first law

Kothawala, Sarkar and Padmanabhan, *Einstein's equations as a thermodynamic identity: the
cases of stationary axisymmetric horizons and evolving spherically symmetric horizons*,
Phys. Lett. B **652** (2007) 338.

The repository already proves the Kerr–Newman first law
(`NullLimitAmbiguity.kerrNewman_firstLaw`) the usual way, by differentiating the mass
function.  This module records the *other direction*, which is the paper's actual claim: the
Einstein equation **evaluated on the horizon**, multiplied by a virtual displacement of the
horizon radius, already **is** `T dS − dE = P dV`.  Nothing thermodynamic is assumed — the
temperature, entropy and energy are read off the field equation rather than imposed on it.

For the static spherically symmetric horizon of §2, with metric
`ds² = −f c²dt² + dr²/g + r²dΩ²` and a simple zero of `f` at `r = a`, the field equation
evaluated at the horizon is Eq. (3),

  `(c⁴/G)·(½ g'(a) a − ½) = 4π P a²`,

and `einstein_horizon_constraint_eq_firstLaw_rate` shows that its left-hand side is
*identically* `T·(dS/da) − dE/da` for

  `T = ℏ c g'(a)/(4π k_B)`,  `S = k_B c³ A /(4Għ)`,  `E = c⁴ a/(2G)`,

which are Eq. (5): the Bekenstein–Hawking entropy at the horizon area `A = 4πa²`, and the
Misner–Sharp energy.  `einstein_horizon_iff_firstLaw` then states the equivalence with the
right-hand side `P·(dV/da)`, `V = 4πa³/3`.

## The information reading

The paper's remark (a) is that `T dS` is completely classical — independent of `ℏ` — while
`T ∝ ℏ` and `S ∝ 1/ℏ` separately.  The repository's dimensional layer sharpens that: the
`ℏ` cancels but the **information charge does not**.  Under the holographic typing
(`[G] = ` area per bit) the entropy `k_B c³A/(4Għ)` is a *nat count*, exactly as
`RyuTakayanagi.rtAreaEntropy` and the Brown–Henneaux central charge measure, so the product
`T dS` carries the one nat that `dE` and `P dV` do not.  That is the same single nat that
`Meta.EntropicWepDepthGate` §22 finds in Jacobson's equation of state and §23 localizes on
the coupling: read as a thermodynamic identity, Einstein's equation is the statement that a
horizon displacement converts exactly one nat of boundary information into bulk energy.

**Honest layering.**  This is the algebraic core of §2 — the on-horizon field equation and its
virtual displacement — on scalar carriers.  The metric ansatz, the regularity conditions
`g(a) = 0`, `f'(a) = g'(a)`, and the surface-gravity computation that produces the temperature
are the paper's inputs, taken here as the definitions of the horizon data rather than derived
from a metric.  The evolving-horizon case of §3 and the Kerr–Newman case of §4 are not
formalized here; the latter's endpoint already exists in `NullLimitAmbiguity`.
-/

@[expose] public section

namespace Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity

open Real

/-- **Horizon temperature** `k_B T = ℏ c g'(a)/4π` (paper §2). -/
noncomputable def horizonTemperature (ℏ c kB gPrime : ℝ) : ℝ :=
  ℏ * c * gPrime / (4 * π * kB)

/-- **Horizon entropy** `S = k_B c³ A/(4Għ)` at area `A = 4πa²` — Eq. (5), the
Bekenstein–Hawking entropy in full units. -/
noncomputable def horizonEntropy (kB c ℏ G a : ℝ) : ℝ :=
  kB * c ^ 3 * (4 * π * a ^ 2) / (4 * (G * ℏ))

/-- **Misner–Sharp energy** `E = c⁴a/(2G)` — Eq. (5). -/
noncomputable def horizonEnergy (c G a : ℝ) : ℝ := c ^ 4 * a / (2 * G)

/-- `dS/da = 2π k_B c³ a/(Għ)`, the entropy's response to a virtual horizon displacement. -/
noncomputable def horizonEntropyRate (kB c ℏ G a : ℝ) : ℝ :=
  2 * π * kB * c ^ 3 * a / (G * ℏ)

/-- `dE/da = c⁴/(2G)`. -/
noncomputable def horizonEnergyRate (c G : ℝ) : ℝ := c ^ 4 / (2 * G)

/-- `dV/da = 4πa²` for `V = 4πa³/3`. -/
noncomputable def horizonVolumeRate (a : ℝ) : ℝ := 4 * π * a ^ 2

/-- **The left-hand side of the field equation is exactly `T dS − dE`.**  This is the paper's
Eq. (3) → Eq. (4) step, and it is an identity: no thermodynamic input is used, the `ℏ` of the
temperature cancels against the `ℏ` of the entropy, and what remains is the purely classical
combination `(c⁴/G)(½g'(a)a − ½)` that the Einstein equation sets equal to `4πPa²`. -/
theorem einstein_horizon_constraint_eq_firstLaw_rate
    (ℏ c kB G a gPrime : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hG : G ≠ 0) :
    horizonTemperature ℏ c kB gPrime * horizonEntropyRate kB c ℏ G a
        - horizonEnergyRate c G
      = c ^ 4 / G * (gPrime * a / 2 - 1 / 2) := by
  unfold horizonTemperature horizonEntropyRate horizonEnergyRate
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Einstein's equation on the horizon is the first law.**  The field equation evaluated at
the horizon, Eq. (3), holds if and only if the virtual displacement of the horizon satisfies
`T dS − dE = P dV`.  The thermodynamic quantities are *read off* the field equation, not
assumed: this is the sense in which gravitational dynamics near a horizon is already
thermodynamics. -/
theorem einstein_horizon_iff_firstLaw
    (ℏ c kB G a gPrime P : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hG : G ≠ 0) :
    c ^ 4 / G * (gPrime * a / 2 - 1 / 2) = P * horizonVolumeRate a
      ↔ horizonTemperature ℏ c kB gPrime * horizonEntropyRate kB c ℏ G a
          - horizonEnergyRate c G = P * horizonVolumeRate a := by
  rw [einstein_horizon_constraint_eq_firstLaw_rate ℏ c kB G a gPrime hℏ hkB hG]

/-- **The entropy is the horizon area in Planck units**: `S = k_B A/(4ℓ_P²)` with
`ℓ_P² = Għ/c³`, which is what makes `dS` a count of bits rather than a bookkeeping device. -/
theorem horizonEntropy_eq_area_over_four_planckAreas
    (kB c ℏ G a ℓP : ℝ) (hℓP : ℓP ^ 2 = G * ℏ / c ^ 3) (hG : G ≠ 0) (hℏ : ℏ ≠ 0)
    (hc : c ≠ 0) :
    horizonEntropy kB c ℏ G a = kB * (4 * π * a ^ 2) / (4 * ℓP ^ 2) := by
  unfold horizonEntropy
  rw [hℓP]
  field_simp

/-! ### §3 — evolving spherically symmetric horizons

The horizon `f(t, r_H) = 0` now moves.  There is no timelike Killing vector, so the surface
gravity is defined from the outward radial null generator in Painlevé–Gullstrand form
(Eqs. (7)–(11)); evaluating it on the horizon gives Eq. (12): `κ = g'(τ, r_H)/2`, carrying no
explicit time derivative even though `r_H(τ)` itself moves.  The temperature is `κ/2π`. -/

/-- **Evolving-horizon surface gravity** `κ = g'(τ, r_H)/2` — Eq. (12). -/
noncomputable def evolvingSurfaceGravity (gPrime : ℝ) : ℝ := gPrime / 2

/-- **Evolving-horizon temperature** `T = κ/2π = g'/4π` (natural units). -/
noncomputable def evolvingHorizonTemperature (gPrime : ℝ) : ℝ := gPrime / (4 * π)

/-- The evolving temperature is the surface gravity over `2π` — the same Unruh normalization
the static case uses, now for a horizon with no timelike Killing vector. -/
theorem evolvingHorizonTemperature_eq_surfaceGravity_div (gPrime : ℝ) :
    evolvingHorizonTemperature gPrime = evolvingSurfaceGravity gPrime / (2 * π) := by
  unfold evolvingHorizonTemperature evolvingSurfaceGravity; ring

/-- **Einstein's equation on an evolving horizon is the first law** — Eqs. (13) → (14).  The
on-horizon field equation `g'(r_H)/r_H − 1/r_H² = 8π T^r_r`, multiplied by `dr_H`, is exactly
`T dS − dE = P dV` for `S = π r_H²`, `V = 4π r_H³/3` and instantaneous Misner–Sharp energy
`E = r_H/2`.  The differentials now arise from the horizon's *evolution* rather than from
comparing two static solutions. -/
theorem evolving_einstein_iff_firstLaw (rH gPrime P : ℝ) (hrH : rH ≠ 0) :
    gPrime / rH - 1 / rH ^ 2 = 8 * π * P
      ↔ evolvingHorizonTemperature gPrime * (2 * π * rH) - 1 / 2
          = P * (4 * π * rH ^ 2) := by
  unfold evolvingHorizonTemperature
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  constructor
  · intro h; field_simp at h ⊢; nlinarith [h]
  · intro h; field_simp at h ⊢; nlinarith [h]

/-! ### §4 — Kerr–Newman: a stationary axisymmetric horizon

The horizon is no longer a 2-sphere.  Its surface gravity comes from the Killing vector
`ξ = t + Ω_H φ` via `κ² = −½ ξ^{α;β} ξ_{α;β}` (Eq. (20)), the area is `A = 4π(R²+a²)`
(Eq. (22)), and the temperature is Eq. (21). -/

/-- **Kerr–Newman horizon temperature** `T = f'(R)/(4π(R²+a²))` — Eq. (21). -/
noncomputable def kerrNewmanHorizonTemperature (fPrime R a : ℝ) : ℝ :=
  fPrime / (4 * π * (R ^ 2 + a ^ 2))

/-- **Kerr–Newman horizon entropy** `S = π(R²+a²)` — a quarter of the Eq. (22) area.  The
horizon is not a sphere; this is what replaces `πr²`. -/
noncomputable def kerrNewmanHorizonEntropy (R a : ℝ) : ℝ := π * (R ^ 2 + a ^ 2)

/-- **The on-horizon Einstein equation for Kerr–Newman**, Eqs. (28)–(29) combined: the
Einstein tensor seen by stationary observers, sourced by the Maxwell stress
`T^η̂_η̂ = −Q²/(8πρ⁴)`, reduces to `R² − R f'(R) − a² = Q²`.  The angular factor `ρ⁴` cancels
between the sides, which is why what survives is a relation among horizon parameters alone. -/
def kerrNewmanOnHorizonEinstein (fPrime R a Q : ℝ) : Prop :=
  R ^ 2 - R * fPrime - a ^ 2 = Q ^ 2

/-- **The Kerr–Newman first law is the on-horizon Einstein equation** — Eqs. (30) → (33), in
the radial direction.  With `M = (R²+a²+Q²)/(2R)` (the horizon condition solved for the mass),
`J = aM`, `Ω_H = a/(R²+a²)` and `Φ = RQ/(R²+a²)`, the identity `T dS = dM − Ω_H dJ − Φ dQ`
holds **exactly when** the field equation holds on the horizon.  Neither side is assumed: this
is an equivalence, and it carries the paper's claim to a horizon that is neither spherical nor
static. -/
theorem kerrNewman_einstein_iff_firstLaw_radial
    (fPrime R a Q : ℝ) (hR : R ≠ 0) (hRa : R ^ 2 + a ^ 2 ≠ 0) :
    kerrNewmanOnHorizonEinstein fPrime R a Q
      ↔ kerrNewmanHorizonTemperature fPrime R a * (2 * π * R)
          = (R ^ 2 - a ^ 2 - Q ^ 2) / (2 * R ^ 2) * (R ^ 2 / (R ^ 2 + a ^ 2)) := by
  unfold kerrNewmanOnHorizonEinstein kerrNewmanHorizonTemperature
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  constructor
  · intro h; field_simp; nlinarith [h]
  · intro h; field_simp at h; nlinarith [h]

/-- **The charge direction is automatically satisfied.**  Varying `Q` at fixed horizon radius
moves no entropy, and the mass and charge terms cancel identically, because
`(∂M/∂Q)(1 − Ω_H a) = QR/(R²+a²) = Φ`.  So the entire content of the first law sits in the
radial direction — where, by the theorem above, it *is* the field equation. -/
theorem kerrNewman_firstLaw_charge_direction (R a Q : ℝ) (hR : R ≠ 0)
    (hRa : R ^ 2 + a ^ 2 ≠ 0) :
    Q / R * (R ^ 2 / (R ^ 2 + a ^ 2)) - Q * R / (R ^ 2 + a ^ 2) = 0 := by
  field_simp
  ring

/-! ### Welds — this module's carriers are the repository's, not an island

The temperatures, entropies and potentials above must coincide with the carriers the
repository already owns (`Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity` for Kerr–Newman,
`SemiClassical.hawkingTemperature` for the static case), and the welds below prove they do.
The Kerr–Newman one is more than bookkeeping: the on-horizon Einstein equation turns out to
be *exactly* the statement that the metric-ansatz temperature agrees with the Unruh
temperature of the repository's Killing surface gravity. -/

/-- **The static temperature is the Hawking temperature** at surface gravity `κ = c²g'(a)/2`:
`ℏcg'(a)/(4πk_B) = ℏκ/(2πck_B)`. -/
theorem horizonTemperature_eq_hawkingTemperature (ℏ c kB gPrime : ℝ) :
    horizonTemperature ℏ c kB gPrime
      = hawkingTemperature ℏ (c ^ 2 * gPrime / 2) c kB := by
  unfold horizonTemperature hawkingTemperature
  by_cases hc : c = 0
  · simp [hc]
  · field_simp
    ring

/-- **The on-horizon Einstein equation is the equality of the two temperatures.**  The metric
temperature `f'(R)/(4π(R²+a²))` of Eq. (21) equals the Unruh reading
`kerrNewmanSurfaceGravity/(2π)` of the repository's Killing surface gravity
`κ = (R²−a²−Q²)/(2R(R²+a²))` **if and only if** the Maxwell-sourced constraint
`R² − Rf'(R) − a² = Q²` holds.  The field equation on the horizon *is* the calibration of the
metric clock to the Killing clock. -/
theorem kerrNewman_onHorizonEinstein_iff_temperature_eq_unruh
    (fPrime R a Q : ℝ) (hR : R ≠ 0) (hRa : R ^ 2 + a ^ 2 ≠ 0) :
    kerrNewmanOnHorizonEinstein fPrime R a Q
      ↔ kerrNewmanHorizonTemperature fPrime R a
          = Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanSurfaceGravity R a Q / (2 * π) := by
  unfold kerrNewmanOnHorizonEinstein kerrNewmanHorizonTemperature
    Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanSurfaceGravity
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  constructor
  · intro h
    field_simp
    nlinarith [h]
  · intro h
    field_simp at h
    nlinarith [h]

/-- **The Kerr–Newman entropy is a quarter of the repository's horizon area**:
`π(R²+a²) = kerrHorizonArea/4`. -/
theorem kerrNewmanHorizonEntropy_eq_area_quarter (R a : ℝ) :
    kerrNewmanHorizonEntropy R a = Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrHorizonArea R a / 4 := by
  unfold kerrNewmanHorizonEntropy Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrHorizonArea
  ring

/-- **The mass responds to charge at rate `Q/R`**: the actual derivative of the repository's
`kerrNewmanMass` in the charge direction at fixed horizon radius and spin. -/
theorem kerrNewmanMass_hasDerivAt_charge (R a Q : ℝ) (hR : R ≠ 0) :
    HasDerivAt (fun q => Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanMass R a q) (Q / R) Q := by
  unfold Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanMass
  have h := ((hasDerivAt_pow 2 Q).const_add (R ^ 2 + a ^ 2)).div_const (2 * R)
  refine h.congr_deriv ?_
  field_simp
  try ring

/-- **The charge-direction identity on named carriers**: the mass response `Q/R`, corrected by
the frame-dragging factor `1 − Ω_H a`, is exactly the repository's horizon electric potential.
This is the honest form of the cancellation: varying `Q` at fixed horizon geometry moves no
entropy, and produces no constraint beyond the definitions — but the electromagnetic sector
is *not* thereby empty: `Q²` sources the radial constraint, and `Φ` does work.  What vanishes
is only the charge direction's *independent* thermodynamic content. -/
theorem kerrNewman_charge_work_cancellation (R a Q : ℝ) (hR : R ≠ 0)
    (hRa : R ^ 2 + a ^ 2 ≠ 0) :
    Q / R * (1 - Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanAngularVelocity R a * a)
      = Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanElectricPotential R a Q := by
  unfold Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanAngularVelocity Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanElectricPotential
  field_simp
  ring

/- ZIL-BEGIN -/

zil attach Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.kerrNewman_onHorizonEinstein_iff_temperature_eq_unruh where
  formalizes @ "claim:the-on-horizon-kerr-newman-einstein-equation-holds-exactly-when-the-metric-ansatz-temperature-equals-the-unruh-reading-of-the-killing-surface-gravity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanSurfaceGravity"

zil attach Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.kerrNewman_charge_work_cancellation where
  formalizes @ "claim:the-charge-direction-of-the-kerr-newman-first-law-is-a-consistency-identity-on-the-repositorys-named-carriers-not-an-independent-constraint-and-not-a-claim-that-the-electromagnetic-sector-is-thermodynamically-empty",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanElectricPotential"

zil attach Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.einstein_horizon_iff_firstLaw where
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrHorizonArea_hasDerivAt",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewmanMass_hasDerivAt",
  discloses @ "lean:Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewman_firstLaw",
  formalizes @ "claim:einsteins-equation-evaluated-on-a-static-spherically-symmetric-horizon-holds-exactly-when-a-virtual-displacement-of-that-horizon-satisfies-the-first-law-t-ds-minus-de-equals-p-dv",
  derives @ "claim:the-horizon-temperature-entropy-and-energy-are-read-off-the-field-equation-rather-than-imposed-on-it",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:kothawala-sarkar-padmanabhan-2007-einsteins-equations-as-a-thermodynamic-identity-phys-lett-b-652-338",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NullLimitAmbiguity.kerrNewman_firstLaw",
  caveat @ "claim:the-metric-ansatz-the-horizon-regularity-conditions-and-the-surface-gravity-computation-are-the-papers-inputs-taken-here-as-the-definitions-of-the-horizon-data-not-derived-from-a-metric",
  caveat @ "claim:only-the-static-spherically-symmetric-warm-up-is-formalized-the-evolving-horizon-and-kerr-newman-cases-of-the-paper-are-not"

zil attach Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.einstein_horizon_constraint_eq_firstLaw_rate where
  formalizes @ "claim:the-classical-left-hand-side-of-the-on-horizon-field-equation-is-identically-the-temperature-times-the-entropy-rate-minus-the-energy-rate-with-the-hbar-of-the-temperature-cancelling-that-of-the-entropy",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity.horizonEntropy_eq_area_over_four_planckAreas where
  formalizes @ "claim:the-horizon-entropy-of-the-thermodynamic-identity-is-the-area-in-quarter-planck-areas-so-its-differential-counts-bits",
  epistemic_status @ "consistency-identity"

/- ZIL-END -/

end Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity

end
