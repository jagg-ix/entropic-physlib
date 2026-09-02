/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Convergence of canonical entropic-time routes

This module proves that candidate numerical routes to canonical entropic time,
defined in different parts of `physlib`, give the same scalar object under
explicit identification hypotheses.

* Bender lifetime `τ = ℏ/(2·Ṡ_I)` ↔ KMS thermal time
  `β = ℏ/(k_B·T)`.  Sections §A–§D.
* KMS thermal time ↔ ETH information-density time
  `τ_ent_canon = β_I·I/ℏ`.  Sections §E–§H.
* Bender ↔ ETH transitive corollary.  Section §I.
* ETH information-density time ↔ Page-Wootters
  clock-readout time `t_PW = clock reading`.  Sections §J–§L.
* KMS ↔ PW and Bender ↔ PW transitive corollaries.  Section §M.
* Connes-Rovelli thermal-time hypothesis at the scalar
  level — modular period `β_mod` ↔ KMS Planckian period.
  Sections §N–§Q.
* Aggregate canonical `τ_ent` — a single witness type
  `CanonicalTauWitness` to which all five routes contribute, with
  the uniqueness theorem that any two witnesses sharing the same
  `KMSScale` agree numerically.  Sections §R–§V.

## The two routes

* **Bender route** — `BenderIdentity.lifetimeFromRate`:
    `τ_Bender(ℏ, Ṡ_I) := ℏ / (2 · Ṡ_I)`
  A Gamow-state lifetime computed from the entropy-production rate
  `Ṡ_I = − Im E` of a complex-energy resonance.

* **KMS route** — `ThermoFieldDynamics.KMS.KMSScale.planckianPeriod`:
    `τ_KMS(k_B, T, ℏ) := ℏ / (k_B · T)`
  The Tomita-Takesaki modular period of a KMS thermal state at
  temperature `T`.

Algebraically the two are the same expression `ℏ / X` with
`X = 2 · Ṡ_I` in the first and `X = k_B · T` in the second.

## The identification hypothesis

`BenderKMSIdentification` is a `structure` that bundles a
`KMSScale` carrier, a Bender entropy-production rate, and the
single algebraic condition that pins the two routes together:

  `2 · Ṡ_I = k_B · T`.

Equivalently, the resonance width `Γ := 2 · Ṡ_I` equals the thermal
energy `k_B · T`.  Stated as a structure field, not a free-floating
hypothesis, so any downstream consumer must produce a witness.

## What this module does claim

Under the identification:

* `benderLifetime_eq_planckianPeriod` — `τ_Bender = τ_KMS`.
* `benderWidth_eq_thermal_scale` — `Γ = k_B · T`.
* `thermalRate_eq_benderTwoRate_over_ℏ` — `λ_th = 2·Ṡ_I/ℏ`.
* `planckianPeriod_mul_benderWidth_eq_ℏ` — `τ_KMS · Γ = ℏ` (which
  is the Bender `τ · Γ = ℏ` rewritten in KMS variables).

All four are one-step algebraic consequences of the identification.

## What this module does NOT claim

* That the identification `2 · Ṡ_I = k_B · T` holds in any specific
  physical system.  Two different objects — a Gamow-state imaginary
  energy and a thermal scale — are being asserted equal.  Whether
  any real material has this property is an empirical question that
  this module does not address.
* That `τ_ent` is the right physical time scale.  Route convergence
  is a precondition for the headline claim, not the claim itself.
  Even if all nine routes converge under their respective
  identification hypotheses, the empirical question (does the
  converged scale match measurements?) is independent.
* That the Bender lifetime and the KMS thermal period describe the
  same physical *process*.  The Bender lifetime is a decay
  exponential for a resonance state; the KMS thermal period is the
  modular automorphism period of a thermal equilibrium state.
  Their *numerical* coincidence under the identification does not
  make them physically the same.

## Connection to the wider program

This module hosts the route-convergence layer documented in
`Physlib.Optics.EntropicTimeOverview`: uniqueness of the scalar route value.
Neighboring files own the separate questions of classical reduction, sharp
prediction statements, empirical comparison, and closure.

## References

* Bender, Brody, Hook (2008) — see `BenderIdentity`.
* Hartnoll (2015) Planckian dissipation bound — see `ThermoFieldDynamics.KMS`.
* Connes, Rovelli (1994) thermal-time hypothesis — KMS modular
  period as physical time at temperature `T`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.RouteConvergence

open Physlib.QuantumMechanics.ComplexAction
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
open Physlib.Optics.TemporalDoubleSlit


/-- **Bender ↔ KMS identification carrier**.  Bundles a KMS scale
`K`, a Bender entropy-production rate `dSI_dt`, the positivity of
the rate, and the single algebraic identification
`2 · dSI_dt = K.kB · K.T`.

The identification asserts that the Bender resonance width
`Γ = 2 · dSI_dt` equals the thermal energy `k_B · T`.  This is the
condition under which the Bender lifetime equals the Planckian
period.

It is recorded as a `structure` (not a free-floating hypothesis) so
any consumer must produce a witness — including the empirical
content `thermal_match`. -/
structure BenderKMSIdentification where
  /-- KMS thermal scale: `(k_B, T, ℏ)` with positivities. -/
  K : KMSScale
  /-- Bender entropy-production rate `Ṡ_I`. -/
  dSI_dt : ℝ
  /-- The rate is strictly positive (we are in the decay regime,
  not the boring `Ṡ_I = 0` model). -/
  dSI_dt_pos : 0 < dSI_dt
  /-- **The identification**: the Bender resonance width equals
  the thermal energy.  Equivalent forms:
    * `2 · Ṡ_I = k_B · T`
    * `Γ = k_B · T`
    * `Ṡ_I = (k_B · T) / 2`. -/
  thermal_match : 2 * dSI_dt = K.kB * K.T

namespace BenderKMSIdentification

variable (id : BenderKMSIdentification)

/-- The product `kB · T` is positive (carried from `KMSScale`). -/
lemma kB_mul_T_pos : 0 < id.K.kB * id.K.T :=
  mul_pos id.K.kB_pos id.K.T_pos

/-- The product `kB · T` is nonzero. -/
lemma kB_mul_T_ne_zero : id.K.kB * id.K.T ≠ 0 :=
  ne_of_gt id.kB_mul_T_pos

/-- The rate is nonzero. -/
lemma dSI_dt_ne_zero : id.dSI_dt ≠ 0 := ne_of_gt id.dSI_dt_pos

/-- The doubled rate `2 · Ṡ_I` is positive. -/
lemma two_dSI_dt_pos : 0 < 2 * id.dSI_dt := by linarith [id.dSI_dt_pos]

/-- The doubled rate is nonzero. -/
lemma two_dSI_dt_ne_zero : 2 * id.dSI_dt ≠ 0 := ne_of_gt id.two_dSI_dt_pos

end BenderKMSIdentification

/-!

The Bender lifetime computed from `Ṡ_I` and the KMS Planckian period
computed from `(k_B, T)` are the *same number* whenever the
identification `2·Ṡ_I = k_B·T` holds and both sides share the same
`ℏ` (the `ℏ` of the supplied `KMSScale`). -/

/-- **A.1 main theorem** — Bender lifetime equals KMS Planckian
period under the thermal identification.

Both sides unfold to `ℏ / (2·Ṡ_I) = ℏ / (k_B·T)` and the rewrite
`thermal_match` makes them equal. -/
lemma benderLifetime_eq_planckianPeriod
    (id : BenderKMSIdentification) :
    lifetimeFromRate id.K.ℏ id.dSI_dt = id.K.planckianPeriod := by
  unfold lifetimeFromRate KMSScale.planckianPeriod planckianTime
  rw [id.thermal_match]

/-- **Width form** — the Bender resonance width equals the
thermal-energy scale.  This is the identification field itself,
restated using the named width function `widthFromRate`. -/
lemma benderWidth_eq_thermal_scale
    (id : BenderKMSIdentification) :
    widthFromRate id.dSI_dt = id.K.kB * id.K.T := by
  unfold widthFromRate
  exact id.thermal_match

/-- **Rate form** — the KMS thermal entropic rate `λ_th = k_B·T/ℏ`
equals the Bender double-rate ratio `2·Ṡ_I/ℏ`.  Algebraic
consequence of the identification. -/
lemma thermalRate_eq_benderTwoRate_over_ℏ
    (id : BenderKMSIdentification) :
    id.K.thermalRate = 2 * id.dSI_dt / id.K.ℏ := by
  unfold KMSScale.thermalRate thermalEntropicRate QuantumMechanics.FiniteTarget.kmsThermalRate
  rw [← id.thermal_match]

/-- **Duality form** — the Bender `τ · Γ = ℏ` identity rewritten in
KMS variables: `τ_KMS · Γ = ℏ`. Composes
`BenderIdentity.lifetime_mul_width` with the A.1 main theorem. -/
lemma planckianPeriod_mul_benderWidth_eq_ℏ
    (id : BenderKMSIdentification) :
    id.K.planckianPeriod * widthFromRate id.dSI_dt = id.K.ℏ := by
  rw [← benderLifetime_eq_planckianPeriod id]
  exact lifetime_mul_width id.K.ℏ id.dSI_dt id.dSI_dt_ne_zero

/-!

Whichever direction one comes from, the converged scale is positive.
This is a small lemma but worth recording because the headline claim
"τ_ent is a time" already assumes positivity. -/

/-- **Bender lifetime is positive** under the identification.
Follows from `BenderIdentity.lifetime_pos` with the rate positivity
field of the identification and the `ℏ` positivity of the KMS scale. -/
lemma benderLifetime_pos (id : BenderKMSIdentification) :
    0 < lifetimeFromRate id.K.ℏ id.dSI_dt :=
  lifetime_pos id.K.ℏ_pos id.dSI_dt_pos

/-- **Equal-positivity** — the two positivity statements
`0 < τ_Bender` and `0 < τ_KMS` reduce to each other under the
identification.  Recorded as an `iff` for symmetry of use. -/
lemma benderLifetime_pos_iff_planckianPeriod_pos
    (id : BenderKMSIdentification) :
    0 < lifetimeFromRate id.K.ℏ id.dSI_dt ↔
      0 < id.K.planckianPeriod := by
  rw [benderLifetime_eq_planckianPeriod id]

/-!

Given a `KMSScale`, the identification can be solved for `Ṡ_I`:
set `Ṡ_I := k_B · T / 2`.  This shows the identification is always
*satisfiable* — for any thermal scale there is a Bender rate that
matches.  It does *not* show the resulting `Ṡ_I` corresponds to a
physical resonance in any particular system. -/

/-- **Witness construction** — from a `KMSScale` produce the
`BenderKMSIdentification` with `Ṡ_I := k_B · T / 2`. -/
def ofKMSScale (K : KMSScale) : BenderKMSIdentification where
  K := K
  dSI_dt := K.kB * K.T / 2
  dSI_dt_pos := by
    have h := mul_pos K.kB_pos K.T_pos
    linarith
  thermal_match := by ring

/-- **Consistency** — `ofKMSScale K` preserves `K`. -/
@[simp] lemma ofKMSScale_K (K : KMSScale) :
    (ofKMSScale K).K = K := rfl

/-- **Consistency** — the rate field of `ofKMSScale K` is `k_B·T/2`. -/
@[simp] lemma ofKMSScale_dSI_dt (K : KMSScale) :
    (ofKMSScale K).dSI_dt = K.kB * K.T / 2 := rfl

/-!

The ETH (Eigenstate Thermalization Hypothesis) "canonical
entropic time" has the published shape

  `τ_ent_canon := β_I · I / ℏ`

where `β_I` is an inverse-temperature-like real parameter and
`I` is the value of an information-density functional at the
phase-space point of interest (D'Alessio et al. 2016 review of
ETH and quantum thermalization; standard canonical form).
This module defines a standalone physlib carrier of that shape.

**External-origin disclaimer.**  An external Lean development
(outside physlib, no dependency from here) provides an
alternate version of the same construction labelled
`canonicalTauDiag`; the two are by inspection the same
algebraic expression, but physlib carries no import dependency
on that external code. -/

/-- **ETH information-density scale**.  Carries `(β_I, I, ℏ)`
with positivities.  The canonical entropic time is
`canonicalTau := β_I · I / ℏ`. -/
structure ETHInformationScale where
  /-- Inverse-temperature-like parameter (β_I). -/
  β_I : ℝ
  /-- Information-density value at the point of interest. -/
  I_dens : ℝ
  /-- Reduced Planck constant (J·s). -/
  ℏ : ℝ
  /-- `β_I > 0`. -/
  β_I_pos : 0 < β_I
  /-- `I > 0` — the information density is nonzero at the point. -/
  I_dens_pos : 0 < I_dens
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ

namespace ETHInformationScale

variable (E : ETHInformationScale)

/-- **Canonical entropic time** from information density:
`τ_ent_canon := β_I · I / ℏ`.  Standard ETH canonical form
(D'Alessio et al. 2016). -/
def canonicalTau : ℝ := E.β_I * E.I_dens / E.ℏ

/-- **Canonical entropic time is positive** — follows from the
three positivity fields. -/
lemma canonicalTau_pos : 0 < E.canonicalTau := by
  unfold canonicalTau
  exact div_pos (mul_pos E.β_I_pos E.I_dens_pos) E.ℏ_pos

end ETHInformationScale


/-- **KMS ↔ ETH identification carrier**.  Bundles a KMS scale `K`,
an ETH information-density scale `E`, and two algebraic identifications:

* `ℏ_match` — the two `ℏ` fields agree (both routes use the same
  Planck constant).
* `info_match` — `β_I · I = K.ℏ · K.planckianPeriod`.

The second condition is the algebraic pin-down: under it, the ETH
canonical entropic time at the chosen phase-space point equals the
KMS Planckian period.

Stated as a structure field, not a free-floating hypothesis, so any
consumer must produce both witnesses.  In particular the consumer
asserts that *the system at hand* has an information-density value
matching the thermal scale — this is an empirical input. -/
structure KMSETHIdentification where
  /-- KMS thermal scale. -/
  K : KMSScale
  /-- ETH information-density scale. -/
  E : ETHInformationScale
  /-- The two `ℏ` fields agree. -/
  ℏ_match : E.ℏ = K.ℏ
  /-- **The identification**: `β_I · I = ℏ · τ_KMS`.

  Equivalent forms (each derivable from this one):
    * `β_I · I / ℏ = K.planckianPeriod`
    * `β_I · I · k_B · T = ℏ²`. -/
  info_match : E.β_I * E.I_dens = K.ℏ * K.planckianPeriod


/-- **A.2 main theorem** — the ETH canonical entropic time equals
the KMS Planckian period under the identification.

Algebraically: both sides equal `K.ℏ · K.planckianPeriod / K.ℏ =
K.planckianPeriod`. -/
lemma canonicalTau_eq_planckianPeriod
    (id : KMSETHIdentification) :
    id.E.canonicalTau = id.K.planckianPeriod := by
  unfold ETHInformationScale.canonicalTau
  rw [id.info_match, id.ℏ_match]
  exact mul_div_cancel_left₀ _ (ne_of_gt id.K.ℏ_pos)

/-- **Equivalent restatement** — the identification condition
`β_I · I = ℏ · τ_KMS` can be rewritten as
`β_I · I / ℏ = τ_KMS`.  This is the form in which the canonical
ETH τ_ent appears in the literature (D'Alessio et al. 2016). -/
lemma info_match_div_ℏ
    (id : KMSETHIdentification) :
    id.E.β_I * id.E.I_dens / id.E.ℏ = id.K.planckianPeriod := by
  rw [id.info_match, id.ℏ_match]
  exact mul_div_cancel_left₀ _ (ne_of_gt id.K.ℏ_pos)


/-- **Equal-positivity for A.2** — the two positivity statements
`0 < τ_ETH_canon` and `0 < τ_KMS` reduce to each other under the
identification. -/
lemma canonicalTau_pos_iff_planckianPeriod_pos
    (id : KMSETHIdentification) :
    0 < id.E.canonicalTau ↔ 0 < id.K.planckianPeriod := by
  rw [canonicalTau_eq_planckianPeriod id]

namespace KMSETHIdentification

/-- **Witness construction** — from a `KMSScale` produce a
`KMSETHIdentification` with `β_I := K.planckianPeriod` and
`I := K.ℏ`.  Then `β_I · I = K.planckianPeriod · K.ℏ` as required.

This is the simplest witness; it does *not* claim physical
relevance, only that the identification is at least *satisfiable*
for every thermal scale. -/
def ofKMSScale (K : KMSScale) : KMSETHIdentification where
  K := K
  E := {
    β_I := K.planckianPeriod
    I_dens := K.ℏ
    ℏ := K.ℏ
    β_I_pos := K.planckianPeriod_pos
    I_dens_pos := K.ℏ_pos
    ℏ_pos := K.ℏ_pos }
  ℏ_match := rfl
  info_match := by ring

/-- **Consistency** — `ofKMSScale K` preserves `K`. -/
@[simp] lemma ofKMSScale_K (K : KMSScale) :
    (ofKMSScale K).K = K := rfl

end KMSETHIdentification

/-!

Combining A.1 (`τ_Bender = τ_KMS`) and A.2 (`τ_ETH_canon = τ_KMS`)
gives `τ_Bender = τ_ETH_canon` whenever the two identifications
share the same `KMSScale`.  Stated as a corollary parametrised by
two identification carriers plus the matching condition. -/

/-- **Bender ↔ ETH equality** — assuming the Bender ↔ KMS and
KMS ↔ ETH identifications use the same `KMSScale`, the Bender
Gamow-state lifetime equals the ETH canonical entropic time.

This is the simplest two-step convergence in the program: three
formally distinct routes (Bender complex-energy, KMS thermal,
ETH information-density) all yield the same numerical scale
under hypothesis composition.  As before, whether any specific
physical system satisfies both identifications simultaneously is
an empirical question outside this module. -/
lemma benderLifetime_eq_canonicalTau
    (idBK : BenderKMSIdentification)
    (idKE : KMSETHIdentification)
    (h : idBK.K = idKE.K) :
    lifetimeFromRate idBK.K.ℏ idBK.dSI_dt = idKE.E.canonicalTau := by
  rw [benderLifetime_eq_planckianPeriod idBK]
  rw [h]
  rw [← canonicalTau_eq_planckianPeriod idKE]

/-!

The Page-Wootters mechanism (Page-Wootters 1983; Giovannetti-Lloyd-
Maccone 2015) makes time relational: the universe is divided into a
clock subsystem and a system subsystem, and the system's evolution
is governed by Schrödinger's equation parametrised by the *clock
readout*.  For a system energy eigenstate of eigenvalue `E_S`, the
phase accumulated when the clock reads `t` is

  `phaseS(t) := −E_S · t / ℏ`.

In `physlib`, the full Page-Wootters operator-level mechanism lives
in `Physlib.QuantumMechanics.RelationalTime.PageWootters`
(`HamiltonianConstraint`, `EffectiveClockHamiltonian`).  The
scalar-level phase identity already appears in `BenderIdentity` as
`benderPhase E_R t ℏ := −(E_R · t)/ℏ`.  This section adds the minimal
scalar carrier that lets us state the A.3 identification with the
ETH route: a clock readout `t`, a system energy `E_S`, and the
shared `ℏ`. -/

/-- **Page-Wootters scalar scale**.  Carries a clock readout `t`,
a system energy eigenvalue `E_S`, and `ℏ`.  The system phase at
clock reading `t` is `phaseS := −E_S · t / ℏ`.

Captures only the scalar phase aspect of the Page-Wootters
mechanism — the full operator-level construction is in
`Physlib.QuantumMechanics.RelationalTime.PageWootters`. -/
structure PageWoottersScale where
  /-- Clock readout (the "physical time"). -/
  t   : ℝ
  /-- System energy eigenvalue. -/
  E_S : ℝ
  /-- Reduced Planck constant (J·s). -/
  ℏ   : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ

namespace PageWoottersScale

variable (PW : PageWoottersScale)

/-- **System phase** at clock reading `t`: `phaseS := −E_S · t / ℏ`.
Same algebraic shape as `BenderIdentity.benderPhase`.  Recorded
here as a method on `PageWoottersScale` for use inside this
module's identification theorems. -/
def systemPhase : ℝ := benderPhase PW.E_S PW.t PW.ℏ

/-- **Unfolding** — `systemPhase = −E_S · t / ℏ`. -/
lemma systemPhase_def : PW.systemPhase = -(PW.E_S * PW.t) / PW.ℏ := rfl

end PageWoottersScale


/-- **ETH ↔ Page-Wootters identification carrier**.  Bundles an ETH
information-density scale `E`, a Page-Wootters scale `PW`, and two
algebraic identifications:

* `ℏ_match` — the two `ℏ` fields agree.
* `time_match` — `PW.t = E.canonicalTau`.

The second condition is the Page-Wootters–ETH agreement: the clock
readout (Page-Wootters "physical time") equals the ETH canonical
entropic time at the phase-space point of interest.

Stated as a structure field so the consumer must produce both
witnesses.  This is an empirical assertion — that the clock subsystem
in a Page-Wootters split actually reads out the ETH information-
density time — not a derived theorem. -/
structure ETHClockIdentification where
  /-- ETH information-density scale. -/
  E  : ETHInformationScale
  /-- Page-Wootters scalar scale. -/
  PW : PageWoottersScale
  /-- The two `ℏ` fields agree. -/
  ℏ_match : PW.ℏ = E.ℏ
  /-- **The identification**: clock readout equals ETH canonical
  entropic time. -/
  time_match : PW.t = E.canonicalTau


/-- **A.3 main theorem** — the Page-Wootters clock readout equals
the ETH canonical entropic time under the identification.  This is
the identification itself rephrased as a theorem on the carrier. -/
lemma clockReadout_eq_canonicalTau
    (id : ETHClockIdentification) :
    id.PW.t = id.E.canonicalTau := id.time_match

/-- **A.3 phase consequence** — under the identification, the
Page-Wootters system phase equals the ETH-determined phase
`−E_S · τ_ent_canon / ℏ`.

This is the substantive A.3 statement: not just an algebraic
relabelling of one real number, but a structural agreement between
the two routes' phase prescriptions.  Both sides reduce to
`−E_S · β_I · I / ℏ²` after unfolding. -/
lemma systemPhase_eq_eth_phase
    (id : ETHClockIdentification) :
    id.PW.systemPhase = -(id.PW.E_S * id.E.canonicalTau) / id.E.ℏ := by
  unfold PageWoottersScale.systemPhase benderPhase
  rw [id.time_match, id.ℏ_match]

/-- **Fully expanded form** — the Page-Wootters system phase
expanded in ETH parameters: `−E_S · β_I · I / ℏ²`. -/
lemma systemPhase_eq_eth_expanded
    (id : ETHClockIdentification) :
    id.PW.systemPhase =
      -(id.PW.E_S * (id.E.β_I * id.E.I_dens)) / (id.E.ℏ * id.E.ℏ) := by
  rw [systemPhase_eq_eth_phase id]
  unfold ETHInformationScale.canonicalTau
  field_simp

/-!

Combining A.2 and A.3 gives the Page-Wootters clock readout as the
KMS Planckian period under composed identifications.  Combining
A.1, A.2, and A.3 gives the Page-Wootters clock readout as the
Bender Gamow-state lifetime.

Each corollary requires that the shared carriers (KMS scale on the
left, ETH scale on the right) match across the two identifications.
-/

/-- **KMS ↔ PW** — the Page-Wootters clock readout equals the KMS
Planckian period when the ETH ↔ PW and KMS ↔ ETH identifications
share the same ETH scale. -/
lemma clockReadout_eq_planckianPeriod
    (idKE : KMSETHIdentification)
    (idEP : ETHClockIdentification)
    (h : idKE.E = idEP.E) :
    idEP.PW.t = idKE.K.planckianPeriod := by
  rw [idEP.time_match, ← h]
  exact canonicalTau_eq_planckianPeriod idKE

/-- **Bender ↔ PW** — the Page-Wootters clock readout equals the
Bender Gamow-state lifetime when all three identifications chain
together (Bender↔KMS, KMS↔ETH, ETH↔PW) through matching shared
scales.

Four formally distinct routes (Bender complex-energy, KMS thermal,
ETH information-density, Page-Wootters relational time) all yield
the same numerical scale under hypothesis composition.  As at every
prior step, whether any specific physical system satisfies all
three identifications simultaneously is an empirical question
outside this module. -/
lemma clockReadout_eq_benderLifetime
    (idBK : BenderKMSIdentification)
    (idKE : KMSETHIdentification)
    (idEP : ETHClockIdentification)
    (hK : idBK.K = idKE.K)
    (hE : idKE.E = idEP.E) :
    idEP.PW.t = lifetimeFromRate idBK.K.ℏ idBK.dSI_dt := by
  rw [benderLifetime_eq_canonicalTau idBK idKE hK, idEP.time_match, ← hE]

/-!

Tomita-Takesaki theory (Takesaki 1970) associates to a faithful
normal state `ω` on a von Neumann algebra a one-parameter
automorphism group `σ_t` (the modular automorphism) and a modular
operator `Δ` such that `Δ^{it}` implements `σ_t`.  At a KMS state
of inverse temperature `β`, the modular automorphism is the
thermal time evolution (Connes-Rovelli 1994 thermal time
hypothesis).

**External-origin disclaimer.**  Physlib's lakefile depends only
on Mathlib + doc-gen4.  The full operator-level Tomita-Takesaki
construction (`Δ^{it}` unitary, the proved theorem
`(Δ^{it})* = Δ^{−it}`, and its composition into the KMS bridge)
is the published mathematical content of Takesaki 1970, with a
formal Lean development carried separately in an external
codebase (no dependency from physlib).  This section carries
only the **scalar-level shadow** of the Connes-Rovelli
identification: a real number `β_mod` ("modular period") plus
the assertion that it equals the KMS Planckian period.

That assertion is what the operator-level theorem reduces to
once projected to the numerical period, so the scalar-level
identification is consistent with — and a necessary consequence
of — the operator-level theorem (Takesaki 1970, Connes-Rovelli
1994).  The full operator-level claim (modular automorphism
`σ_t` IS physical time evolution at a KMS state) is not provable
inside physlib's dependency surface; the scalar-level claim
(modular period equals thermal period) is. -/

/-- **Modular-flow scalar scale**.  Carries `(β_mod, ℏ)` with
positivities.  `β_mod` is the period of the modular automorphism
group `σ_t` at a KMS state, as a real number.  The operator-level
content of the Tomita-Takesaki theorem `(Δ^{it})* = Δ^{−it}` is
published in Takesaki 1970; physlib carries no dependency on any
external Lean formalisation of it. -/
structure ModularFlowScale where
  /-- Modular period (Tomita-Takesaki). -/
  β_mod : ℝ
  /-- Reduced Planck constant (J·s). -/
  ℏ     : ℝ
  /-- `β_mod > 0`. -/
  β_mod_pos : 0 < β_mod
  /-- `ℏ > 0`. -/
  ℏ_pos     : 0 < ℏ

namespace ModularFlowScale

variable (M : ModularFlowScale)

/-- The modular period is positive. -/
lemma β_mod_ne_zero : M.β_mod ≠ 0 := ne_of_gt M.β_mod_pos

end ModularFlowScale

/-!

The Connes-Rovelli 1994 thermal-time hypothesis identifies the
modular automorphism of a KMS state with physical time evolution at
temperature `T`.  At the scalar level, this reduces to the equality
of two real numbers: the modular period `β_mod` and the KMS
Planckian period `β = ℏ/(k_B·T)`.

This section carries that scalar-level identification as a
`structure` and records the trivial theorem that the two periods
are equal under the assumption. -/

/-- **KMS ↔ Modular identification carrier**.  Bundles a KMS scale
`K`, a modular-flow scale `M`, and two algebraic identifications:

* `ℏ_match` — the two `ℏ` fields agree.
* `period_match` — `M.β_mod = K.planckianPeriod`.

The second condition is the Connes-Rovelli scalar identification.
Stated as a structure field so any consumer must produce both
witnesses.  In particular, the consumer asserts that the modular
period of *its system's* KMS state at temperature `T` equals
`ℏ/(k_B·T)` — this is the operator-level Tomita-Takesaki result,
projected to its scalar value. -/
structure KMSModularIdentification where
  /-- KMS thermal scale. -/
  K : KMSScale
  /-- Modular-flow scalar scale. -/
  M : ModularFlowScale
  /-- The two `ℏ` fields agree. -/
  ℏ_match : M.ℏ = K.ℏ
  /-- **The identification**: modular period equals KMS Planckian
  period.  Equivalent at the scalar level to the Connes-Rovelli
  1994 thermal-time hypothesis. -/
  period_match : M.β_mod = K.planckianPeriod

/-- **A.4 main theorem** — the modular period equals the KMS
Planckian period under the identification.  Restatement of the
`period_match` field as a theorem. -/
lemma modularPeriod_eq_planckianPeriod
    (id : KMSModularIdentification) :
    id.M.β_mod = id.K.planckianPeriod := id.period_match


/-- **Equal-positivity for A.4** — modular and Planckian
positivities reduce to each other under the identification. -/
lemma modularPeriod_pos_iff_planckianPeriod_pos
    (id : KMSModularIdentification) :
    0 < id.M.β_mod ↔ 0 < id.K.planckianPeriod := by
  rw [id.period_match]

namespace KMSModularIdentification

/-- **Witness construction** — from a `KMSScale` produce the
`KMSModularIdentification` with `β_mod := K.planckianPeriod`.

This is the simplest witness; it shows the scalar-level
Connes-Rovelli identification is at least *satisfiable* for every
thermal scale.  The substantive claim — that a particular system's
modular period actually equals its Planckian period — is the
operator-level Tomita-Takesaki theorem (Takesaki 1970,
Connes-Rovelli 1994), whose Lean formalisation lives outside
physlib's dependency surface. -/
def ofKMSScale (K : KMSScale) : KMSModularIdentification where
  K := K
  M := {
    β_mod := K.planckianPeriod
    ℏ := K.ℏ
    β_mod_pos := K.planckianPeriod_pos
    ℏ_pos := K.ℏ_pos }
  ℏ_match := rfl
  period_match := rfl

/-- **Consistency** — `ofKMSScale K` preserves `K`. -/
@[simp] lemma ofKMSScale_K (K : KMSScale) :
    (ofKMSScale K).K = K := rfl

/-- **Consistency** — the modular period of `ofKMSScale K` is
`K.planckianPeriod`. -/
@[simp] lemma ofKMSScale_β_mod (K : KMSScale) :
    (ofKMSScale K).M.β_mod = K.planckianPeriod := rfl

end KMSModularIdentification

/-!

The Connes-Rovelli scalar identification composes with A.1, A.2,
and A.3 to give five-route convergence: under hypothesis composition
through matching shared scales, the modular period equals the
Bender Gamow-state lifetime, the ETH canonical entropic time, and
the Page-Wootters clock readout.

Each corollary requires that the relevant shared carriers
(`KMSScale` or `ETHInformationScale`) match across the two
identifications. -/

/-- **Modular ↔ Bender** — the modular period equals the Bender
Gamow-state lifetime when the two identifications share the same
`KMSScale`. -/
lemma modularPeriod_eq_benderLifetime
    (idBK : BenderKMSIdentification)
    (idKM : KMSModularIdentification)
    (h : idBK.K = idKM.K) :
    idKM.M.β_mod = lifetimeFromRate idBK.K.ℏ idBK.dSI_dt := by
  rw [idKM.period_match, ← h]
  exact (benderLifetime_eq_planckianPeriod idBK).symm

/-- **Modular ↔ ETH** — the modular period equals the ETH canonical
entropic time when the two identifications share the same
`KMSScale`. -/
lemma modularPeriod_eq_canonicalTau
    (idKE : KMSETHIdentification)
    (idKM : KMSModularIdentification)
    (h : idKE.K = idKM.K) :
    idKM.M.β_mod = idKE.E.canonicalTau := by
  rw [idKM.period_match, ← h]
  exact (canonicalTau_eq_planckianPeriod idKE).symm

/-- **Modular ↔ PW** — the modular period equals the Page-Wootters
clock readout under composed identifications (KMS↔Modular and
ETH↔PW, sharing the matching scales). -/
lemma modularPeriod_eq_clockReadout
    (idKE : KMSETHIdentification)
    (idEP : ETHClockIdentification)
    (idKM : KMSModularIdentification)
    (hK : idKE.K = idKM.K)
    (hE : idKE.E = idEP.E) :
    idKM.M.β_mod = idEP.PW.t := by
  rw [modularPeriod_eq_canonicalTau idKE idKM hK, hE, ← idEP.time_match]

/-!

A.1–A.4 each prove that one specific route's numerical output equals
`K.planckianPeriod` for the shared `KMSScale K`.  Section A.5
packages this into a single aggregate carrier: a `KMSScale`, a real
number called the *canonical entropic time*, and a proved equality
between the two.

Any of the five routes (Bender, KMS, ETH, Page-Wootters, modular
flow) produces a `CanonicalTauWitness` via the corresponding
constructor.  Two witnesses built from any combination of routes,
sharing the same `KMSScale`, agree numerically by the uniqueness
theorem in §T.

The canonical entropic time is therefore well-defined relative to a
`KMSScale`: independent of which route was used to derive it, under
the identification hypotheses required by each route. -/

/-- **Aggregate canonical entropic time witness**.  Carries a
`KMSScale`, a real number `τ_ent` interpreted as the canonical
entropic time of that scale, and a proved equality
`τ_ent = K.planckianPeriod`.

Constructed from any of the five routes via the `of*` lemmas in
§S.  Two witnesses sharing the same `KMSScale` agree numerically
(§T `eq_of_same_K`). -/
structure CanonicalTauWitness where
  /-- KMS thermal scale supplying the canonical numerical value. -/
  K : KMSScale
  /-- The canonical entropic time. -/
  τ_ent : ℝ
  /-- **The defining equality**: the canonical entropic time
  numerically equals the KMS Planckian period of `K`.  Every
  route's constructor in §S supplies this proof from its own
  route-level identification. -/
  matches_planckian : τ_ent = K.planckianPeriod


namespace CanonicalTauWitness

/-- **KMS-route constructor** — every `KMSScale` produces a
canonical witness by taking `τ_ent := K.planckianPeriod` directly. -/
def ofKMS (K : KMSScale) : CanonicalTauWitness where
  K := K
  τ_ent := K.planckianPeriod
  matches_planckian := rfl

/-- **Bender-route constructor** — a Bender ↔ KMS identification
produces a canonical witness with `τ_ent := τ_Bender = ℏ/(2·Ṡ_I)`. -/
def ofBender (idBK : BenderKMSIdentification) : CanonicalTauWitness where
  K := idBK.K
  τ_ent := lifetimeFromRate idBK.K.ℏ idBK.dSI_dt
  matches_planckian := benderLifetime_eq_planckianPeriod idBK

/-- **ETH-route constructor** — a KMS ↔ ETH identification produces
a canonical witness with `τ_ent := τ_ent_canon = β_I·I/ℏ`. -/
def ofETH (idKE : KMSETHIdentification) : CanonicalTauWitness where
  K := idKE.K
  τ_ent := idKE.E.canonicalTau
  matches_planckian := canonicalTau_eq_planckianPeriod idKE

/-- **Page-Wootters-route constructor** — a chained KMS↔ETH and
ETH↔PW identification (sharing the same ETH scale) produces a
canonical witness with `τ_ent := t_PW = clock reading`. -/
def ofPW
    (idKE : KMSETHIdentification)
    (idEP : ETHClockIdentification)
    (hE : idKE.E = idEP.E) : CanonicalTauWitness where
  K := idKE.K
  τ_ent := idEP.PW.t
  matches_planckian := clockReadout_eq_planckianPeriod idKE idEP hE

/-- **Modular-route constructor** — a KMS ↔ Modular identification
produces a canonical witness with `τ_ent := β_mod` (modular period). -/
def ofModular (idKM : KMSModularIdentification) : CanonicalTauWitness where
  K := idKM.K
  τ_ent := idKM.M.β_mod
  matches_planckian := idKM.period_match


/-- **A.5 uniqueness theorem** — any two canonical-τ witnesses
sharing the same `KMSScale` give the same numerical `τ_ent`.

This formalises **part (i) of the headline claim** (uniqueness):
under matching `KMSScale`, the five-route convergence collapses to
a single number, independent of which route was used.

It does *not* establish parts (ii) reduction or (iii) discrimination
— those are Phases B and E.  Whether any specific physical system
has *all* the matching scales' identifications satisfied (so that
its actual physical time scale agrees with any of the routes) is
an empirical question outside the module. -/
lemma eq_of_same_K
    (w₁ w₂ : CanonicalTauWitness) (h : w₁.K = w₂.K) :
    w₁.τ_ent = w₂.τ_ent := by
  rw [w₁.matches_planckian, h, w₂.matches_planckian]

/-- **Cross-route corollary** — applied to two witnesses built
from different routes but the same `KMSScale`.  Spells out the
ten pairwise equalities that follow from `eq_of_same_K`. -/
lemma bender_eq_eth
    (idBK : BenderKMSIdentification)
    (idKE : KMSETHIdentification)
    (h : idBK.K = idKE.K) :
    (ofBender idBK).τ_ent = (ofETH idKE).τ_ent :=
  eq_of_same_K _ _ h

/-- Symmetric companion to `bender_eq_eth`. -/
lemma bender_eq_pw
    (idBK : BenderKMSIdentification)
    (idKE : KMSETHIdentification)
    (idEP : ETHClockIdentification)
    (hK : idBK.K = idKE.K)
    (_hE : idKE.E = idEP.E) :
    (ofBender idBK).τ_ent = (ofPW idKE idEP _hE).τ_ent :=
  eq_of_same_K _ _ hK

/-- Symmetric companion to `bender_eq_pw`. -/
lemma bender_eq_modular
    (idBK : BenderKMSIdentification)
    (idKM : KMSModularIdentification)
    (h : idBK.K = idKM.K) :
    (ofBender idBK).τ_ent = (ofModular idKM).τ_ent :=
  eq_of_same_K _ _ h

/-- ETH ↔ PW collapse via the canonical witness. -/
lemma eth_eq_pw
    (idKE : KMSETHIdentification)
    (idEP : ETHClockIdentification)
    (hE : idKE.E = idEP.E) :
    (ofETH idKE).τ_ent = (ofPW idKE idEP hE).τ_ent :=
  eq_of_same_K _ _ rfl

/-- ETH ↔ Modular collapse via the canonical witness. -/
lemma eth_eq_modular
    (idKE : KMSETHIdentification)
    (idKM : KMSModularIdentification)
    (h : idKE.K = idKM.K) :
    (ofETH idKE).τ_ent = (ofModular idKM).τ_ent :=
  eq_of_same_K _ _ h

/-- PW ↔ Modular collapse via the canonical witness. -/
lemma pw_eq_modular
    (idKE : KMSETHIdentification)
    (idEP : ETHClockIdentification)
    (idKM : KMSModularIdentification)
    (hK : idKE.K = idKM.K)
    (hE : idKE.E = idEP.E) :
    (ofPW idKE idEP hE).τ_ent = (ofModular idKM).τ_ent :=
  eq_of_same_K _ _ hK


/-- **Canonical τ_ent is positive** — follows from the equality
with `K.planckianPeriod` and the latter's positivity. -/
lemma τ_ent_pos (w : CanonicalTauWitness) : 0 < w.τ_ent := by
  rw [w.matches_planckian]
  exact w.K.planckianPeriod_pos

end CanonicalTauWitness

/-!

**Proved (formal Lean theorems on this branch):**

1. `τ_Bender`, `τ_KMS`, `τ_ETH`, `t_PW`, and `β_mod` are pairwise
   equal as real numbers under their respective identification hypotheses.
2. Any aggregate `CanonicalTauWitness` derived from any of the five
   routes, sharing the same `KMSScale`, yields the same `τ_ent`.
3. Positivity of `τ_ent` follows from `KMSScale.planckianPeriod_pos`.

**Not proved in this module:**

1. That the identification hypotheses (`2·Ṡ_I = k_B·T`, `β_I·I =
   ℏ·τ_KMS`, `t_PW = τ_ent_canon`, `β_mod = τ_KMS`) hold in any
   specific physical system.  They are asserted as `structure`
   fields, not derived from microscopic physics.
2. That the canonical `τ_ent` reduces to coordinate time `t` in a
   classical/decoherence limit.
3. That the canonical `τ_ent` correctly predicts any measured
   observable.
4. That there exists an experiment whose τ_ent prediction
   distinguishes the framework from coordinate-time-only QM.
5. The operator-level Connes-Rovelli theorem (modular automorphism
   is physical time at a KMS state).  Published in Takesaki 1970
   and Connes-Rovelli 1994; a formal Lean development lives in
   external codebases outside physlib's dependency surface.  Here
   the file records only its scalar projection. -/

end Physlib.QuantumMechanics.ComplexAction.RouteConvergence

end
