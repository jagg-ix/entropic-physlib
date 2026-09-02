/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.RouteConvergence

/-!
# Phase B — classical (lossless) limit at the scalar level

Phase A (`RouteConvergence`) established that the five candidate
routes to entropic time (Bender, KMS, ETH, Page-Wootters, modular
flow) reduce to a single canonical `τ_ent` under matching
identifications.  Phase B asks the consistency question: what
happens to this framework in the limit where the entropic
contribution vanishes?  The physical expectation is that the
framework reduces to standard unitary QM, with coordinate time `t`
as the sole evolution parameter and no entropic-time scale
operative.

This module formalises that expectation **at the scalar level**:

1. Each route's defining quantity has a "lossless" value at the
   boundary of its carrier's positivity field — `Ṡ_I = 0` for
   Bender, `β_I · I = 0` for ETH, `β_mod = 0` for modular.  At
   that value, the route's defining real number takes its
   "no entropic content" form.

2. In the lossless limit, the route's `RouteConvergence` carrier
   *cannot be constructed* — its positivity field would be
   violated.  Formally this means the Phase-A convergence
   framework does not apply in the lossless limit; the downstream
   consumer falls back to standard coordinate-time QM.

## What lives in this module and what does not

**Here:**
* `IsLossless*` predicates per route.
* Bender boring-model recovery at scalar level: width zero,
  imaginary energy zero, complex energy real, decay fraction one.
* Carrier non-existence theorems: any Phase-A identification
  carrier refutes the corresponding lossless predicate.

**Not here (scope acknowledgement):**
* The operator-level reduction — that the Bender complex
  evolution `exp(−i·E·t/ℏ)` collapses to the Schrödinger
  evolution `exp(−i·H_R·t/ℏ)` when `Ṡ_I = 0` — lives in
  `Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame`
  and `Physlib.QuantumMechanics.FiniteTarget.\
  NagaoNielsenSchrodinger`.  The scalar content here is the
  *projection* of that operator-level statement onto the
  numerical scales.
* Whether any specific physical system is in the lossless limit
  is an empirical question outside the module.
* Phase B does not establish that `τ_ent` is the right physical
  time scale (Phases C–F).

## References

* For the operator-level Schrödinger reduction:
  `NagaoNielsenSchrodinger.tise_from_H_R_eigen_and_H_I_kernel`
  in `Physlib.QuantumMechanics.FiniteTarget`.
* For the Bender boring-model algebraic identities:
  `BenderIdentity` §C (`widthFromRate_at_zero`,
  `imaginaryEnergyOfRate_at_zero`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ClassicalLimit

open Physlib.QuantumMechanics.ComplexAction
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
open Physlib.QuantumMechanics.ComplexAction.RouteConvergence


/-- **Bender lossless condition**: zero entropy production rate.
At `Ṡ_I = 0` the complex energy is purely real, the resonance width
vanishes, and the decay fraction is unity.  No Bender resonance to
analyse. -/
def IsLosslessBender (dSI_dt : ℝ) : Prop := dSI_dt = 0

/-- **ETH lossless condition**: zero information-density rate
product.  Either `β_I = 0` (no inverse-temperature parameter) or
`I_dens = 0` (vanishing information density); both make the
canonical entropic time `τ_ent_canon = β_I · I / ℏ` equal zero. -/
def IsLosslessETH (β_I I_dens : ℝ) : Prop := β_I * I_dens = 0

/-- **Modular lossless condition**: zero modular period.  At
`β_mod = 0` the Tomita-Takesaki modular flow has trivial period;
the Connes-Rovelli identification with the KMS Planckian period
fails because `K.planckianPeriod > 0` is structural. -/
def IsLosslessModular (β_mod : ℝ) : Prop := β_mod = 0


/-- **Bender width vanishes** in the lossless limit.  Composes
`widthFromRate_at_zero` (BenderIdentity §C) with the predicate
unfolding. -/
lemma widthFromRate_eq_zero_of_lossless
    {dSI_dt : ℝ} (h : IsLosslessBender dSI_dt) :
    widthFromRate dSI_dt = 0 := by
  unfold IsLosslessBender at h
  rw [h]
  exact widthFromRate_at_zero

/-- **Imaginary energy vanishes** in the lossless limit. -/
lemma imaginaryEnergyOfRate_eq_zero_of_lossless
    {dSI_dt : ℝ} (h : IsLosslessBender dSI_dt) :
    imaginaryEnergyOfRate dSI_dt = 0 := by
  unfold IsLosslessBender at h
  rw [h]
  exact imaginaryEnergyOfRate_at_zero

/-- **Complex energy is purely real** in the lossless limit:
`E = E_R + 0·i`.  This is the standard QM form. -/
lemma complexEnergyOfRate_eq_real_of_lossless
    (E_R : ℝ) {dSI_dt : ℝ} (h : IsLosslessBender dSI_dt) :
    complexEnergyOfRate E_R dSI_dt = (E_R : ℂ) := by
  unfold IsLosslessBender at h
  apply Complex.ext
  · simp [complexEnergyOfRate_re]
  · simp [h]

/-- **Decay fraction is one** in the lossless limit, at any
slit-separation `t`.  Uses Lean's convention `ℏ / 0 = 0` and
`t / 0 = 0`: the lifetime computed at zero rate is zero (Lean
convention), and `exp(−t/0) = exp(0) = 1`. -/
lemma benderDecayFraction_eq_one_in_lossless_limit
    (t ℏ : ℝ) :
    benderDecayFraction t (lifetimeFromRate ℏ 0) = 1 := by
  unfold benderDecayFraction lifetimeFromRate
  simp [Real.exp_zero]

/-!

Each Phase-A identification carrier requires a positivity field on
the entropic parameter.  In the lossless limit the positivity field
is violated, so no carrier can be constructed.  Formally this means
the Phase-A framework does not apply in the lossless limit. -/

/-- **No `BenderKMSIdentification` in the Bender-lossless limit**.
Any constructed carrier refutes the lossless predicate.

Physically: the framework assumes `Ṡ_I > 0` (a resonance with a
finite lifetime); the lossless boundary `Ṡ_I = 0` corresponds to a
bound state with infinite lifetime, which the framework does not
parametrise. -/
lemma no_BenderKMS_in_lossless_limit
    (id : BenderKMSIdentification) :
    ¬ IsLosslessBender id.dSI_dt := by
  unfold IsLosslessBender
  exact id.dSI_dt_pos.ne'

/-- **No `KMSETHIdentification` in the ETH-lossless limit**.
The ETH carrier requires `β_I > 0` and `I_dens > 0`, so
`β_I · I_dens > 0`. -/
lemma no_KMSETH_in_lossless_limit
    (id : KMSETHIdentification) :
    ¬ IsLosslessETH id.E.β_I id.E.I_dens := by
  unfold IsLosslessETH
  exact (mul_pos id.E.β_I_pos id.E.I_dens_pos).ne'

/-- **No `KMSModularIdentification` in the modular-lossless
limit**.  The modular carrier requires `β_mod > 0`.

Physically: the Tomita-Takesaki modular automorphism at a faithful
KMS state has nontrivial period; the lossless boundary
`β_mod = 0` corresponds to a degenerate state where modular flow
does not exist. -/
lemma no_KMSModular_in_lossless_limit
    (id : KMSModularIdentification) :
    ¬ IsLosslessModular id.M.β_mod := by
  unfold IsLosslessModular
  exact id.M.β_mod_pos.ne'

/-!

The only `CanonicalTauWitness` constructor that does not require
entropic positivity is `ofKMS` — it takes a `KMSScale` directly
and sets `τ_ent := K.planckianPeriod`, which is positive by the
structural positivity fields of `KMSScale` itself.  In the
lossless boundary (where the four entropic-route carriers cannot
be constructed), only this KMS-route witness remains.

The numerical value `K.planckianPeriod = ℏ/(k_B·T)` still has the
KMS interpretation as the Planckian thermal period.  But without
cross-route confirmation from any of the four entropic carriers,
its identification with the system's physical time scale loses
the Phase-A multi-route support. -/

/-- **KMS-route witness survives the lossless boundary**: the
canonical witness `ofKMS K` exists for every `KMSScale K`, with
positive `τ_ent`, regardless of whether the four entropic routes
can be witnessed. -/
lemma ofKMS_τ_ent_pos (K : KMSScale) :
    0 < (CanonicalTauWitness.ofKMS K).τ_ent :=
  K.planckianPeriod_pos

end Physlib.QuantumMechanics.ComplexAction.ClassicalLimit

end
