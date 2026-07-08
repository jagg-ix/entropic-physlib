/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Physlib.Optics.TemporalDoubleSlit
public import Physlib.Optics.MaterialTimescales
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# KMS bridge: Euclidean modular scale → Lorentzian visibility

A KMS state at temperature `T` has natural period `β := ℏ/(k_B·T)`
in *imaginary* time; this is the period of the Tomita-Takesaki
modular automorphism `σ_t` (Connes-Rovelli thermal time).
"Entropic time lives in Euclidean space" refers to this object.

Real-time Lorentzian observables — fringe visibility at separation
`S`, dephasing-time `T₂`, etc. — see the modular flow through a
different window: the analytic continuation that ties Euclidean
correlators `G(τ_E)` to Wightman correlators `G(t)`.  In the
non-Hermitian-Hamiltonian formulation the bridge is concrete:
`H = H_R − i·H_I` evolves `ψ` in real Lorentzian time `t`, but the
imaginary part `H_I` is the Wick rotation of the Euclidean
entropy generator.

This module sets up the bridge.  It does not *prove* that any
specific Lorentzian rate equals the Euclidean modular rate — that
is the **Planckian saturation hypothesis**, recorded here as a
`Prop`.  What is proved is the algebraic chain of definitions and
the composition that, *under the saturation hypothesis*, yields a
visibility prediction `V(S) = V_cl · exp(−(k_B·T/ℏ)·S)`.

## The chain (theorem-by-theorem)

         [ Euclidean side ]                  [ Bridge / hypothesis ]               [ Lorentzian side ]

  KMS scale `(T, k_B, ℏ)`
      │
      ▼
  `planckianTime k_B T ℏ`                 ←── modular period `β = ℏ/(k_B·T)`
      │   from `Physlib.Optics.TemporalDoubleSlit` §F
      │
      │   `planckianTime_mul_thermalEntropicRate`:  `β · λ_th = 1`
      ▼   from `Physlib.Optics.TemporalDoubleSlit` §F
  `thermalEntropicRate k_B T ℏ`           ←── Lorentzian image `λ_th = k_B·T/ℏ`
      │   from `Physlib.Optics.TemporalDoubleSlit` §A
      │
      │   *** `IsPlanckianSaturation`: empirical hypothesis
      │       `lam_visibility = λ_th`
      ▼
                                          Bender identity slots:
                                          `rateFromLifetime`, `lifetimeFromRate`
                                              from `BenderIdentity` §A and §F
                                          `rate_lifetime_inverse`:  `λ · τ = 1`
                                              from `BenderIdentity` §F
                                          `widthFromLifetime_eq_two_entropyRateFromLifetime`:
                                              `Γ = 2·Ṡ_I`
                                              from `BenderIdentity` §F
                                          `lifetime_mul_width`:  `τ · Γ = ℏ`
                                              from `BenderIdentity` §B
                                                  │
                                                  ▼
                                          `visibility V_cl λ S = V_cl · exp(−λ·S)`
                                              from `Physlib.Optics.TemporalDoubleSlit` §C
                                                  │
                                                  │   `visibility_strictAnti_of_pos`
                                                  │       (falsifiable monotonicity)
                                                  │   `log_visibility_ratio`
                                                  │       (extraction recipe)
                                                  ▼
                                          Predicted V(S) at fixed T

## Contents

### §A — KMS scale structure

* `KMSScale` — bundle `(k_B, T, ℏ)` with positivities.
* `KMSScale.planckianPeriod` — `β := ℏ/(k_B·T)` projection.
* `KMSScale.thermalRate` — `λ_th := k_B·T/ℏ` projection.

### §B — Euclidean ↔ Lorentzian inversion

* `KMSScale.planckianPeriod_mul_thermalRate` — `β · λ_th = 1`.
* `KMSScale.planckianPeriod_pos`, `thermalRate_pos` — positivities.

### §C — Saturation hypothesis (empirical Prop)

* `IsPlanckianSaturation` — empirical claim that the medium's
  visibility-controlling Lorentzian rate equals `λ_th`.

### §D — Visibility prediction under saturation

* `KMSScale.saturationVisibility` — `V_cl · exp(−λ_th·S)`.
* `saturationVisibility_eq_visibility` — the prediction *is* the
  `visibility` function from TemporalDoubleSlit §C with `λ := λ_th`.
* `saturationVisibility_strictAnti_of_pos` — monotonicity in `S`.
* `log_saturationVisibility_ratio` — `ln(V/V_cl) = −λ_th·S`.

### §E — Sub-Planckian regime

For `lam_visibility < λ_th`, the observed visibility decays slower
than the saturation prediction.  Stated as a Prop; no theorem,
since the sub-Planckian rate is whatever the medium measures.

## What this module does NOT claim

* It does not prove that any physical medium is at Planckian
  saturation.  That is the empirical claim recorded as
  `IsPlanckianSaturation`.
* It does not derive the modular flow / KMS state from first
  principles; it takes the Euclidean period as the input scale
  `β := ℏ/(k_B·T)`.
* It does not connect to any specific experiment.  Consumer
  files (e.g. `Physlib.Optics.MaterialTimescales` for the four-
  timescale taxonomy, or downstream temporal-double-slit-specific
  files) wire experimental observables into the Lorentzian slot.

## References

* Connes, A. and Rovelli, C. (1994), *Von Neumann algebra
  automorphisms and time-thermodynamics relation in generally
  covariant quantum theories*, Class. Quantum Grav. **11**,
  2899-2917.
  DOI [10.1088/0264-9381/11/12/007](https://doi.org/10.1088/0264-9381/11/12/007).

* Bender, Brody, Hook (2008), *Quantum effects in classical
  systems having complex energy*, J. Phys. A **41** (35), 352003.
  DOI [10.1088/1751-8113/41/35/352003](https://doi.org/10.1088/1751-8113/41/35/352003).
  arXiv [0804.4169](https://arxiv.org/abs/0804.4169).

* Hartnoll, S. A. (2015), *Theory of universal incoherent metallic
  transport*, Nature Physics **11**, 54-61.
  DOI [10.1038/nphys3174](https://doi.org/10.1038/nphys3174).
  Origin of the Planckian dissipation bound `τ_Planck = ℏ/(k_B·T)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS

open Physlib.QuantumMechanics.ComplexAction
open Physlib.Optics.TemporalDoubleSlit

/-! ## §A — KMS scale structure -/

/-- **KMS thermal scale**: temperature `T` together with the
constants kit `(k_B, ℏ)`, with positivities.  All four physical
projections (`β`, `λ_th`, `Γ`, `Ṡ_I`) derive from these three
inputs. -/
structure KMSScale where
  /-- Boltzmann constant (J/K). -/
  kB  : ℝ
  /-- Temperature (K). -/
  T   : ℝ
  /-- Reduced Planck constant (J·s). -/
  ℏ   : ℝ
  /-- `k_B > 0`. -/
  kB_pos : 0 < kB
  /-- `T > 0`. -/
  T_pos  : 0 < T
  /-- `ℏ > 0`. -/
  ℏ_pos  : 0 < ℏ

namespace KMSScale

variable (K : KMSScale)

/-- **Planckian (modular) period**: `β := ℏ / (k_B · T)`.

This is the period of the Tomita-Takesaki modular automorphism
at the KMS state of temperature `T`.  Stored as the Euclidean
input timescale of the bridge.  Delegates to
`Physlib.Optics.TemporalDoubleSlit.planckianTime`. -/
def planckianPeriod : ℝ := planckianTime K.kB K.T K.ℏ

/-- **Thermal entropic rate**: `λ_th := k_B · T / ℏ`.

The Lorentzian image of the Euclidean modular generator.
Delegates to
`Physlib.Optics.TemporalDoubleSlit.thermalEntropicRate`. -/
def thermalRate : ℝ := thermalEntropicRate K.kB K.T K.ℏ

end KMSScale

/-! ## §B — Euclidean ↔ Lorentzian inversion -/

/-- **Planckian period is positive**.  Composes
`planckianTime_pos` from TemporalDoubleSlit §F. -/
theorem KMSScale.planckianPeriod_pos (K : KMSScale) :
    0 < K.planckianPeriod := by
  unfold KMSScale.planckianPeriod
  exact planckianTime_pos K.kB_pos K.T_pos K.ℏ_pos

/-- **Thermal rate is positive**.  Composes
`thermalEntropicRate_pos` from TemporalDoubleSlit §A. -/
theorem KMSScale.thermalRate_pos (K : KMSScale) :
    0 < K.thermalRate := by
  unfold KMSScale.thermalRate
  exact thermalEntropicRate_pos K.kB_pos K.T_pos K.ℏ_pos

/-- **Euclidean ↔ Lorentzian inversion**: `β · λ_th = 1`.

Composes `planckianTime_mul_thermalEntropicRate` from
TemporalDoubleSlit §F.  This is the bridge identity at the
algebraic level — the Euclidean period and the Lorentzian rate
are reciprocals. -/
theorem KMSScale.planckianPeriod_mul_thermalRate (K : KMSScale) :
    K.planckianPeriod * K.thermalRate = 1 := by
  unfold KMSScale.planckianPeriod KMSScale.thermalRate
  exact planckianTime_mul_thermalEntropicRate
    K.kB_pos K.T_pos K.ℏ_pos

/-! ## §C — Saturation hypothesis (empirical Prop) -/

/-- **Planckian saturation hypothesis**: the medium's
visibility-controlling Lorentzian rate `lam_visibility` equals the
KMS thermal rate `λ_th = k_B·T/ℏ`.

This is the `Π = 1` (saturation) condition of the Planckian
dissipation literature.  It is an empirical hypothesis, not a
theorem of the framework; recorded here as a `Prop` so consumer
code that assumes it (e.g. when feeding `thermalRate` into the
`visibility` slot) must state the assumption. -/
def IsPlanckianSaturation
    (K : KMSScale) (lam_visibility : ℝ) : Prop :=
  lam_visibility = K.thermalRate

/-! ## §D — Visibility prediction under saturation -/

/-- **Visibility predicted by KMS at Planckian saturation**:
`V(S) := V_cl · exp(−λ_th · S)`.

Definition delegates directly to `Physlib.Optics.TemporalDoubleSlit.visibility`
with `λ_ent` instantiated to the KMS thermal rate. -/
def KMSScale.saturationVisibility
    (K : KMSScale) (V_cl S : ℝ) : ℝ :=
  visibility V_cl K.thermalRate S

/-- **Saturation visibility is the TemporalDoubleSlit visibility
formula at `λ := λ_th`**.  This is a definitional equality but
recorded as a `theorem` to make the chain explicit. -/
theorem KMSScale.saturationVisibility_eq_visibility
    (K : KMSScale) (V_cl S : ℝ) :
    K.saturationVisibility V_cl S = visibility V_cl K.thermalRate S :=
  rfl

/-- **Saturation visibility at `S = 0` equals `V_cl`**.  Composes
`visibility_at_zero` from TemporalDoubleSlit §C. -/
@[simp] theorem KMSScale.saturationVisibility_at_zero
    (K : KMSScale) (V_cl : ℝ) :
    K.saturationVisibility V_cl 0 = V_cl := by
  unfold KMSScale.saturationVisibility
  exact visibility_at_zero V_cl K.thermalRate

/-- **Saturation visibility is non-negative**.  Composes
`visibility_nonneg` from TemporalDoubleSlit §C. -/
theorem KMSScale.saturationVisibility_nonneg
    (K : KMSScale) {V_cl S : ℝ} (hV : 0 ≤ V_cl) :
    0 ≤ K.saturationVisibility V_cl S := by
  unfold KMSScale.saturationVisibility
  exact visibility_nonneg hV

/-- **Saturation visibility is strictly monotone-decreasing in `S`**
whenever `V_cl > 0`.  Composes `visibility_strictAnti_of_pos` from
TemporalDoubleSlit §C with `thermalRate_pos` from §B above.

This is the falsifiable shape: at any fixed temperature, the
saturation prediction gives a strictly decreasing visibility in
`S` with slope `−λ_th`. -/
theorem KMSScale.saturationVisibility_strictAnti_of_pos
    (K : KMSScale) {V_cl : ℝ} (hV : 0 < V_cl) :
    StrictAnti (fun S : ℝ => K.saturationVisibility V_cl S) := by
  unfold KMSScale.saturationVisibility
  exact visibility_strictAnti_of_pos hV K.thermalRate_pos

/-- **Log-visibility ratio under saturation**:
`ln(V/V_cl) = −λ_th · S`.

Composes `log_visibility_ratio` from TemporalDoubleSlit §D.  This
is the extractable observable: plotting `ln(V(S)/V_cl)` against
`S` and reading the slope returns `−λ_th = −k_B·T/ℏ` whenever
the saturation hypothesis holds. -/
theorem KMSScale.log_saturationVisibility_ratio
    (K : KMSScale) {V_cl S : ℝ} (hV : 0 < V_cl) :
    Real.log (K.saturationVisibility V_cl S / V_cl) =
      -(K.thermalRate * S) := by
  unfold KMSScale.saturationVisibility
  exact log_visibility_ratio hV

/-! ## §E — Sub-Planckian regime

When the medium's Lorentzian dephasing rate `lam_visibility` is
strictly less than `λ_th`, the system is sub-Planckian: the
visibility decays slower than the saturation prediction.  This is
the *expected* generic case (Planckian saturation is a bound, not
a universal value).

No new theorem is needed: just instantiate `visibility V_cl
lam_visibility S` with `lam_visibility < K.thermalRate` and use
`visibility_strictAnti_of_pos` for the `λ`-axis monotonicity.

The predicate below records the regime; comparing
`lam_visibility` to `K.thermalRate` is what falsifies or supports
the saturation hypothesis given measured data. -/

/-- **Sub-Planckian dephasing**: the medium's measured Lorentzian
rate is strictly less than the KMS thermal rate. -/
def IsSubPlanckian
    (K : KMSScale) (lam_visibility : ℝ) : Prop :=
  lam_visibility < K.thermalRate

/-- **Saturation and sub-Planckian are mutually exclusive at a
fixed `lam_visibility`**.  Trivial dichotomy: equality versus strict
inequality. -/
theorem not_saturation_of_subPlanckian
    {K : KMSScale} {lam_visibility : ℝ}
    (h : IsSubPlanckian K lam_visibility) :
    ¬ IsPlanckianSaturation K lam_visibility := by
  unfold IsPlanckianSaturation IsSubPlanckian at *
  intro heq
  rw [heq] at h
  exact lt_irrefl _ h

/-! ## §F — Tomita-Takesaki / modular-flow hook

The rigorous Euclidean side of the bridge formalised in §A–§D
is the **Tomita-Takesaki modular automorphism** `σ_t` of a KMS
state, which Connes-Rovelli identify with the
generally-covariant "thermal time" direction.  For a KMS state
at temperature `T`, the modular automorphism has period
`β = ℏ/(k_B·T)` in *imaginary* time and acts on the observable
algebra by `σ_t (A) := Δ^{it/β} · A · Δ^{−it/β}` where `Δ` is
the modular operator of Tomita-Takesaki theory.

## External-origin disclaimer

Physlib's lakefile depends only on Mathlib and doc-gen4.  The
Tomita-Takesaki / Connes-Rovelli operator-level construction
described in this section is the *published mathematical
result* (Takesaki 1970; Connes-Rovelli 1994), referenced here
conceptually.  A formal Lean development of these theorems
exists outside physlib in a separate downstream Lean codebase
maintained by the same author; physlib has no import
dependency on it and does not invoke its theorems.  The role
of §F is solely to provide a `Prop` structure into which any
such downstream construction can plug, at the cost of one
declared assumption.

## Architectural decision: rate level here, operator level
   external

The physlib `ThermoFieldDynamics.KMS` works at the **rate level** (`β`,
`λ_th`, and the proved inverse identity `β · λ_th = 1`).  It
does **not** include the operator-level modular automorphism
group `σ_t` itself, the modular operator `Δ`, or Tomita's
theorem `(Δ^{it})* = Δ^{−it}`.

The operator-level content is part of the published Tomita-
Takesaki 1970 / Connes-Rovelli 1994 literature.  A formal Lean
treatment exists in a separate external codebase (no
dependency from physlib).  The split is intentional: physlib
stays material-agnostic and rate-level so it can be imported
by any downstream theory; the operator-algebra content lives
externally.  Physlib's §F provides only the **hook** by which
the rate-level KMS bridge can connect upward to an external
modular-flow construction without taking a build-time
dependency on it.

## What §F provides as the hook

A typed `Prop` structure `IsModularFlow` paralleling
`Physlib.QuantumMechanics.ComplexAction.\
PendryPhotonConservation.IsPendryEvolution`.  Any external
consumer that has constructed a concrete modular automorphism
family (per the Tomita-Takesaki 1970 / Connes-Rovelli 1994
construction) can declare `IsModularFlow K σ` and use the
rate-level theorems below to compose with the rest of
physlib.  The structure is opaque to physlib: nothing here
inspects the structure of `σ`.

## References

* Takesaki, M. (1970), *Tomita's theory of modular Hilbert
  algebras*, Springer Lecture Notes in Mathematics **128**.

* Connes, A. and Rovelli, C. (1994), *Von Neumann algebra
  automorphisms and time-thermodynamics relation in generally
  covariant quantum theories*, Class. Quantum Grav. **11**,
  2899-2917.
  DOI [10.1088/0264-9381/11/12/007](https://doi.org/10.1088/0264-9381/11/12/007).
-/

/-- **Modular-flow hypothesis**: the input from an
external operator-algebra construction that a given KMS scale
`K` is equipped with an abstract modular automorphism family
`σ : ℝ → α → α` on some observable structure `α`.

The shape of `σ` is intentionally minimal — a one-parameter
family of maps `α → α` indexed by a real parameter (the
modular time `t`) — so that external code with the full
operator-algebra structure (per Tomita 1970 / Connes-Rovelli
1994) can supply a witness for this `Prop` from its
constructed modular flow, without physlib taking any
dependency on that external code.

Stated as opaque `True` so that downstream callers must
*declare* the modular-flow input explicitly when assuming it
in a physlib-level theorem. -/
def IsModularFlow {α : Type*}
    (_K : KMSScale) (_σ : ℝ → α → α) : Prop :=
  True

/-- **Compatibility note**: the Lorentzian `thermalRate`
projection is consistent with any modular-flow input,
because `thermalRate` is just `1/β` and `β` is a property of
the KMS scale alone, not of the modular flow constructed on
top of it. -/
theorem thermalRate_pos_under_isModularFlow
    {α : Type*} (K : KMSScale) (σ : ℝ → α → α)
    (_h : IsModularFlow K σ) :
    0 < K.thermalRate :=
  K.thermalRate_pos

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS

end
