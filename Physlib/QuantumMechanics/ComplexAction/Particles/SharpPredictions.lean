/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.RouteConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Positivity

/-!
# Phase C — sharp predictions per route

Phases A and B established the formal scaffold: route uniqueness
under identification hypotheses (Phase A) and consistency with
standard QM in the lossless limit (Phase B).  Phase C is the
**bridge to empirical content**: state each route's framework
prediction as a Lean `Prop` sharp enough that data can refute it.

The unifying form of a route prediction is:

  **measured observable ≈ framework-predicted value**,
  where ≈ means "within an O(1) multiplicative window".

The multiplicative window is parametrised by a `tolerance_factor`
`k > 1`: the prediction `Holds` iff the ratio `measured/predicted`
lies in `(1/k, k)`.  Tight predictions (e.g. Bender Gamow half-life
to mean lifetime ratio) use small `k`; order-of-magnitude
predictions (e.g. Planckian dissipation prefactor) use `k ≈ 10`.

## What this module does and does not claim

**Does:**
* Provide the `SharpPrediction` structure that records measured
  value, framework-predicted value, and tolerance.
* Provide per-route constructors (Planckian dissipation, Bender
  Gamow lifetime) that instantiate `SharpPrediction` from
  Phase-A carriers.
* Prove `Holds ↔ ¬ Refutes` (the two-valued semantics).

**Does not:**
* Claim that any specific prediction `Holds` — that is an empirical
  question whose answer requires measurement data.  The structure
  states the prediction sharply enough that someone with
  measurements can evaluate it.
* Establish that `τ_ent` is the right physical time scale (still
  Phases D–F).

## References for empirical status

* **Planckian dissipation**:
  Bruin, J. A. N. et al. (2013), *Similarity of scattering rates in
  metals showing T-linear resistivity*, Science **339**, 804-807.
  Found `τ_tr · k_B · T / ℏ ≈ 1` (within an order of magnitude)
  for ten metals across nine orders of magnitude of resistivity.
  Legros, A. et al. (2019), *Universal T-linear resistivity and
  Planckian dissipation in overdoped cuprates*, Nature Physics
  **15**, 142-147.  Confirms in La-Sr-Cu-O cuprate series.

* **Bender Gamow lifetime**:
  Gamow, G. (1928), *Zur Quantentheorie des Atomkernes*, Zeitschrift
  für Physik **51**, 204-212.  The half-life / mean-lifetime
  relationship `τ_½ = ln(2)·τ_mean` is standard nuclear physics;
  α-decay lifetimes have been measured across more than thirty
  orders of magnitude (from ²¹²Po at 0.3 μs to ²⁰⁹Bi at 10¹⁹ yr).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.SharpPredictions

open Physlib.QuantumMechanics.ComplexAction
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KMS
open Physlib.QuantumMechanics.ComplexAction.RouteConvergence


/-- **Sharp prediction**.  A measured real-valued observable, a
framework-predicted positive value, and a tolerance factor `k > 1`.

The prediction `Holds` iff the ratio `measured / predicted ∈ (1/k, k)`.
The prediction is `Refutes`-d iff the ratio falls outside that open
interval.  Together `Holds ↔ ¬ Refutes` (§C). -/
structure SharpPrediction where
  /-- The measured value (from experiment). -/
  measured : ℝ
  /-- The framework-predicted positive value. -/
  predicted : ℝ
  /-- The predicted value is positive. -/
  predicted_pos : 0 < predicted
  /-- Multiplicative tolerance factor `k > 1`. -/
  tolerance_factor : ℝ
  /-- `k > 1`. -/
  tolerance_factor_gt_one : 1 < tolerance_factor

namespace SharpPrediction

variable (P : SharpPrediction)

/-- **The prediction holds**: `measured/predicted ∈ (1/k, k)`. -/
def Holds : Prop :=
  1 / P.tolerance_factor < P.measured / P.predicted
    ∧ P.measured / P.predicted < P.tolerance_factor

/-- **The prediction is refuted**: `measured/predicted` falls
outside `(1/k, k)`. -/
def Refutes : Prop :=
  P.measured / P.predicted ≤ 1 / P.tolerance_factor
    ∨ P.tolerance_factor ≤ P.measured / P.predicted

end SharpPrediction


/-- **Planckian dissipation prediction** (KMS route).

For a material at temperature `T` (carried by a `KMSScale K`), the
transport scattering time `measured_τ_tr` is predicted to satisfy
`τ_tr · k_B · T / ℏ ∈ (0.1, 10)` — equivalently
`τ_tr / K.planckianPeriod ∈ (0.1, 10)`.

This is the **Planckian dissipation hypothesis** of Hartnoll 2015
and the empirical observation of Bruin 2013 / Legros 2019.  The
tolerance factor `k = 10` reflects the order-of-magnitude nature of
the prediction — known experimental data spans an O(1) prefactor
that varies across materials by less than an order of magnitude.

Refuter: any strange-metal-regime material with measured `τ_tr`
outside `[K.planckianPeriod/10, K.planckianPeriod·10]`. -/
def planckianDissipationPrediction
    (K : KMSScale) (measured_τ_tr : ℝ) : SharpPrediction where
  measured := measured_τ_tr
  predicted := K.planckianPeriod
  predicted_pos := K.planckianPeriod_pos
  tolerance_factor := 10
  tolerance_factor_gt_one := by norm_num

/-- **Bender Gamow half-life prediction** (Bender route).

For an α-decay resonance with entropy-production rate `Ṡ_I > 0`
and Planck constant `ℏ > 0`, the framework predicts a *mean*
lifetime `τ_mean := ℏ / (2·Ṡ_I)` and consequently a *half-life*
`τ_½ := ln(2) · τ_mean` (the standard mean-vs-half-life relation
for exponential decay).

Tolerance factor `k = 1.05` represents 5% experimental uncertainty,
typical of modern α-decay measurements.

Refuter: an α-decay resonance whose measured half-life deviates from
`ln(2) · ℏ / (2·Ṡ_I)` by more than 5%, where `Ṡ_I` is independently
extracted from the resonance's complex energy (e.g. via
S-matrix-pole methods). -/
def benderHalfLifePrediction
    (ℏ dSI_dt : ℝ) (ℏ_pos : 0 < ℏ) (dSI_dt_pos : 0 < dSI_dt)
    (measured_τ_half : ℝ) : SharpPrediction where
  measured := measured_τ_half
  predicted := Real.log 2 * lifetimeFromRate ℏ dSI_dt
  predicted_pos := by
    apply mul_pos
    · exact Real.log_pos (by norm_num)
    · exact lifetime_pos ℏ_pos dSI_dt_pos
  tolerance_factor := 1.05
  tolerance_factor_gt_one := by norm_num


/-- **Two-valued semantics**: a `SharpPrediction` either `Holds` or
`Refutes`, never both, never neither.  This is the formal statement
that the prediction is well-defined and falsifiable: any pair
`(measured, predicted)` of real numbers (with predicted positive)
deterministically lands in one of the two outcomes.

Proof: `Holds` says the ratio is in the open interval `(1/k, k)`;
`Refutes` says it is in the union `(−∞, 1/k] ∪ [k, ∞)` — the
complement.  Negation of `Holds` (with `push_neg`) gives exactly
`Refutes`. -/
lemma SharpPrediction.holds_iff_not_refutes (P : SharpPrediction) :
    P.Holds ↔ ¬ P.Refutes := by
  unfold Holds Refutes
  push Not
  rfl

/-!

The route-specific predictions can be evaluated against measured
data.  Each `Holds` reduces to a concrete real-arithmetic
inequality on the measurement. -/

/-- **Planckian-saturated `Holds` form** — the prediction holds iff
the measured `τ_tr / K.planckianPeriod` lies in the open interval
`(0.1, 10)`. -/
lemma planckianDissipationPrediction_Holds_iff
    (K : KMSScale) (measured_τ_tr : ℝ) :
    (planckianDissipationPrediction K measured_τ_tr).Holds ↔
      1/10 < measured_τ_tr / K.planckianPeriod
        ∧ measured_τ_tr / K.planckianPeriod < 10 := by
  unfold planckianDissipationPrediction SharpPrediction.Holds
  exact Iff.rfl

/-- **Bender Gamow half-life `Holds` form** — the prediction holds
iff the measured `τ_½` is within 5% of `ln(2)·τ_mean`. -/
lemma benderHalfLifePrediction_Holds_iff
    (ℏ dSI_dt : ℝ) (ℏ_pos : 0 < ℏ) (dSI_dt_pos : 0 < dSI_dt)
    (measured_τ_half : ℝ) :
    (benderHalfLifePrediction ℏ dSI_dt ℏ_pos dSI_dt_pos measured_τ_half).Holds ↔
      1 / 1.05 < measured_τ_half / (Real.log 2 * lifetimeFromRate ℏ dSI_dt)
        ∧ measured_τ_half / (Real.log 2 * lifetimeFromRate ℏ dSI_dt) < 1.05 := by
  unfold benderHalfLifePrediction SharpPrediction.Holds
  exact Iff.rfl

/-!

**In scope (this module):**
* Unified `SharpPrediction` structure with `Holds`/`Refutes`.
* Two route specialisations with literature-backed tolerance factors:
  Planckian dissipation (`k=10`) and Bender Gamow half-life (`k=1.05`).
* Iff-form unfoldings of `Holds` per route.
* Two-valued semantics theorem `holds_iff_not_refutes`.

**Out of scope (this module):**
* Whether either prediction `Holds` for any specific physical
  system — that requires measurement input.
* ETH information-density prediction.  The route's parameters
  `(β_I, I_dens)` are abstract carrier hypotheses; pinning them
  to a measurable observable requires operator-level ETH
  infrastructure (D'Alessio et al. 2016) not present in
  physlib's current scope.
* Page-Wootters clock-period prediction.  The clock readout
  observable depends on the clock subsystem's Hamiltonian
  spectrum; sharp prediction requires that data as input.
* Modular-flow period prediction.  The Connes-Rovelli scalar
  identification (`β_mod = K.planckianPeriod`) is a mathematical
  theorem at the operator level (Tomita-Takesaki); not separately
  empirical here.

These can be added in subsequent commits as the supporting
infrastructure (operator-level ETH, clock-Hamiltonian spectra)
becomes available in physlib or a downstream consumer. -/

end Physlib.QuantumMechanics.ComplexAction.Particles.SharpPredictions

end
