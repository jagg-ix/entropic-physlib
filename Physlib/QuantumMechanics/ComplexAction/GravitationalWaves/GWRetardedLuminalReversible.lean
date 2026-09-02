/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravitationalWaves.GWRetardedCausalDiamond
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TidalPairsGWDispersion
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime

/-!
# The GW retarded null ray is the massless, luminal, reversible Bogoliubov mode

Links the gravitational-wave **retarded separation** (`GravitationalWaves.GWRetardedCausalDiamond`, the lightlike
source-to-field interval `q = c(t−t') + i·r`) to the **Bogoliubov / entropic-time** cluster — the GW
dispersion (`CanonicalTetradGravity.TidalPairsGWDispersion`, `gw_luminal`/`bogoliubovEnergy_massless`) and the
metric-root entropic time (`EntropicTime.MetricCommonRootEntropicTime`, `entropicTime_zero_iff_metric_luminal`).

The retarded separation `q` is lightlike (`L(q) = 0`, `retardedSeparation_lightlike`); its real and
imaginary parts are **equal** (both `= r`, `retardedSeparation_re`/`retardedSeparation_im`), so its
slope in the diamond's `(time, space)` coordinate is `q.im / q.re = 1` — exactly the **massless
Bogoliubov group velocity** `r / E = 1` (`retarded_velocity_eq_luminal_bogoliubov`), with
`E = bogoliubovEnergy r 0 = r` the massless dispersion (`retarded_massless_energy`). And a luminal
velocity is **zero entropic time** `τ_ent = 0` (`retarded_reversible`) — the GW retarded null
propagation is the *reversible* point of the Bogoliubov entropic clock.

So one and the same luminal point: the retarded **null cone** (geometry) = the **massless** GW mode
(`Δ = 0` dispersion) = **luminal** group velocity `r/E = 1` = **reversible** `τ_ent = 0` Bogoliubov
mode = the de Sitter **static patch** of the causal diamond (`CausalDiamond.Helicity`, the
`R = L` limit of `entropicTime_zero_iff_metric_luminal`). The GW Green's function propagates on the
boundary where the entropic clock stops.

* **§A — the parts of the retarded separation** (`retardedSeparation_re`, `retardedSeparation_im`).
* **§B — the massless, luminal mode** (`retarded_massless_energy`, `retarded_luminal`).
* **§C — the retarded slope is the Bogoliubov velocity** (`retarded_velocity_eq_luminal_bogoliubov`).
* **§D — luminal ⟹ reversible** (`retarded_reversible`).
* **§E — the unification** (`gw_retarded_luminal_reversible`).

## References

* Repo carriers: `GravitationalWaves.GWRetardedCausalDiamond` (`retardedSeparation`), `CanonicalTetradGravity.TidalPairsGWDispersion`
  (`gw_luminal`, `bogoliubovEnergy_massless`), `EntropicTime.MetricCommonRootEntropicTime`
  (`entropicTime_zero_iff_metric_luminal`), `Bogoliubov.EntropicTime` (`bogoliubovEntropicTime`),
  `CausalDiamond.Helicity` (the static-patch realization).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravitationalWaves.GWRetardedLuminalReversible

open Physlib.QuantumMechanics.ComplexAction.GravitationalWaves.GWRetardedCausalDiamond
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TidalPairsGWDispersion
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime


/-- **The real (time) part of the retarded separation is `r`** — `q.re = c(t−t') = r` (the retarded
condition `t' = t − r/c`); the source-to-field time elapsed times `c` equals the distance. -/
lemma retardedSeparation_re (t r c : ℝ) (hc : c ≠ 0) : (retardedSeparation t r c).re = r := by
  rw [retardedSeparation, retardedTime]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  field_simp; ring

/-- **The imaginary (space) part of the retarded separation is `r`** — `q.im = r`, the source-to-field
distance. -/
lemma retardedSeparation_im (t r c : ℝ) : (retardedSeparation t r c).im = r := by
  rw [retardedSeparation]
  simp [Complex.add_im, Complex.mul_im]


/-- **[Massless GW mode] `E = r`** — the Bogoliubov energy of the retarded mode (spatial scale `r`,
gap `Δ = 0`) is `bogoliubovEnergy r 0 = |r| = r` (`bogoliubovEnergy_massless`); the GW retarded mode is
massless. -/
lemma retarded_massless_energy (r : ℝ) (hr0 : 0 ≤ r) : bogoliubovEnergy r 0 = r := by
  rw [bogoliubovEnergy_massless, abs_of_nonneg hr0]

/-- **[Luminal group velocity] `r / E = 1`** — the massless GW mode propagates at the light speed
(`gw_luminal`): its Bogoliubov group velocity is exactly `1`. -/
lemma retarded_luminal (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≠ 0) : r / bogoliubovEnergy r 0 = 1 := by
  nth_rewrite 1 [← abs_of_nonneg hr0]
  exact gw_luminal r hr


/-- **[The retarded null slope is the luminal Bogoliubov velocity] `q.im / q.re = r / E = 1`.** Because
the retarded separation has equal real and imaginary parts (`q.re = q.im = r`), its slope in the
diamond's `(time, space)` coordinate is the **massless Bogoliubov group velocity** `r / E` — both equal
`1`, the light cone. The geometric null ray and the kinematic luminal mode are the same. -/
lemma retarded_velocity_eq_luminal_bogoliubov (t r c : ℝ) (hr0 : 0 ≤ r) (hr : r ≠ 0) (hc : c ≠ 0) :
    (retardedSeparation t r c).im / (retardedSeparation t r c).re = r / bogoliubovEnergy r 0 := by
  rw [retardedSeparation_im, retardedSeparation_re t r c hc, retarded_luminal r hr0 hr, div_self hr]


/-- **[The GW retarded null propagation is reversible] `τ_ent = 0`.** A luminal velocity (`r / E = 1`)
is the metric-null condition `entropicTime_zero_iff_metric_luminal`, so the Bogoliubov entropic time of
the massless GW mode vanishes — the retarded Green's function is supported exactly on the surface where
the entropic clock stops (the reversible, `τ_ent = 0` light cone). -/
lemma retarded_reversible (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≠ 0) :
    bogoliubovEntropicTime r 0 = 0 := by
  refine (entropicTime_zero_iff_metric_luminal r 0).mpr (Or.inl ?_)
  nth_rewrite 1 [← abs_of_nonneg hr0]
  exact gw_luminal r hr


/-- **[GW retarded null = massless = luminal = reversible, unified] one luminal point.** The retarded
source-to-field separation is **lightlike** (on the diamond null cone) and **future-directed**
(in `causalFuture 0`); the associated GW mode (spatial scale `r`) is **massless** (`E = r`), propagates
at the **luminal** group velocity `r / E = 1`, and has **zero entropic time** `τ_ent = 0` (reversible).
So the geometry (retarded null cone), the dispersion (massless GW), the kinematics (luminal velocity),
and the thermodynamics (reversible Bogoliubov clock) all coincide on the GW retarded light cone — the
de Sitter static patch of the Jacobson–Visser causal diamond. -/
lemma gw_retarded_luminal_reversible (t r c : ℝ) (hr0 : 0 ≤ r) (hr : r ≠ 0) (hc : c ≠ 0) :
    lightlike (retardedSeparation t r c)
      ∧ retardedSeparation t r c ∈ causalFuture 0
      ∧ bogoliubovEnergy r 0 = r
      ∧ r / bogoliubovEnergy r 0 = 1
      ∧ bogoliubovEntropicTime r 0 = 0 :=
  ⟨retardedSeparation_lightlike t r c hc,
    retarded_in_causalFuture t r c hr0 hc,
    retarded_massless_energy r hr0,
    retarded_luminal r hr0 hr,
    retarded_reversible r hr0 hr⟩

end Physlib.QuantumMechanics.ComplexAction.GravitationalWaves.GWRetardedLuminalReversible

end
