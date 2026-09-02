/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The explicit retarded kernel `G = δ(t−t'−r/c)/4πr` and its causal light-cone support (Lusanna §5)

Completes the gravitational-wave retarded Green's function (`CanonicalTetradGravity.GWRetardedGreen`, the operator-level
inversion) with the **explicit `3+1` retarded kernel**

  `G_ret(t−t', x−x') = δ(t − t' − |x−x'|/c) / (4π|x−x'|)`,

and its **causal (past-light-cone) support**. The Dirac delta fires at the **retarded time**
`t' = t − r/c` (`retardedTime`, `r = |x−x'|`), so the source acts strictly in the *past* of the field point
(`retardedTime_le`) and the signal propagates at exactly the **speed of light** (`retarded_signal_speed`,
`r/(t−t') = c`). The separation is therefore **null** — `c²(t−t')² = r²` (`retarded_null`) — i.e. *lightlike*,
lying on the `45°` light cone (`retarded_separation_lightlike`, consuming
`Rapidity.LightCone45RapidityUnification.lightlike`). Hence the field at `(t,x)` depends only on sources on its
**past light cone** (`retarded_causal_past_lightcone`), and the radial amplitude is `1/4πr`
(`retardedAmplitude`).

* **§A — the retarded time & causality** (`retardedTime`, `retardedTime_le`, `retarded_signal_speed`).
* **§B — null / light-cone support** (`retarded_null`, `retarded_separation_lightlike`,
  `retarded_causal_past_lightcone`).
* **§C — the radial amplitude** (`retardedAmplitude`, `retardedAmplitude_pos`).

The full distributional kernel as a tempered distribution (`δ` on the light cone, the `1/4πr` Coulomb tail) is
the measure-theoretic layer; the geometry of the support — the retarded time, the luminal propagation, the
lightlike separation and the causal past-light-cone dependence — is formalized here.

## References

* The Klein–Gordon / wave-equation retarded Green's function `δ(t−r/c)/4πr` (Jackson, *Classical
  Electrodynamics*); L. Lusanna, IJGMMP 12 (2015) 1530001, §5 (the retarded GW propagation).
* Repo carriers: `Rapidity.LightCone45RapidityUnification` (`lightlike`, `lorentzianForm`),
  `CanonicalTetradGravity.GWRetardedGreen` (the operator-level retarded inversion `□I = id`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification


/-- **The retarded time** `t' = t − r/c` (`r = |x−x'|`) — the instant the source must act for its signal to
reach the field point at time `t`; the argument of the `δ` in `G = δ(t−t'−r/c)/4πr`. -/
noncomputable def retardedTime (t r c : ℝ) : ℝ := t - r / c

/-- **[Causality] the source acts in the past** `t' ≤ t` (for `c > 0`, `r ≥ 0`) — the retarded kernel
propagates forward in time. -/
lemma retardedTime_le (t r c : ℝ) (hc : 0 < c) (hr : 0 ≤ r) : retardedTime t r c ≤ t := by
  rw [retardedTime]; have h : 0 ≤ r / c := div_nonneg hr hc.le
  linarith

/-- **[Luminal propagation] the signal travels at the speed of light** `r/(t−t') = c`. -/
lemma retarded_signal_speed (t r c : ℝ) (hr : 0 < r) :
    r / (t - retardedTime t r c) = c := by
  rw [retardedTime]
  have h : t - (t - r / c) = r / c := by ring
  rw [h, div_div_eq_mul_div, mul_comm r c, mul_div_assoc, div_self hr.ne', mul_one]


/-- **[Null separation] `c²(t−t')² = r²`** — the retarded kernel is supported on the light cone, where the
spacetime interval vanishes. -/
lemma retarded_null (t r c : ℝ) (hc : c ≠ 0) :
    c ^ 2 * (t - retardedTime t r c) ^ 2 = r ^ 2 := by
  rw [retardedTime]; have h : t - (t - r / c) = r / c := by ring
  rw [h, div_pow]; field_simp

/-- **[Lightlike, the `45°` light cone] the retarded separation is lightlike.** The complex interval
`c(t−t') + i·r` has vanishing Lorentzian form `(c(t−t'))² − r² = 0` — it lies on the `45°` light cone
(`Rapidity.LightCone45RapidityUnification.lightlike`). -/
lemma retarded_separation_lightlike (t r c : ℝ) (hc : c ≠ 0) :
    lightlike ((c * (t - retardedTime t r c) : ℝ) + (r : ℝ) * Complex.I) := by
  unfold lightlike lorentzianForm
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  nlinarith [retarded_null t r c hc]

/-- **[Causal past-light-cone support] the field depends only on its past light cone.** The source point sits
in the *past* (`t' ≤ t`) and on the light cone (`lightlike`) of the field point — the defining causal property
of the retarded Green's function: no signal from outside the past light cone. -/
lemma retarded_causal_past_lightcone (t r c : ℝ) (hc : 0 < c) (hr : 0 ≤ r) :
    retardedTime t r c ≤ t
      ∧ lightlike ((c * (t - retardedTime t r c) : ℝ) + (r : ℝ) * Complex.I) :=
  ⟨retardedTime_le t r c hc hr, retarded_separation_lightlike t r c hc.ne'⟩


/-- **The radial amplitude** `1/(4πr)` — the Coulomb-tail prefactor of the retarded kernel
`G = δ(t−t'−r/c)/(4πr)`. -/
noncomputable def retardedAmplitude (r : ℝ) : ℝ := 1 / (4 * Real.pi * r)

/-- **The amplitude is positive** for `r > 0` — the retarded kernel has positive weight on the light cone. -/
lemma retardedAmplitude_pos (r : ℝ) (hr : 0 < r) : 0 < retardedAmplitude r := by
  rw [retardedAmplitude]; positivity

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone

end
