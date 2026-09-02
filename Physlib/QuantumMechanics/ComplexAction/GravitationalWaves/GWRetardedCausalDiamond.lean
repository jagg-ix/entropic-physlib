/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction

/-!
# The GW retarded Green's function propagates on the causal-diamond null boundary

Links the gravitational-wave **retarded Green's function** (`CanonicalTetradGravity.RetardedKernelLightCone`, the
`δ(t−t'−r/c)/4πr` kernel with its causal past-light-cone support) to the **causal-diamond construction**
(`CausalDiamond.Construction`, the `causalFuture`/`causalPast`/`lightlike` Jacobson–Visser geometry) — both
built on the same `45°` `lightlike` null structure (`Rapidity.LightCone45RapidityUnification`).

The retarded source-to-field separation `q = c(t−t') + i·r` (with `t' = t − r/c` the retarded time) is

  **lightlike and future-directed** — `q ∈ causalFuture 0`   (`retarded_in_causalFuture`),

i.e. the field point lies in the **causal future** of the source, on the future **null boundary** of the causal
diamond (equivalently: the source is on the field point's **past light cone**, `retardedTime_le`). So the GW
retarded propagation is exactly the causal-diamond's null-cone causal structure — the Green's function support
is the boundary `𝓗` of `causalPast`, the `45°` light cone of the Jacobson–Visser diamond.

* **§A — the retarded separation** (`retardedSeparation`, `retardedSeparation_lightlike`).
* **§B — the causal-future membership** (`retarded_in_causalFuture`).

## References

* Repo carriers: `CanonicalTetradGravity.RetardedKernelLightCone` (`retardedTime`, the retarded kernel, the causal support),
  `CausalDiamond.Construction` (`causalFuture`, `lightlike`), `Rapidity.LightCone45RapidityUnification` (`lightlike`),
  `ComplexDelta.Convergence` (`lorentzianForm`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravitationalWaves.GWRetardedCausalDiamond

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction


/-- **The retarded source-to-field separation** `q = c(t−t') + i·r` (with `t' = t − r/c`) — the spacetime
interval, in the diamond's complex `(time, space)` coordinate, between the radiating source and the field
point it reaches. -/
noncomputable def retardedSeparation (t r c : ℝ) : ℂ :=
  (c * (t - retardedTime t r c) : ℝ) + (r : ℝ) * Complex.I

/-- **[On the null boundary] the retarded separation is lightlike** — `L(q) = 0`, the `45°` light cone
(`CanonicalTetradGravity.RetardedKernelLightCone.retarded_separation_lightlike`); the GW propagates exactly on the diamond's
null boundary. -/
lemma retardedSeparation_lightlike (t r c : ℝ) (hc : c ≠ 0) :
    lightlike (retardedSeparation t r c) :=
  retarded_separation_lightlike t r c hc


/-- **[GW retarded propagation = causal-diamond null structure] `q ∈ causalFuture 0`.** The retarded
separation is **lightlike** (`L(q) = 0 ≥ 0`) and **future-directed** (`q.re = r ≥ 0`), so the field point lies
in the **causal future** of the source — on the future null boundary of the Jacobson–Visser causal diamond
(`CausalDiamond.Construction.causalFuture`). Equivalently, the retarded Green's function is supported on the
field point's past light cone. -/
lemma retarded_in_causalFuture (t r c : ℝ) (hr : 0 ≤ r) (hc : c ≠ 0) :
    retardedSeparation t r c ∈ causalFuture 0 := by
  refine ⟨?_, ?_⟩
  · rw [sub_zero]
    have h := retarded_separation_lightlike t r c hc
    unfold lightlike at h
    rw [show retardedSeparation t r c
          = (c * (t - retardedTime t r c) : ℝ) + (r : ℝ) * Complex.I from rfl, h]
  · rw [sub_zero, retardedSeparation, retardedTime]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    have hrc : c * (t - (t - r / c)) = r := by field_simp; ring
    rw [hrc]
    simpa using hr

end Physlib.QuantumMechanics.ComplexAction.GravitationalWaves.GWRetardedCausalDiamond

end
