/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# The light-cone `δ` as a Dirac measure: integrating the retarded kernel (Lusanna §5)

Completes the retarded Green's function `G = δ(t−t'−r/c)/4πr` (`CanonicalTetradGravity.RetardedKernelLightCone`, the support
geometry) with the **measure-theoretic layer** — modeling the light-cone `δ` as an *actual* distribution (the
**Dirac measure**) and **integrating** it — by using Mathlib's `MeasureTheory.Measure.dirac` (the same
Dirac measure already used in `Thermodynamics.ComputationLandauer`).

The `δ(t' − (t − r/c))` of the retarded kernel is the Dirac measure concentrated at the **retarded time**
`t' = t − r/c` (`retardedMeasure`). It is a genuine probability distribution — total mass `1`
(`retardedMeasure_univ`, the `δ`-normalization) — and integrating a source against it **sifts** the value at
the retarded time:

 `∫ f(t') δ(t' − t_ret) dt' = f(t_ret)` (`retarded_sift`, Mathlib `integral_dirac`).

Hence the full retarded-kernel action is `(1/4πr)·f(t_ret)` (`retardedKernelAction`,
`retardedKernelAction_eq`) — the source evaluated at the retarded time, weighted by the Coulomb tail: the
closed form of the abstract retarded operator `I` of `CanonicalTetradGravity.GWRetardedGreen`. The measure is concentrated at
`t_ret ≤ t` (`CanonicalTetradGravity.RetardedKernelLightCone.retardedTime_le`), so the integral only ever sees the *past* —
the causal (past-light-cone) support is now a measure-theoretic statement.

* **§A — the light-cone `δ` as a Dirac measure** (`retardedMeasure`, `retardedMeasure_univ`, `retarded_sift`).
* **§B — the retarded-kernel action** (`retardedKernelAction`, `retardedKernelAction_eq`).

(An alternative analytic representation — the `δ` as the `c → ∞` Gaussian nascent-delta limit — is the NN
contour `ComplexDelta.ContourGaussian.gaussianContourIntegral`; the Dirac-measure model is used here.)

## References

* Mathlib `MeasureTheory.Measure.dirac`, `integral_dirac` (the Dirac measure and its sifting property).
* Repo dependencies: `CanonicalTetradGravity.RetardedKernelLightCone` (`retardedTime`, `retardedAmplitude`, the causal geometry),
 `CanonicalTetradGravity.GWRetardedGreen` (the abstract retarded operator `I`), `ComplexDelta.ContourGaussian` (the NN Gaussian
 nascent delta).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure

open MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone

/-! ## §A — the light-cone `δ` as a Dirac measure -/

/-- **The light-cone `δ` as a Dirac measure** — `δ(t' − (t − r/c))` is the Dirac measure concentrated at the
retarded time `t_ret = t − r/c`. -/
noncomputable def retardedMeasure (t r c : ℝ) : Measure ℝ := Measure.dirac (retardedTime t r c)

/-- **[`δ`-normalization] total mass `1`** — the retarded `δ` is a genuine probability distribution
`∫ δ = 1`. -/
@[simp] theorem retardedMeasure_univ (t r c : ℝ) : (retardedMeasure t r c) Set.univ = 1 := by
  rw [retardedMeasure, Measure.dirac_apply_of_mem (Set.mem_univ _)]

/-- **[Sifting property] `∫ f(t') δ(t' − t_ret) dt' = f(t_ret)`.** Integrating a source against the light-cone
`δ` evaluates it at the retarded time — the defining distributional action of the retarded kernel, modelled by
Mathlib's `integral_dirac`. -/
theorem retarded_sift (t r c : ℝ) (f : ℝ → ℝ) :
    ∫ t', f t' ∂(retardedMeasure t r c) = f (retardedTime t r c) := by
  rw [retardedMeasure, integral_dirac]

/-! ## §B — the retarded-kernel action -/

/-- **The retarded-kernel action** `G ⋆ f = (1/4πr) ∫ f(t') δ(t' − t_ret) dt'` — the Coulomb tail times the
source integrated against the light-cone `δ`; the closed form of the abstract retarded operator `I`. -/
noncomputable def retardedKernelAction (t r c : ℝ) (f : ℝ → ℝ) : ℝ :=
  retardedAmplitude r * ∫ t', f t' ∂(retardedMeasure t r c)

/-- **[The retarded solution is the retarded source] `G ⋆ f = (1/4πr)·f(t_ret)`.** Integrating the explicit
kernel against a source yields the source evaluated at the retarded time, weighted by `1/4πr` — the field at
`(t,x)` is the source on its past light cone (`t_ret ≤ t`). -/
theorem retardedKernelAction_eq (t r c : ℝ) (f : ℝ → ℝ) :
    retardedKernelAction t r c f = retardedAmplitude r * f (retardedTime t r c) := by
  rw [retardedKernelAction, retarded_sift]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure

end
