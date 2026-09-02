/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone
public import Physlib.Mathematics.Distribution.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

meta import Zil

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

  `∫ f(t') δ(t' − t_ret) dt' = f(t_ret)`   (`retarded_sift`, Mathlib `integral_dirac`).

Hence the full retarded-kernel action is `(1/4πr)·f(t_ret)` (`retardedKernelAction`,
`retardedKernelAction_eq`) — the source evaluated at the retarded time, weighted by the Coulomb tail: the
closed form of the abstract retarded operator `I` of `CanonicalTetradGravity.GWRetardedGreen`. The measure is concentrated at
`t_ret ≤ t` (`CanonicalTetradGravity.RetardedKernelLightCone.retardedTime_le`), so the integral only ever sees the *past* —
the causal (past-light-cone) support is now an honest measure-theoretic statement.

* **§A — the light-cone `δ` as a Dirac measure** (`retardedMeasure`, `retardedMeasure_univ`, `retarded_sift`).
* **§B — the retarded-kernel action** (`retardedKernelAction`, `retardedKernelAction_eq`).
* **§C — exact causal path composition**: complex-valued Dirac transport composes by addition of radial
  light-travel distances (`retardedTransport_compose`), the pointwise Chapman--Kolmogorov law for this
  light-cone path measure.
* **§D — advanced transport and Pauli--Jordan difference**: the advanced measure is derived by time
  reversal, obeys the same composition law, and the retarded-minus-advanced operator is odd under time
  reversal (`causalKernelActionComplex_timeReversal`).
* **§E — bounded operator realization**: fixed-event retarded, advanced, and causal actions are genuine
  continuous linear maps on bounded continuous complex sources; the causal operator has the explicit
  `2 |1/(4πr)|` norm bound.
* **§F — Schwartz-distribution realization**: the same finite Dirac measures embed canonically into
  `𝓢'(ℝ)`, and their Coulomb-weighted difference is an actual distributional Pauli--Jordan kernel.

(An alternative analytic representation — the `δ` as the `c → ∞` Gaussian nascent-delta limit — is the NN
contour `ComplexDelta.ContourGaussian.gaussianContourIntegral`; the Dirac-measure model is used here.)

## References

* Mathlib `MeasureTheory.Measure.dirac`, `integral_dirac` (the Dirac measure and its sifting property).
* Repo carriers: `CanonicalTetradGravity.RetardedKernelLightCone` (`retardedTime`, `retardedAmplitude`, the causal geometry),
  `CanonicalTetradGravity.GWRetardedGreen` (the abstract retarded operator `I`), `ComplexDelta.ContourGaussian` (the NN Gaussian
  nascent delta).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure

open MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone


/-- **The light-cone `δ` as a Dirac measure** — `δ(t' − (t − r/c))` is the Dirac measure concentrated at the
retarded time `t_ret = t − r/c`. -/
noncomputable def retardedMeasure (t r c : ℝ) : Measure ℝ := Measure.dirac (retardedTime t r c)

/-- The retarded light-cone measure is finite because it is a Dirac probability
measure.  Naming the instance lets downstream distribution constructors use
the semantic alias without repeatedly unfolding it. -/
noncomputable instance retardedMeasure.instIsFiniteMeasure (t r c : ℝ) :
    IsFiniteMeasure (retardedMeasure t r c) := by
  unfold retardedMeasure
  infer_instance

/-- **[`δ`-normalization] total mass `1`** — the retarded `δ` is a genuine probability distribution
`∫ δ = 1`. -/
@[simp] lemma retardedMeasure_univ (t r c : ℝ) : (retardedMeasure t r c) Set.univ = 1 := by
  rw [retardedMeasure, Measure.dirac_apply_of_mem (Set.mem_univ _)]

/-- **[Sifting property] `∫ f(t') δ(t' − t_ret) dt' = f(t_ret)`.** Integrating a source against the light-cone
`δ` evaluates it at the retarded time — the defining distributional action of the retarded kernel, modelled by
Mathlib's `integral_dirac`. -/
lemma retarded_sift (t r c : ℝ) (f : ℝ → ℝ) :
    ∫ t', f t' ∂(retardedMeasure t r c) = f (retardedTime t r c) := by
  rw [retardedMeasure, integral_dirac]


/-- **The retarded-kernel action** `G ⋆ f = (1/4πr) ∫ f(t') δ(t' − t_ret) dt'` — the Coulomb tail times the
source integrated against the light-cone `δ`; the closed form of the abstract retarded operator `I`. -/
noncomputable def retardedKernelAction (t r c : ℝ) (f : ℝ → ℝ) : ℝ :=
  retardedAmplitude r * ∫ t', f t' ∂(retardedMeasure t r c)

/-- **[The retarded solution is the retarded source] `G ⋆ f = (1/4πr)·f(t_ret)`.** Integrating the explicit
kernel against a source yields the source evaluated at the retarded time, weighted by `1/4πr` — the field at
`(t,x)` is the source on its past light cone (`t_ret ≤ t`). -/
lemma retardedKernelAction_eq (t r c : ℝ) (f : ℝ → ℝ) :
    retardedKernelAction t r c f = retardedAmplitude r * f (retardedTime t r c) := by
  rw [retardedKernelAction, retarded_sift]

/-! ## C. Complex light-cone transport and exact path composition -/

/-- Complex-valued sifting against the same light-cone Dirac measure.  This is
the scalar field used by the Lorentzian/path-integral layer, rather than a
second measure model. -/
lemma retarded_sift_complex (t r c : ℝ) (f : ℝ → ℂ) :
    ∫ t', f t' ∂(retardedMeasure t r c) = f (retardedTime t r c) := by
  rw [retardedMeasure, integral_dirac]

/-- Normalized causal transport along one radial null segment.  The Coulomb
tail is omitted here so that this is the transition part of the kernel:
`T_r f(t) = ∫ f(t') δ(t'-(t-r/c)) = f(t-r/c)`. -/
noncomputable def retardedTransport (t r c : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ t', f t' ∂(retardedMeasure t r c)

@[simp]
lemma retardedTransport_eq (t r c : ℝ) (f : ℝ → ℂ) :
    retardedTransport t r c f = f (retardedTime t r c) := by
  rw [retardedTransport, retarded_sift_complex]

/-- Retarded times concatenate exactly when radial light-travel distances
are added. -/
lemma retardedTime_compose (t r₂ r₁ c : ℝ) :
    retardedTime (retardedTime t r₂ c) r₁ c =
      retardedTime t (r₁ + r₂) c := by
  unfold retardedTime
  ring

/-- **Exact causal Chapman--Kolmogorov law.**  Integrating over two
successive light-cone Dirac measures is the same as transport over the sum of
the radial segments.  This is a genuine pointwise path-measure composition,
not multiplication of two scalar damping factors. -/
theorem retardedTransport_compose
    (t r₂ r₁ c : ℝ) (f : ℝ → ℂ) :
    retardedTransport t r₂ c
        (fun τ => retardedTransport τ r₁ c f) =
      retardedTransport t (r₁ + r₂) c f := by
  simp only [retardedTransport_eq, retardedTime_compose]

/-! ## D. Advanced transport and the Pauli--Jordan difference -/

/-- Advanced time `t+r/c`, constructed as the time reverse of the retarded
time rather than supplied independently. -/
noncomputable def advancedTime (t r c : ℝ) : ℝ := t + r / c

lemma advancedTime_eq_neg_retardedTime_neg (t r c : ℝ) :
    advancedTime t r c = -retardedTime (-t) r c := by
  unfold advancedTime retardedTime
  ring

/-- The advanced light-cone delta measure. -/
noncomputable def advancedMeasure (t r c : ℝ) : Measure ℝ :=
  Measure.dirac (advancedTime t r c)

/-- The advanced light-cone measure is finite for the same derived Dirac
reason as the retarded measure. -/
noncomputable instance advancedMeasure.instIsFiniteMeasure (t r c : ℝ) :
    IsFiniteMeasure (advancedMeasure t r c) := by
  unfold advancedMeasure
  infer_instance

@[simp]
lemma advancedMeasure_univ (t r c : ℝ) :
    (advancedMeasure t r c) Set.univ = 1 := by
  rw [advancedMeasure, Measure.dirac_apply_of_mem (Set.mem_univ _)]

/-- Advanced sifting is evaluation at `t+r/c`. -/
lemma advanced_sift_complex (t r c : ℝ) (f : ℝ → ℂ) :
    ∫ t', f t' ∂(advancedMeasure t r c) = f (advancedTime t r c) := by
  rw [advancedMeasure, integral_dirac]

/-- Normalized advanced transport along one radial null segment. -/
noncomputable def advancedTransport (t r c : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ t', f t' ∂(advancedMeasure t r c)

@[simp]
lemma advancedTransport_eq (t r c : ℝ) (f : ℝ → ℂ) :
    advancedTransport t r c f = f (advancedTime t r c) := by
  rw [advancedTransport, advanced_sift_complex]

/-- Advanced transport is the time reverse of retarded transport. -/
lemma advancedTransport_eq_timeReverse_retarded
    (t r c : ℝ) (f : ℝ → ℂ) :
    advancedTransport t r c f =
      retardedTransport (-t) r c (fun τ => f (-τ)) := by
  rw [advancedTransport_eq, retardedTransport_eq,
    advancedTime_eq_neg_retardedTime_neg]

/-- Advanced times concatenate by addition of radial light-travel
distances. -/
lemma advancedTime_compose (t r₂ r₁ c : ℝ) :
    advancedTime (advancedTime t r₂ c) r₁ c =
      advancedTime t (r₁ + r₂) c := by
  unfold advancedTime
  ring

/-- Exact Chapman--Kolmogorov composition for the time-reversed advanced
light-cone measure. -/
theorem advancedTransport_compose
    (t r₂ r₁ c : ℝ) (f : ℝ → ℂ) :
    advancedTransport t r₂ c
        (fun τ => advancedTransport τ r₁ c f) =
      advancedTransport t (r₁ + r₂) c f := by
  simp only [advancedTransport_eq, advancedTime_compose]

/-- Complex retarded Green-kernel action, including the Coulomb radial
amplitude. -/
noncomputable def retardedKernelActionComplex
    (t r c : ℝ) (f : ℝ → ℂ) : ℂ :=
  (retardedAmplitude r : ℂ) * retardedTransport t r c f

/-- Complex advanced Green-kernel action obtained from the advanced
transport. -/
noncomputable def advancedKernelActionComplex
    (t r c : ℝ) (f : ℝ → ℂ) : ℂ :=
  (retardedAmplitude r : ℂ) * advancedTransport t r c f

/-- The explicit radial Pauli--Jordan action `G_ret-G_adv`. -/
noncomputable def causalKernelActionComplex
    (t r c : ℝ) (f : ℝ → ℂ) : ℂ :=
  retardedKernelActionComplex t r c f -
    advancedKernelActionComplex t r c f

lemma retardedKernelActionComplex_eq
    (t r c : ℝ) (f : ℝ → ℂ) :
    retardedKernelActionComplex t r c f =
      (retardedAmplitude r : ℂ) * f (retardedTime t r c) := by
  simp [retardedKernelActionComplex]

lemma advancedKernelActionComplex_eq
    (t r c : ℝ) (f : ℝ → ℂ) :
    advancedKernelActionComplex t r c f =
      (retardedAmplitude r : ℂ) * f (advancedTime t r c) := by
  simp [advancedKernelActionComplex]

/-- **Pauli--Jordan time-reversal antisymmetry.**  Time reversal exchanges
the derived retarded and advanced measures, so their difference changes
sign. -/
theorem causalKernelActionComplex_timeReversal
    (t r c : ℝ) (f : ℝ → ℂ) :
    causalKernelActionComplex (-t) r c (fun τ => f (-τ)) =
      -causalKernelActionComplex t r c f := by
  have hret : -retardedTime (-t) r c = advancedTime t r c :=
    (advancedTime_eq_neg_retardedTime_neg t r c).symm
  have hadv : -advancedTime (-t) r c = retardedTime t r c := by
    unfold advancedTime retardedTime
    ring
  simp only [causalKernelActionComplex, retardedKernelActionComplex_eq,
    advancedKernelActionComplex_eq, hret, hadv]
  ring

/-! ## E. Continuous operator realization and energy bounds -/

/-- Retarded light-cone transport as a genuine continuous complex-linear
functional on bounded continuous sources. -/
noncomputable def retardedTransportCLM (t r c : ℝ) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] ℂ :=
  BoundedContinuousFunction.evalCLM ℂ (retardedTime t r c)

@[simp]
lemma retardedTransportCLM_apply
    (t r c : ℝ) (f : BoundedContinuousFunction ℝ ℂ) :
    retardedTransportCLM t r c f = f (retardedTime t r c) :=
  rfl

/-- Advanced light-cone transport as a continuous complex-linear
functional. -/
noncomputable def advancedTransportCLM (t r c : ℝ) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] ℂ :=
  BoundedContinuousFunction.evalCLM ℂ (advancedTime t r c)

@[simp]
lemma advancedTransportCLM_apply
    (t r c : ℝ) (f : BoundedContinuousFunction ℝ ℂ) :
    advancedTransportCLM t r c f = f (advancedTime t r c) :=
  rfl

/-- Continuous retarded Green action including the radial amplitude. -/
noncomputable def retardedKernelOperator (t r c : ℝ) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] ℂ :=
  (retardedAmplitude r : ℂ) • retardedTransportCLM t r c

/-- Continuous advanced Green action, derived on the same source carrier. -/
noncomputable def advancedKernelOperator (t r c : ℝ) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] ℂ :=
  (retardedAmplitude r : ℂ) • advancedTransportCLM t r c

/-- Continuous radial Pauli--Jordan operator `G_ret-G_adv`. -/
noncomputable def causalKernelOperator (t r c : ℝ) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] ℂ :=
  retardedKernelOperator t r c - advancedKernelOperator t r c

@[simp]
lemma causalKernelOperator_apply
    (t r c : ℝ) (f : BoundedContinuousFunction ℝ ℂ) :
    causalKernelOperator t r c f =
      causalKernelActionComplex t r c f := by
  simp [causalKernelOperator, retardedKernelOperator,
    advancedKernelOperator, causalKernelActionComplex,
    retardedKernelActionComplex_eq, advancedKernelActionComplex_eq]

/-- Explicit energy/operator bound for the Pauli--Jordan light-cone action.
It is finite at every nonzero radius and does not assume a Green operator as
data. -/
theorem norm_causalKernelOperator_apply_le
    (t r c : ℝ) (f : BoundedContinuousFunction ℝ ℂ) :
    ‖causalKernelOperator t r c f‖ ≤
      2 * |retardedAmplitude r| * ‖f‖ := by
  rw [causalKernelOperator_apply, causalKernelActionComplex,
    retardedKernelActionComplex_eq, advancedKernelActionComplex_eq]
  calc
    ‖(retardedAmplitude r : ℂ) * f (retardedTime t r c) -
        (retardedAmplitude r : ℂ) * f (advancedTime t r c)‖
        ≤ ‖(retardedAmplitude r : ℂ) * f (retardedTime t r c)‖ +
          ‖(retardedAmplitude r : ℂ) * f (advancedTime t r c)‖ :=
      norm_sub_le _ _
    _ = |retardedAmplitude r| *
          (‖f (retardedTime t r c)‖ + ‖f (advancedTime t r c)‖) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ |retardedAmplitude r| * (‖f‖ + ‖f‖) := by
      gcongr
      · exact BoundedContinuousFunction.norm_coe_le_norm f _
      · exact BoundedContinuousFunction.norm_coe_le_norm f _
    _ = 2 * |retardedAmplitude r| * ‖f‖ := by ring

/-- Operator-norm form of the explicit Pauli--Jordan energy bound. -/
theorem norm_causalKernelOperator_le (t r c : ℝ) :
    ‖causalKernelOperator t r c‖ ≤ 2 * |retardedAmplitude r| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro f
    calc
      ‖causalKernelOperator t r c f‖
          ≤ 2 * |retardedAmplitude r| * ‖f‖ :=
        norm_causalKernelOperator_apply_le t r c f
      _ = (2 * |retardedAmplitude r|) * ‖f‖ := rfl

/-! ## F. The explicit causal kernel as a Schwartz distribution -/

/-- The retarded light-cone Dirac measure embedded canonically as a complex
Schwartz distribution. -/
noncomputable def retardedDistribution (t r c : ℝ) : ℝ →d[ℂ] ℂ :=
  Physlib.Distribution.ofFiniteMeasure ℂ (retardedMeasure t r c)

@[simp]
lemma retardedDistribution_apply
    (t r c : ℝ) (η : SchwartzMap ℝ ℂ) :
    retardedDistribution t r c η = η (retardedTime t r c) := by
  rw [retardedDistribution, Physlib.Distribution.ofFiniteMeasure_apply,
    retarded_sift_complex]

/-- The finite-measure embedding is exactly the repository's existing Dirac
distribution at the retarded time. -/
theorem retardedDistribution_eq_diracDelta (t r c : ℝ) :
    retardedDistribution t r c =
      Physlib.Distribution.diracDelta ℂ (retardedTime t r c) := by
  ext η
  simp

/-- The advanced light-cone Dirac measure as a complex Schwartz
distribution. -/
noncomputable def advancedDistribution (t r c : ℝ) : ℝ →d[ℂ] ℂ :=
  Physlib.Distribution.ofFiniteMeasure ℂ (advancedMeasure t r c)

@[simp]
lemma advancedDistribution_apply
    (t r c : ℝ) (η : SchwartzMap ℝ ℂ) :
    advancedDistribution t r c η = η (advancedTime t r c) := by
  rw [advancedDistribution, Physlib.Distribution.ofFiniteMeasure_apply,
    advanced_sift_complex]

/-- The advanced finite measure is exactly a shifted Dirac distribution. -/
theorem advancedDistribution_eq_diracDelta (t r c : ℝ) :
    advancedDistribution t r c =
      Physlib.Distribution.diracDelta ℂ (advancedTime t r c) := by
  ext η
  simp

/-- Coulomb-weighted retarded distribution. -/
noncomputable def retardedKernelDistribution (t r c : ℝ) : ℝ →d[ℂ] ℂ :=
  (retardedAmplitude r : ℂ) • retardedDistribution t r c

/-- Coulomb-weighted advanced distribution. -/
noncomputable def advancedKernelDistribution (t r c : ℝ) : ℝ →d[ℂ] ℂ :=
  (retardedAmplitude r : ℂ) • advancedDistribution t r c

/-- The actual Schwartz-distribution Pauli--Jordan kernel
`G_ret-G_adv` for the explicit radial light-cone model. -/
noncomputable def causalKernelDistribution (t r c : ℝ) : ℝ →d[ℂ] ℂ :=
  retardedKernelDistribution t r c - advancedKernelDistribution t r c

@[simp]
lemma causalKernelDistribution_apply
    (t r c : ℝ) (η : SchwartzMap ℝ ℂ) :
    causalKernelDistribution t r c η =
      (retardedAmplitude r : ℂ) *
        (η (retardedTime t r c) - η (advancedTime t r c)) := by
  simp [causalKernelDistribution, retardedKernelDistribution,
    advancedKernelDistribution]
  ring

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure

end

/- ZIL-BEGIN -/

zil attach
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.retardedTransport_compose where
  formalizes @ "claim:the-explicit-light-cone-dirac-path-measure-obeys-an-exact-retarded-chapman-kolmogorov-law-under-addition-of-radial-null-segments",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.retarded_sift_complex",
  caveat @ "claim:exact-flat-radial-dirac-measure-composition-not-a-construction-of-a-global-green-operator-on-an-arbitrary-globally-hyperbolic-spacetime"

zil attach
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.advancedTransport_compose where
  formalizes @ "claim:time-reversal-constructs-the-advanced-light-cone-path-measure-and-its-exact-chapman-kolmogorov-composition-law",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.advancedTransport_eq_timeReverse_retarded"

zil attach
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.causalKernelActionComplex_timeReversal where
  formalizes @ "claim:the-explicit-retarded-minus-advanced-light-cone-dirac-kernel-is-odd-under-time-reversal",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.advancedTime_eq_neg_retardedTime_neg"

zil attach
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.norm_causalKernelOperator_le where
  formalizes @ "claim:the-explicit-flat-radial-pauli-jordan-dirac-kernel-is-a-bounded-continuous-operator-on-bounded-continuous-complex-sources-with-norm-at-most-two-times-the-coulomb-tail-amplitude",
  epistemic_status @ "risky",
  supported_by @ "lean:BoundedContinuousFunction.evalCLM",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.retardedKernelActionComplex_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.advancedKernelActionComplex_eq",
  caveat @ "claim:fixed-event-flat-radial-energy-bound-not-a-sobolev-estimate-a-wave-operator-inverse-or-a-hadamard-wavefront-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.causalKernelDistribution_apply where
  formalizes @ "claim:the-explicit-radial-pauli-jordan-kernel-is-the-coulomb-weighted-difference-of-two-canonically-embedded-shifted-dirac-schwartz-distributions",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Distribution.ofFiniteMeasure",
  supported_by @ "lean:Physlib.Distribution.diracDelta",
  caveat @ "claim:actual-one-dimensional-time-distribution-at-fixed-radius-not-yet-the-full-four-dimensional-maxwell-bivector-distribution"

zil_file_contract physlib.retardedDeltaCausalPathIntegral where
  promises "The explicit three-plus-one radial retarded light-cone delta is realized by an actual Dirac measure. Complex source transport is its Bochner integral and composes exactly under addition of null radial segments. Isometric time reversal derives the advanced measure and its composition law; the retarded-minus-advanced action is time-reversal odd. On bounded continuous complex sources the two evaluations and their Pauli-Jordan difference are continuous linear maps, with an explicit two-times-Coulomb-amplitude operator bound. The same finite measures embed canonically into the repository's Schwartz-distribution carrier, where their Coulomb-weighted difference is an actual distributional Pauli-Jordan kernel."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:MeasureTheory.Measure.dirac",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone.retardedTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedKernelLightCone.retardedAmplitude",
    "lean:BoundedContinuousFunction.evalCLM"
  ]
  forbids_substitutes [
    "a claim that global hyperbolicity alone constructs retarded or advanced Green operators",
    "an identification of the one-dimensional radial Dirac transport with the full intrinsic Maxwell inverse",
    "a Hadamard wavefront equality without off-cone rapid decay and on-cone lower-escape estimates"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.retardedTransport_compose,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.advancedTransport_compose,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.causalKernelActionComplex_timeReversal,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.norm_causalKernelOperator_le,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure.causalKernelDistribution_apply
  ]

/- ZIL-END -/
