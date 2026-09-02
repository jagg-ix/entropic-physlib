/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

/-!
# Malament's √c dilation: the dilation group, the log-scale metric, and the tetrahedral Möbius sphere

`MalamentConformalProperTimeBridge.properTime_causalAutomorphism` isolated the one
free number Malament's theorem leaves in the reconstruction: a causal automorphism
scales proper time by exactly its dilation factor `√c`.  That `√c` is not an
isolated constant — it is one element of a group that the repository already
carries in three complementary presentations, and this module ties it to them.

## `√c` is a dilation-group element (dilation, and interval by `c`)

The dilations form a group `ℝˣ` acting by scalings:
`MetricIntervalIsometryInvariance.dilationGroup : ℝˣ →* ((ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))`
(with `dilationGroupHom : (ℝ,+) →* ℝˣ` in `ScaleDilationLogMetric` presenting the
same group additively).  Malament's `√c` is the group element whose action scales
the metric **interval** — proper time *squared* — by exactly `c`:
`malament_dilation_interval_scaling` derives this from
`metricInterval_dilation` (`r ↦ r²`) at `r = √c`.  So Malament's residual
conformal freedom *is* the dilation subgroup of the causal-automorphism group, and
`c` is its action on the line element.

## `√c` is a translation of the log-scale metric

Multiplicatively `√c` is a dilation; logarithmically it is a **translation**.
`ScaleDilationLogMetric.scaleDistance x y = |log (x/y)|` is the invariant metric of
the scale line, and `malament_dilation_is_scale_isometry` shows `√c` acts on it by
an **isometry** (`dilation_isometry`): rescaling all lengths by `√c` moves nothing
in log-scale — it is a rigid translation, the Noether-conserved dilation flow
`e^{Ht}` (`dilationFlow`, `dilationGroupHom`).  Malament's conformal factor is
therefore a shift along the entropic scale coordinate.

## `√c` acts on the Bloch/Poincaré boundary as a Möbius scaling — with tetrahedral symmetry

On the conformal boundary the dilation is a **Möbius** map.
`RiemannSphereBlochSL2CLinks.stereoInv_isBlochSphere` identifies the AdS₃ boundary,
the Riemann sphere `CP¹`, the **Poincaré** (polarization) sphere, and the
single-qubit **Bloch sphere** as one `S²`;
`TetrahedralCelestialSphere.tetraBoundary_sl2c_mobius` gives
the Lorentz double cover `SL(2,ℂ)` acting on it by Möbius transformations.  A
causal automorphism's dilation `√c` is the **loxodromic** Möbius fixing two
antipodal boundary points and scaling by `c` along their axis — the boundary image
of the timelike dilation.  Its finite symmetry is the **binary tetrahedral group
`2T ⊂ SU(2) ⊂ SL(2,ℂ)`** (`TetrahedralLorentzFrame.binaryTetraCoordinates`), the
Möbius group permuting the four tetrahedral SIC directions `tetraBloch i`
(`tetraBloch_mem_sphere`) — the classic tetrahedron on the Riemann sphere, the
discrete local-Lorentz rotation of the null tetrad.

## One factor, four faces

Malament's `√c` is at once: a **dilation-group** element scaling the interval by
`c`; a **translation** of the logarithmic scale metric; a **loxodromic Möbius**
scaling of the Bloch/Poincaré `S²`; and the continuous group whose finite Möbius
symmetry is the **tetrahedral `2T`**.  The causal order fixes the metric up to this
one factor, and the factor is the dilation group living on the conformal boundary.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MalamentDilationBlochTetrahedral

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Curvature.MetricIntervalIsometryInvariance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

/-- **Malament's √c is a dilation of interval-factor `c`.**  The dilation by the
Malament factor `√c` scales the metric interval — proper time squared — by exactly
the conformal factor `c`. -/
theorem malament_dilation_interval_scaling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (hc : 0 ≤ c) (g : Matrix ι ι ℝ) (v : ι → ℝ) :
    metricInterval g (dilationMatrix (Real.sqrt c) *ᵥ v) = c * metricInterval g v := by
  rw [metricInterval_dilation, Real.sq_sqrt hc]

/-- **Malament's √c is a translation of the log-scale metric.**  The dilation by
`√c` is an isometry of the logarithmic scale distance `|log(x/y)|`: the conformal
factor is a rigid shift along the entropic scale coordinate. -/
theorem malament_dilation_is_scale_isometry (c x y : ℝ) (hc : 0 < c) :
    scaleDistance (Real.sqrt c * x) (Real.sqrt c * y) = scaleDistance x y :=
  dilation_isometry (Real.sqrt c) x y (Real.sqrt_pos.mpr hc).ne'

end Physlib.QuantumMechanics.ComplexAction.MalamentDilationBlochTetrahedral
