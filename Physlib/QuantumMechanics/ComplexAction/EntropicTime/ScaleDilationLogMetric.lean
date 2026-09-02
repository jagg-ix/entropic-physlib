/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComplexNoetherChargeEntropicHorizon
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.VectorBanachStoneDistortion
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Physlib.QuantumMechanics.SpinDensityFunctionalOperators
public import Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

/-!
# The entropic-time dilation group and its invariant scale metric — Noether charge, lattice ladder, `√2` half-step

The entropic-time arc measures separations by `r = λ_C·log K` (`EntropicProperDistance`): distances
are *logarithms of scale ratios*. This module isolates the group behind that formula and the metric
it preserves.

* **§A — the dilation group and its Noether charge.** The one-parameter flow
  `λ(t) = e^{Ht}` (`dilationFlow`) is a group homomorphism `(ℝ,+) →* ℝˣ` (`dilationGroupHom`) — the
  multiplicative group of expansions and reductions. It is the *Noether flow* of scale invariance:
  the scale Lagrangian `L(λ, λ̇) = ½(λ̇/λ)²` is invariant under `λ ↦ μλ`
  (`scaleLagrangian_dilation_invariant`), its Euler–Lagrange equation is `λ̈λ = λ̇²`, and along any
  solution the Noether charge `Q = λ̇/λ` is conserved (`noether_dilation_charge`); along the group
  orbit itself the charge is the generator, `d(log λ)/dt = H` (`dilationFlow_log_derivative`). The
  entropic-horizon energy decay `H_R(τ) = H_R(0)e^{−2τ}` of `ComplexNoetherChargeEntropicHorizon`
  *is* the orbit at `H = −2` (`entropicEnergyDecay_eq_dilationFlow`) — the group is already the
  time-evolution of the entropic-time arc.

* **§B — the invariant metric.** `scaleDistance x y = |log(x/y)|` is a metric on the positive reals
  (`scaleDistance_self/_comm/_triangle/_eq_zero_iff`) with the two properties requested of it:
  the dilation group acts by **isometries** — `scaleDistance (μx) (μy) = scaleDistance x y`
  (`dilation_isometry`): expanding or reducing all scales changes nothing — and `log` transports it
  **exactly** onto the standard line, `scaleDistance x y = dist (log x) (log y)`
  (`scaleDistance_eq_dist_log`): calculations in log coordinates are exact, not approximations.
  The entropic proper distance is precisely this metric on Schmidt numbers:
  `r = λ_C·scaleDistance K 1` and `|r − r'| = λ_C·scaleDistance K K'`
  (`entropicProperDistance_eq_scaleDistance`, `entropicProperDistance_sub`).

* **§C — the lattice ladder (QCD).** In lattice gauge theory the scale is the lattice spacing and
  the renormalization step is the blocking `a ↦ 2a` (the Wilson-action carrier is
  `QFT.PathIntegral.FiniteWilsonGaugeModel`; couplings run in `log a`). In the invariant metric the
  blocking step has the *same exact length from every starting point* —
  `scaleDistance (2a) a = scaleDistance 2 1 = log 2` (`blockspin_step_isometric`,
  `scaleDistance_two_one`) — and `n` blockings lie at exactly `n·log 2`
  (`blockspin_ladder`): the RG ladder is an arithmetic progression, with no accumulating error,
  because each step is an isometry of the group.

* **§D — the `√2` half-step and the holographic radial direction.** The Banach–Stone critical
  distortion `√2 = M²` (`VectorBanachStoneDistortion`, `M⁴ = 2`), the Johnson–Lindenstrauss
  endpoint `1 + ε = √2` at `ε = √2 − 1`, and the dual-sphere orthogonality chord
  `scalingFactor 2 = √2` (`dualSphere_orthogonal_chord`) are all the *same point* of the scale
  line, and in the invariant metric that point sits exactly **half a blocking step** from unity:
  `scaleDistance √2 1 = ½·scaleDistance 2 1` (`sqrtTwo_half_blockspin`,
  `critical_distortion_half_blockspin`, `scalingFactor_half_blockspin`). The AdS/CFT radial
  direction carries the same metric: the radial line element `dr/r` integrates to it,
  `∫_a^b dr/r = scaleDistance b a` (`adsRadial_arclength`), and the holographic RG shift is its
  isometry, `∫_{μa}^{μb} dr/r = ∫_a^b dr/r` (`adsRadial_dilation_invariant`) — the
  dimensional-reduction modules (`JohnsonLindenstraussHolographicReduction`,
  `LovelockHolographicReduction`) run along exactly this direction.

**Honest layering.** Everything here is exact: the group laws, the Noether conservation (an ODE
identity), the metric axioms, the isometries, the ladder arithmetic, the `√2` half-step, and the
radial arclength (Mathlib's `intervalIntegral.integral_inv_of_pos`). The *identifications* — the
scale variable as lattice spacing, the radial coordinate as RG scale, the Schmidt number as the
dilation carrier — are the standard readings of the referenced arcs, recorded in docstrings; no
lattice simulation data or holographic dictionary beyond the cited modules is claimed.

## References

* E. Noether, invariant variational problems — the dilation charge of the scale-invariant
  Lagrangian; `Physlib` (`EntropicTime.ComplexNoetherChargeEntropicHorizon`,
  `WeylCartanFluidNoether`).
* K. Wilson, lattice gauge theory and block-spin renormalization; `Physlib`
  (`QFT.PathIntegral.FiniteWilsonGaugeModel`).
* E. M. Galego, vector Banach–Stone at distortion `√2`; W. Johnson–J. Lindenstrauss; `Physlib`
  (`AdSCFT.VectorBanachStoneDistortion`, `AdSCFT.JohnsonLindenstraussHolographicReduction`,
  `Hopf.DualSphereFiberDecomposition`, `Mathematics.DimensionalScalingFunctorTower`).
* J. Maldacena, AdS/CFT — the radial direction as RG scale; `Physlib`
  (`AdSCFT.LovelockHolographicReduction`, `ComptonClock.EntropicProperDistance`).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComplexNoetherChargeEntropicHorizon
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.Mathematics.DimensionalScaling
open Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy


/-! ## §A — the dilation group and its Noether charge -/

/-- **The dilation flow** `λ(t) = e^{Ht}` — the one-parameter group of expansions (`H > 0`) and
reductions (`H < 0`) generated by the Noether charge `H`. -/
def dilationFlow (H t : ℝ) : ℝ := Real.exp (H * t)

/-- **[Identity]** `λ(0) = 1`. -/
@[simp] lemma dilationFlow_zero (H : ℝ) : dilationFlow H 0 = 1 := by
  simp [dilationFlow]

/-- **[Group law]** `λ(s + t) = λ(s)·λ(t)` — composing an expansion with a reduction is exact
multiplication of scale factors. -/
lemma dilationFlow_add (H s t : ℝ) :
    dilationFlow H (s + t) = dilationFlow H s * dilationFlow H t := by
  simp [dilationFlow, mul_add, Real.exp_add]

/-- **[Inverses]** `λ(−t) = λ(t)⁻¹` — every expansion is exactly undone by the matching
reduction. -/
lemma dilationFlow_neg (H t : ℝ) : dilationFlow H (-t) = (dilationFlow H t)⁻¹ := by
  simp [dilationFlow, ← Real.exp_neg]

/-- The flow is strictly positive — it stays in the multiplicative group. -/
lemma dilationFlow_pos (H t : ℝ) : 0 < dilationFlow H t := Real.exp_pos _

/-- **The dilation group** as a group homomorphism `(ℝ, +) →* ℝˣ`: the entropic-time translations
land in the units of the scale line — the new group, with the Noether charge `H` as generator. -/
def dilationGroupHom (H : ℝ) : Multiplicative ℝ →* ℝˣ where
  toFun t := Units.mk0 (dilationFlow H t.toAdd) (dilationFlow_pos H _).ne'
  map_one' := by
    ext
    simp [dilationFlow]
  map_mul' s t := by
    ext
    simp [dilationFlow_add]

/-- **The scale Lagrangian** `L(λ, λ̇) = ½(λ̇/λ)²` — the kinetic energy of the logarithm of the
scale. -/
def scaleLagrangian (x v : ℝ) : ℝ := (v / x) ^ 2 / 2

/-- **[The Noether symmetry]** the scale Lagrangian is invariant under the dilation
`(λ, λ̇) ↦ (μλ, μλ̇)` — the hypothesis of Noether's theorem for the scale group. -/
lemma scaleLagrangian_dilation_invariant (mu x v : ℝ) (hmu : mu ≠ 0) :
    scaleLagrangian (mu * x) (mu * v) = scaleLagrangian x v := by
  unfold scaleLagrangian
  rw [mul_div_mul_left _ _ hmu]

/-- **[Noether's theorem for the dilation]** along any solution of the scale Euler–Lagrange
equation `λ̈λ = λ̇²`, the Noether charge `Q = λ̇/λ` is conserved: `dQ/dt = 0`. -/
theorem noether_dilation_charge (lam lam' lam'' : ℝ → ℝ) (t : ℝ)
    (hd : HasDerivAt lam (lam' t) t) (hd' : HasDerivAt lam' (lam'' t) t)
    (hEL : lam'' t * lam t = lam' t ^ 2) (hne : lam t ≠ 0) :
    HasDerivAt (fun u => lam' u / lam u) 0 t := by
  have h := hd'.div hd hne
  have hz : (lam'' t * lam t - lam' t * lam' t) / lam t ^ 2 = 0 := by
    rw [hEL]
    ring
  rwa [hz] at h

/-- **[The orbit carries the charge `H`]** along the group orbit `λ₀·e^{Ht}` the logarithm grows
linearly with slope exactly the generator: `d(log λ)/dt = H` — the conserved Noether charge *is*
the group parameter. -/
theorem dilationFlow_log_derivative (H lam0 t : ℝ) (h0 : 0 < lam0) :
    HasDerivAt (fun u => Real.log (lam0 * dilationFlow H u)) H t := by
  have hfun : (fun u => Real.log (lam0 * dilationFlow H u))
      = fun u => Real.log lam0 + H * u := by
    funext u
    rw [dilationFlow, Real.log_mul h0.ne' (Real.exp_ne_zero _), Real.log_exp]
  rw [hfun]
  simpa using ((hasDerivAt_id t).const_mul H).const_add (Real.log lam0)

/-- **[The entropic-horizon decay is a group orbit]** the entropic-time energy decay
`H_R(τ) = H_R(0)·e^{−2τ}` of `ComplexNoetherChargeEntropicHorizon` is the dilation orbit with
generator `H = −2` — the arc's time evolution already moves along the new group. -/
lemma entropicEnergyDecay_eq_dilationFlow (HR0 τ : ℝ) :
    entropicEnergyDecay HR0 τ = HR0 * dilationFlow (-2) τ := rfl


/-! ## §B — the invariant scale metric -/

/-- **The scale distance** `d(x, y) = |log(x/y)|` — the metric of the scale line, measuring
expansions and reductions by their exact logarithmic ratio. -/
def scaleDistance (x y : ℝ) : ℝ := |Real.log (x / y)|

/-- **[Reflexivity]** `d(x, x) = 0`. -/
@[simp] lemma scaleDistance_self (x : ℝ) : scaleDistance x x = 0 := by
  rcases eq_or_ne x 0 with h | h <;> simp [scaleDistance, h, div_self]

/-- **[Symmetry]** `d(x, y) = d(y, x)`. -/
lemma scaleDistance_comm (x y : ℝ) : scaleDistance x y = scaleDistance y x := by
  unfold scaleDistance
  rw [← abs_neg, ← Real.log_inv, inv_div]

/-- **[Triangle inequality]** `d(x, z) ≤ d(x, y) + d(y, z)` on the positive scale line. -/
lemma scaleDistance_triangle (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    scaleDistance x z ≤ scaleDistance x y + scaleDistance y z := by
  have hsplit : Real.log (x / z) = Real.log (x / y) + Real.log (y / z) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  unfold scaleDistance
  rw [hsplit]
  exact abs_add_le _ _

/-- **[Separation]** `d(x, y) = 0 ↔ x = y` on the positive scale line. -/
lemma scaleDistance_eq_zero_iff (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    scaleDistance x y = 0 ↔ x = y := by
  unfold scaleDistance
  rw [abs_eq_zero]
  constructor
  · intro h
    have hexp := Real.exp_log (show (0 : ℝ) < x / y by positivity)
    rw [h, Real.exp_zero] at hexp
    exact (div_eq_one_iff_eq hy.ne').mp hexp.symm
  · intro h
    rw [h, div_self hy.ne', Real.log_one]

/-- **[The dilation group acts by isometries]** `d(μx, μy) = d(x, y)`: expanding or reducing every
scale by the same group element moves nothing — the metric under which "expands–reduces but
calculations keep exact". -/
theorem dilation_isometry (mu x y : ℝ) (hmu : mu ≠ 0) :
    scaleDistance (mu * x) (mu * y) = scaleDistance x y := by
  unfold scaleDistance
  rw [mul_div_mul_left _ _ hmu]

/-- **[Exact transport to the line]** `d(x, y) = dist (log x) (log y)`: the logarithm is an exact
isometry from the multiplicative scale line onto the standard additive line — calculations
transport with no loss. -/
theorem scaleDistance_eq_dist_log (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    scaleDistance x y = dist (Real.log x) (Real.log y) := by
  unfold scaleDistance
  rw [Real.log_div hx.ne' hy.ne', Real.dist_eq]

/-- **[The entropic proper distance is the scale metric]** `r = λ_C·d(K, 1)`: the entropic-time
separation `r = λ_C·log K` of `EntropicProperDistance` is exactly the invariant scale distance of
the Schmidt number from unity, in Compton wavelengths. -/
theorem entropicProperDistance_eq_scaleDistance (m c ħ η : ℝ) (hη : 0 < η) :
    entropicProperDistance m c ħ η
      = comptonWavelength m c ħ * scaleDistance (schmidtNumber η) 1 := by
  unfold entropicProperDistance scaleDistance
  rw [div_one, abs_of_nonneg (Real.log_nonneg (schmidtNumber_gt_one η hη).le)]

/-- **[Separations of scales]** `|r − r'| = λ_C·d(K, K')`: differences of entropic proper distances
measure the invariant scale distance between the two Schmidt numbers — the dilation group relates
entangled configurations isometrically. -/
theorem entropicProperDistance_sub (m c ħ η η' : ℝ) (hη : 0 < η) (hη' : 0 < η')
    (hlam : 0 ≤ comptonWavelength m c ħ) :
    |entropicProperDistance m c ħ η - entropicProperDistance m c ħ η'|
      = comptonWavelength m c ħ * scaleDistance (schmidtNumber η) (schmidtNumber η') := by
  have hK : (0 : ℝ) < schmidtNumber η := lt_trans one_pos (schmidtNumber_gt_one η hη)
  have hK' : (0 : ℝ) < schmidtNumber η' := lt_trans one_pos (schmidtNumber_gt_one η' hη')
  unfold entropicProperDistance scaleDistance
  rw [← mul_sub, abs_mul, abs_of_nonneg hlam, Real.log_div hK.ne' hK'.ne']


/-! ## §C — the lattice ladder -/

/-- **[One blocking step has unit length]** `d(2, 1) = log 2` — the length of the lattice blocking
`a ↦ 2a` in the invariant metric. -/
lemma scaleDistance_two_one : scaleDistance 2 1 = Real.log 2 := by
  unfold scaleDistance
  rw [div_one, abs_of_nonneg (Real.log_nonneg one_le_two)]

/-- **[The blocking step is position-independent]** `d(2a, a) = d(2, 1)`: the lattice blocking has
the *same exact length from every lattice spacing* — it is one and the same isometry of the
dilation group, which is why blocked calculations stay exact. -/
theorem blockspin_step_isometric (a : ℝ) (ha : a ≠ 0) :
    scaleDistance (2 * a) a = scaleDistance 2 1 := by
  have h := dilation_isometry a 2 1 ha
  rw [mul_one, mul_comm a 2] at h
  exact h

/-- **[The renormalization ladder is an arithmetic progression]** `d(2ⁿa, a) = n·log 2`: `n`
blocking steps land at exactly `n` times the unit step — the block-spin ladder of lattice QCD
walks the scale line in equal exact strides, with no accumulating error. -/
theorem blockspin_ladder (n : ℕ) (a : ℝ) (ha : 0 < a) :
    scaleDistance (2 ^ n * a) a = n * Real.log 2 := by
  unfold scaleDistance
  rw [mul_div_assoc, div_self ha.ne', mul_one, Real.log_pow,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two))]


/-! ## §D — the `√2` half-step and the holographic radial direction -/

/-- **[`√2` sits half a blocking step from unity]** `d(√2, 1) = ½·d(2, 1)`: the point `√2` — the
Banach–Stone critical distortion, the Johnson–Lindenstrauss endpoint `1 + (√2 − 1)`, and the
dual-sphere orthogonality chord — is exactly the midpoint of the first lattice blocking step in
the invariant metric. -/
theorem sqrtTwo_half_blockspin :
    scaleDistance (Real.sqrt 2) 1 = (1 / 2) * scaleDistance 2 1 := by
  unfold scaleDistance
  rw [div_one, div_one, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (Real.log_nonneg one_le_two),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log 2 / 2)]
  ring

/-- **[The Banach–Stone critical distortion is the half-step]** for the threshold witness `M` with
`M⁴ = 2` (`VectorBanachStoneDistortion.critical_distortion_iff`), the critical distortion `M²`
sits at `d(M², 1) = ½·d(2, 1)` — half a lattice blocking step. -/
theorem critical_distortion_half_blockspin (M : ℝ) (hM : 0 < M) (hM4 : M ^ 4 = 2) :
    scaleDistance (M ^ 2) 1 = (1 / 2) * scaleDistance 2 1 := by
  have hM2 : M ^ 2 = Real.sqrt 2 := by
    rw [show (2 : ℝ) = M ^ 4 from hM4.symm, show M ^ 4 = (M ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hM2]
  exact sqrtTwo_half_blockspin

/-- **[The dual-sphere chord is the half-step]** the dimensional-scaling factor
`scalingFactor 2 = √2` — the chord between orthogonal directions of the dual sphere
(`dualSphere_orthogonal_chord`) and the `λ_D = √D` rung of the scaling functor tower — sits at
half a blocking step: `d(scalingFactor 2, 1) = ½·d(2, 1)`. -/
theorem scalingFactor_half_blockspin :
    scaleDistance (scalingFactor 2) 1 = (1 / 2) * scaleDistance 2 1 := by
  have h : scalingFactor 2 = Real.sqrt 2 := by
    unfold scalingFactor
    norm_num
  rw [h]
  exact sqrtTwo_half_blockspin

/-- **[The AdS radial arclength is the scale metric]** `∫_a^b dr/r = d(b, a)`: the hyperbolic
radial line element `dr/r` of the holographic direction integrates exactly to the invariant scale
distance — the radial coordinate of `AdS/CFT` *is* the scale line of the dilation group, along
which the dimensional-reduction modules run. -/
theorem adsRadial_arclength (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, x⁻¹) = scaleDistance b a := by
  rw [integral_inv_of_pos ha (lt_of_lt_of_le ha hab)]
  unfold scaleDistance
  rw [abs_of_nonneg (Real.log_nonneg ((one_le_div ha).mpr hab))]

/-- **[The holographic RG shift is an isometry]** `∫_{μa}^{μb} dr/r = ∫_a^b dr/r`: sliding a
radial interval outward or inward by a dilation leaves its arclength exactly unchanged — the
holographic renormalization flow moves along orbits of the group without distorting the metric. -/
theorem adsRadial_dilation_invariant (mu a b : ℝ) (hmu : 0 < mu) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in mu * a..mu * b, x⁻¹) = ∫ x in a..b, x⁻¹ := by
  rw [adsRadial_arclength a b ha hab,
    adsRadial_arclength (mu * a) (mu * b) (by positivity)
      (mul_le_mul_of_nonneg_left hab hmu.le),
    dilation_isometry mu b a hmu.ne']


/-! ## §E — the bundled metric space and the group as isometries -/

/-- **The scale line** — the positive reals carrying the invariant `scaleDistance` as a bundled
metric (a type synonym, so the induced Euclidean subspace metric does not interfere). -/
def ScaleLine : Type := {x : ℝ // 0 < x}

namespace ScaleLine

/-- **The invariant metric, bundled**: `ScaleLine` is a genuine `MetricSpace` under
`scaleDistance` — the metric axioms of §B assembled into the structure downstream developments
can use directly. -/
noncomputable instance : MetricSpace ScaleLine where
  dist a b := scaleDistance a.1 b.1
  dist_self a := scaleDistance_self a.1
  dist_comm a b := scaleDistance_comm a.1 b.1
  dist_triangle a b c := scaleDistance_triangle a.1 b.1 c.1 a.2 b.2 c.2
  eq_of_dist_eq_zero {a b} h :=
    Subtype.ext ((scaleDistance_eq_zero_iff a.1 b.1 a.2 b.2).mp h)

/-- **[The exact log transport, bundled]** `log : ScaleLine ≃ᵢ ℝ` — an isometry *equivalence*
onto the standard line: every computation on the scale line transports to ordinary real
arithmetic and back with zero loss. -/
noncomputable def logEquiv : ScaleLine ≃ᵢ ℝ where
  toFun a := Real.log a.1
  invFun t := ⟨Real.exp t, Real.exp_pos t⟩
  left_inv a := Subtype.ext (Real.exp_log a.2)
  right_inv t := Real.log_exp t
  isometry_toFun := Isometry.of_dist_eq fun a b =>
    (scaleDistance_eq_dist_log a.1 b.1 a.2 b.2).symm

/-- **[The dilation, bundled]** each group element `μ > 0` acts on the scale line as an isometry
equivalence — the expansion `x ↦ μx` with exact inverse `x ↦ μ⁻¹x`. -/
noncomputable def dilation (mu : ℝ) (hmu : 0 < mu) : ScaleLine ≃ᵢ ScaleLine where
  toFun a := ⟨mu * a.1, mul_pos hmu a.2⟩
  invFun a := ⟨mu⁻¹ * a.1, mul_pos (inv_pos.mpr hmu) a.2⟩
  left_inv a := Subtype.ext (by
    show mu⁻¹ * (mu * a.1) = a.1
    rw [← mul_assoc, inv_mul_cancel₀ hmu.ne', one_mul])
  right_inv a := Subtype.ext (by
    show mu * (mu⁻¹ * a.1) = a.1
    rw [← mul_assoc, mul_inv_cancel₀ hmu.ne', one_mul])
  isometry_toFun := Isometry.of_dist_eq fun a b =>
    dilation_isometry mu a.1 b.1 hmu.ne'

/-- **[The action is the group law]** composing the bundled dilations multiplies the scale
factors: `dilation ν ≫ dilation μ = dilation (μν)`. -/
lemma dilation_trans (mu nu : ℝ) (hmu : 0 < mu) (hnu : 0 < nu) :
    (dilation nu hnu).trans (dilation mu hmu) = dilation (mu * nu) (mul_pos hmu hnu) :=
  IsometryEquiv.ext fun a => Subtype.ext
    (show mu * (nu * a.1) = mu * nu * a.1 from (mul_assoc mu nu a.1).symm)

/-- **[The Noether flow acts by isometries]** the one-parameter dilation flow of §A is a
one-parameter group of isometries of the scale line: `t ↦ dilation (e^{Ht})` turns time
translation into isometry composition. -/
lemma dilationFlow_isometry_add (H s t : ℝ) :
    dilation (dilationFlow H (s + t)) (dilationFlow_pos H _)
      = (dilation (dilationFlow H s) (dilationFlow_pos H _)).trans
          (dilation (dilationFlow H t) (dilationFlow_pos H _)) :=
  IsometryEquiv.ext fun a => Subtype.ext (by
    show dilationFlow H (s + t) * a.1 = dilationFlow H t * (dilationFlow H s * a.1)
    rw [dilationFlow_add]
    ring)

/-- **[The dilation is conjugate to a translation]** `logEquiv (dilation μ a) = log μ + logEquiv a`:
through the exact log transport every expansion–reduction becomes an ordinary translation of the
real line — the strongest form of "expands and reduces while calculations stay exact". -/
lemma logEquiv_dilation (mu : ℝ) (hmu : 0 < mu) (a : ScaleLine) :
    logEquiv (dilation mu hmu a) = Real.log mu + logEquiv a := by
  show Real.log (mu * a.1) = Real.log mu + Real.log a.1
  exact Real.log_mul hmu.ne' a.2.ne'

end ScaleLine


/-! ## §F — the Tsirelson and Coxeter rungs of the ladder -/

/-- **[Tsirelson sits one-and-a-half blocking steps out]** `d(2√2, 1) = (3/2)·d(2, 1)`: the
Tsirelson bound `2√2` — twice the critical distortion
(`tsirelson_eq_two_mul_critical_distortion`) — lies exactly three half-steps up the lattice
ladder from unity. -/
theorem tsirelson_three_half_steps :
    scaleDistance (2 * Real.sqrt 2) 1 = (3 / 2) * scaleDistance 2 1 := by
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  unfold scaleDistance
  rw [div_one, div_one,
    Real.log_mul two_ne_zero (Real.sqrt_ne_zero'.mpr two_pos),
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg hlog, abs_of_nonneg (by linarith)]
  ring

/-- **[The Coxeter `n = 4` rung is the half-step]** `d(2cos(π/4), 1) = ½·d(2, 1)`: the Coxeter
ladder value `2cos(π/4) = √2` (`critical_distortion_eq_two_cos_pi_div_four`) is the same
half-blocking-step point — the angular ladder of the Banach–Stone arc and the multiplicative
ladder of the lattice meet at the critical distortion. -/
theorem coxeter_rung_half_blockspin :
    scaleDistance (2 * Real.cos (Real.pi / 4)) 1 = (1 / 2) * scaleDistance 2 1 := by
  rw [Real.cos_pi_div_four,
    show (2 : ℝ) * (Real.sqrt 2 / 2) = Real.sqrt 2 by ring]
  exact sqrtTwo_half_blockspin

/-- **[The blocking ladder is a geodesic line]** `d(2ʳ, 2ˢ) = |r − s|·log 2`: the continuous
family `r ↦ 2ʳ` parametrizes a geodesic of the scale metric — the integer blockings of
`blockspin_ladder`, the `√2 = 2^{1/2}` half-step, and the Tsirelson point `2√2 = 2^{3/2}` are all
rungs of one exact geodesic, at parameters `n`, `1/2`, and `3/2`. -/
theorem blockspin_geodesic (r s : ℝ) :
    scaleDistance ((2 : ℝ) ^ r) ((2 : ℝ) ^ s) = |r - s| * Real.log 2 := by
  unfold scaleDistance
  rw [← Real.rpow_sub two_pos, Real.log_rpow two_pos, abs_mul,
    abs_of_nonneg (Real.log_nonneg one_le_two)]

/-- **[The geometric mean is the metric midpoint]** `d(√(xy), x) = d(√(xy), y) = ½·d(x, y)`: the
geometric mean of two scales is exactly equidistant from both in the invariant metric — the
general law behind the `√2 = √(1·2)` half-step, and the reason renormalization interpolates
scales geometrically. -/
theorem geometricMean_midpoint (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    scaleDistance (Real.sqrt (x * y)) x = (1 / 2) * scaleDistance x y
      ∧ scaleDistance (Real.sqrt (x * y)) y = (1 / 2) * scaleDistance x y := by
  have hxy : (0 : ℝ) < x * y := mul_pos hx hy
  have hlog : Real.log (Real.sqrt (x * y)) = (Real.log x + Real.log y) / 2 := by
    rw [Real.log_sqrt hxy.le, Real.log_mul hx.ne' hy.ne']
  constructor
  · unfold scaleDistance
    rw [Real.log_div (Real.sqrt_ne_zero'.mpr hxy) hx.ne', hlog,
      Real.log_div hx.ne' hy.ne',
      show (Real.log x + Real.log y) / 2 - Real.log x
          = -(Real.log x - Real.log y) / 2 by ring,
      abs_div, abs_neg, abs_two]
    ring
  · unfold scaleDistance
    rw [Real.log_div (Real.sqrt_ne_zero'.mpr hxy) hy.ne', hlog,
      Real.log_div hx.ne' hy.ne',
      show (Real.log x + Real.log y) / 2 - Real.log y
          = (Real.log x - Real.log y) / 2 by ring,
      abs_div, abs_two]
    ring

/-! ## §G — SU(2) lattice gauge theory on the dilation group (Mathur, hep-lat/0405008)

Mathur's prepotential formulation gives SU(2) lattice gauge theory an `SU(2) ⊗ U(1)` gauge group:
each link carries a `U(1)` phase `a† ↦ e^{iθ}a†`, `b† ↦ e^{−iθ}b†` (his Eq. 12) whose Gauss law is
the occupation matching `N_a = N_b` (Eq. 10). Complexifying the phase, `θ ↦ −iHt`, turns the link
`U(1)` into the entropic-time **dilation flow** of §A acting with generator `H·(N_a − N_b)`: the
physical Hilbert space is exactly the *fixed-point set* of the flow, and the Gauss-violating
charged sectors run along the §B metric at speed `|charge|`. The su(2) side lives on the Bargmann
carrier (`BargmannFockCCR.schwinger_raise_lower` etc.), the singlet on the `ε`-determinant
(`SuNTensorDecomposition.su2_singlet_bilinear_invariant`), and the state counting below closes the
paper's construction. -/

/-- **[The abelian Gauss law is dilation invariance]** a link state with occupation numbers
`(N_a, N_b)` is invariant under the entropic-time dilation flow with generator `N_a − N_b` for all
times *iff* `N_a = N_b` — Mathur's `U(1)` Gauss law (Eq. 10) selects exactly the fixed points of
the dilation group: the physical Hilbert space of SU(2) lattice gauge theory is the
dilation-invariant sector. -/
theorem gauss_iff_dilation_invariant (Na Nb : ℕ) :
    (∀ t : ℝ, dilationFlow ((Na : ℝ) - Nb) t = 1) ↔ Na = Nb := by
  constructor
  · intro h
    have h1 := h 1
    rw [dilationFlow, mul_one, Real.exp_eq_one_iff, sub_eq_zero] at h1
    exact_mod_cast h1
  · intro h t
    rw [h, sub_self, dilationFlow, zero_mul, Real.exp_zero]

/-- **[Charged sectors run along the metric at speed `|charge|`]** a Gauss-violating link sector
of `U(1)` charge `q` moves through the invariant scale metric at exactly `|q|·|t|` — physical
(charge-zero) states stand still, and each unit of charge is one unit of geodesic speed. -/
theorem chargedSector_scaleDistance (q t : ℝ) :
    scaleDistance (dilationFlow q t) 1 = |q * t| := by
  unfold scaleDistance dilationFlow
  rw [div_one, Real.log_exp]

/-- **[The transverse gluon count]** Mathur's orthonormal physical basis carries `4d − 3` quantum
numbers per site, of which the `U(1)` Gauss law fixes `d`: the remainder is `3(d − 1)` — the
`dim su(2) = 3` polarizations times the `d − 1` transverse directions of the SU(2) gluons. -/
theorem transverse_gluon_count (d : ℕ) (hd : 1 ≤ d) : 4 * d - 3 - d = 3 * (d - 1) := by
  omega

/-- **[The overcomplete labels are the pair linkings]** the gauge-invariant (but overcomplete)
basis of Mathur's Eq. 18 is labelled by `N_d = d(2d − 1)` integers `l_{ij}` at each site — exactly
the number of unordered pairs among the `2d` link legs meeting there, `C(2d, 2)`: the dual
description of the Wilson-loop basis. -/
theorem pair_invariant_count (d : ℕ) : d * (2 * d - 1) = (2 * d).choose 2 := by
  have h2 : 2 * d * (2 * d - 1) = 2 * (d * (2 * d - 1)) := by ring
  rw [Nat.choose_two_right, h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-! ## §H — the Kogut–Susskind strong-coupling spectrum (Jones–Kogut–Sinclair 1979)

Jones–Kogut–Sinclair (Z. Phys. C 3 (1979) 29) compute the hadron spectrum of the Kogut–Susskind
Hamiltonian `W = (2a/g²)H = W_el + x·W_q − 2x²·W_mag` (their Eq. 1.5, `x = 1/g²` — the
strong-coupling expansion runs *up* the §C scale ladder toward the continuum). Exact content
formalized below: the zeroth-order level structure and its crossing in the irrelevant coupling `A`
(Eqs. 1.7), the second-order masses `ω_N = 13.5x²`, `ω_meson = 22.5x²` and their `5/3` ratio
(Eqs. 2.8–2.9), the complete fourth-order graph sums (Eqs. 3.1–3.3, 3.5–3.7, at the paper's
vacuum-subtracted `N = 0` evaluation) which reproduce the printed series coefficients *exactly*
— including the equal `π/ρ/ω` spacing `−27/80` — and the `(2,1)` Padé matching algebra behind the
continuum extrapolation (Eqs. 3.9). **Honest layering**: the graph *values* are the paper's
(deriving them needs the full degenerate-perturbation machinery); the sums, ratios, crossings and
Padé algebra are theorems. The sixth-order coefficients are printed as truncated decimals and the
Goldstone indication (`ω_π` Padé numerator vanishing at `x² ≈ 1.86`, `ω_N`'s never) stays at
docstring level. The baryon composite `X = ⅙ε_{ijk}χᵢχⱼχₖ` being again a canonical fermion
(their Eq. 2.5) is recorded, not yet formalized. -/

/-- **The zeroth-order `q q̄` energy** `ω⁰ = 4/3 + 68A` (Eq. 1.7a): a quark pair joined by one flux
link, in the presence of the irrelevant four-fermion coupling `A`. -/
def quarkPairEnergy (A : ℝ) : ℝ := 4 / 3 + 68 * A

/-- **The zeroth-order `N N̄` energy** `ω⁰ = 180A` (Eq. 1.7b): three quarks and three antiquarks on
adjacent sites — fluxless, since each triple is a colour singlet. -/
def baryonPairEnergy (A : ℝ) : ℝ := 180 * A

/-- **[The level crossing]** the fluxless `N N̄` states lie below the flux-carrying `q q̄` states
exactly when `112A < 4/3` — the paper's dichotomy between the additive-quark-model regime
(`112A > 4/3`) and the degenerate regime studied at `A = 0`. -/
theorem level_crossing_iff (A : ℝ) :
    baryonPairEnergy A < quarkPairEnergy A ↔ 112 * A < 4 / 3 := by
  unfold baryonPairEnergy quarkPairEnergy
  constructor <;> intro h <;> linarith

/-- **[The crossing point]** at `A = 1/84` the two zeroth-order levels are exactly degenerate. -/
theorem level_crossing_point : baryonPairEnergy (1 / 84) = quarkPairEnergy (1 / 84) := by
  norm_num [baryonPairEnergy, quarkPairEnergy]

/-- **[The `ξ` threshold]** in the paper's variable `ξ = 51A`, the crossing condition reads
`ξ < 17/28 ≈ 0.61` — the boundary used throughout their §4. -/
theorem xi_threshold (A : ℝ) : 51 * A < 17 / 28 ↔ 112 * A < 4 / 3 := by
  constructor <;> intro h <;> linarith

/-- **The second-order nucleon mass** `ω_N = 13.5x² = (27/2)x²` (Eq. 2.8), from the effective
Hamiltonian on the fluxless sector. -/
def nucleonMassSecondOrder (x : ℝ) : ℝ := 27 / 2 * x ^ 2

/-- **The second-order meson mass** `ω_meson = 22.5x² = (45/2)x²` (Eq. 2.9): the `N N̄` pair one
link apart — the `π, ρ, ω` multiplet, degenerate at this order. -/
def mesonMassSecondOrder (x : ℝ) : ℝ := 45 / 2 * x ^ 2

/-- **[The strong-coupling mass ratio is `5/3`]** `ω_meson/ω_N = 5/3` at second order, for every
coupling — the zeroth-order value toward which the unreliable low-order Padé ratios collapse. -/
theorem strong_coupling_mass_ratio (x : ℝ) (hx : x ≠ 0) :
    mesonMassSecondOrder x / nucleonMassSecondOrder x = 5 / 3 := by
  unfold mesonMassSecondOrder nucleonMassSecondOrder
  field_simp
  ring

/-- **The nucleon fourth-order graph sum** (Eqs. 3.1a–c, 3.2a–d and the subtraction 3.3, at the
vacuum-subtracted evaluation `N = 0`): three effective-Hamiltonian graphs, four explicit
quark-flux graphs, and the Brillouin–Wigner denominator subtraction. -/
def nucleonFourthOrderGraphs : ℝ :=
  -(30 / 144) * (27 ^ 2 / 8)
    + 36 / 180 * (27 ^ 2 / 8)
    - 6 / 144 * (27 ^ 2 / 8)
    - 2 * 11 * 12 * 9 / (2 * (4 / 3) ^ 3)
    + 2 * 10 * 9 * 6 / (2 * (4 / 3) ^ 3)
    + 6 * 12 / (4 / 3) ^ 3
    - 30 * 3 / (2 * (4 / 3) ^ 3)
    + 36 * 9 / (4 / 3) ^ 3

/-- **[The graphs sum to the printed series]** the eight nucleon graphs total exactly
`−(27/2)·(1539/160)` — i.e. `ω_N = 13.5x²(1 − 9.61875x² + …)` (Eq. 3.4) with
`9.61875 = 1539/160` exact. -/
theorem nucleon_fourth_order :
    nucleonFourthOrderGraphs = -(27 / 2) * (1539 / 160) := by
  norm_num [nucleonFourthOrderGraphs]

/-- **The meson brace graphs** (Eqs. 3.5e–g): the three channel-dependent effective-Hamiltonian
graphs whose weights `(e, f, g)` distinguish `π (−6, 4, 3)`, `ρ (2, 0, −1)`, `ω (10, −4, −5)`. -/
def mesonBraceGraphs (e f g : ℝ) : ℝ :=
  e * -(1 / 144) * (27 ^ 2 / 8) + f * -(1 / 108) * (27 ^ 2 / 8) + g * -(1 / 180) * (27 ^ 2 / 8)

/-- **The channel-independent meson fourth-order graphs** (Eqs. 3.5a–d, 3.6a–g and the
subtraction 3.7, at `N = 0`). -/
def mesonCommonFourthOrderGraphs : ℝ :=
  -(42 / 144) * (27 ^ 2 / 8)
    - 4 / 108 * (27 ^ 2 / 8)
    + 57 / 180 * (27 ^ 2 / 8)
    - 2 * 292 * 9 / (2 * (4 / 3) ^ 3)
    + 2 * 10 * 16 * 6 / (2 * (4 / 3) ^ 3)
    + 11 * 12 / (4 / 3) ^ 3
    + 4 * 11 * 9 / (2 * (4 / 3) ^ 3)
    - 12 / (4 / 3) ^ 3
    - 10 * 3 / (2 * (4 / 3) ^ 3)
    - 50 * 3 / (2 * (4 / 3) ^ 3)
    + 100 * 9 / (4 / 3) ^ 3

/-- **[The pion series]** common graphs plus the `π` braces give exactly `−(45/2)·(4089/400)` —
`ω_π = 22.5x²(1 − 10.2225x² + …)` (Eq. 3.8a) with `10.2225 = 4089/400` exact. -/
theorem pion_fourth_order :
    mesonCommonFourthOrderGraphs + mesonBraceGraphs (-6) 4 3
      = -(45 / 2) * (4089 / 400) := by
  norm_num [mesonCommonFourthOrderGraphs, mesonBraceGraphs]

/-- **[The rho series]** `ω_ρ = 22.5x²(1 − 10.2075x² + …)` (Eq. 3.8b), `10.2075 = 4083/400`. -/
theorem rho_fourth_order :
    mesonCommonFourthOrderGraphs + mesonBraceGraphs 2 0 (-1)
      = -(45 / 2) * (4083 / 400) := by
  norm_num [mesonCommonFourthOrderGraphs, mesonBraceGraphs]

/-- **[The omega series]** `ω_ω = 22.5x²(1 − 10.1925x² + …)` (Eq. 3.8c), `10.1925 = 4077/400`. -/
theorem omega_fourth_order :
    mesonCommonFourthOrderGraphs + mesonBraceGraphs 10 (-4) (-5)
      = -(45 / 2) * (4077 / 400) := by
  norm_num [mesonCommonFourthOrderGraphs, mesonBraceGraphs]

/-- **[The `π/ρ/ω` spectrum is equally spaced at fourth order]** both splittings equal `−27/80`:
`ω_π < ω_ρ < ω_ω` in exact arithmetic progression — the entire channel dependence sits in the
three brace graphs, and it is linear. -/
theorem meson_equal_spacing :
    mesonBraceGraphs (-6) 4 3 - mesonBraceGraphs 2 0 (-1) = -(27 / 80)
      ∧ mesonBraceGraphs 2 0 (-1) - mesonBraceGraphs 10 (-4) (-5) = -(27 / 80) := by
  constructor <;> norm_num [mesonBraceGraphs]

/-- **[The `(2,1)` Padé matches through fourth order]** for a series `1 + c₂x² + c₄x⁴` the Padé
approximant `(1 + (c₂ − c₄/c₂)x²)/(1 + (−c₄/c₂)x²)` of the paper's Eq. 3.9 agrees with the series
up to an explicit `x⁶` remainder — the algebra behind the continuum extrapolation and the
Goldstone-pion diagnosis (`ω_π`'s numerator develops a zero, `ω_N`'s cannot). -/
theorem pade21_agrees_to_fourth (c2 c4 x : ℝ) (hc : c2 ≠ 0) :
    1 + (c2 - c4 / c2) * x ^ 2
      - (1 + -(c4 / c2) * x ^ 2) * (1 + c2 * x ^ 2 + c4 * x ^ 4)
      = c4 ^ 2 / c2 * x ^ 6 := by
  field_simp
  ring

/-- **The second-order `N N̄` energy at coupling `A`** (Eqs. 4.2a–d, vacuum-subtracted `N = 0`):
the four second-order graphs of their §4, with the irrelevant coupling `A` entering through the
energy denominators. -/
noncomputable def baryonPairSecondOrder (A : ℝ) : ℝ :=
  -(42 * 3) / (4 / 3 + 56 * A) - 4 * 3 / (4 / 3 + 44 * A) - 3 / (4 / 3 - 52 * A)
    + 57 * 3 / (4 / 3 + 68 * A)

/-- **[The `A → 0` limit recovers the degenerate meson mass]** the four `A ≠ 0` graphs of §4
collapse at `A = 0` to exactly `45/2` — the `ω_meson = 22.5x²` of Eq. 2.9: the two calculations
(effective-Hamiltonian at `A = 0`, direct perturbation at `A ≠ 0`) agree exactly where they
meet. -/
theorem baryonPair_secondOrder_at_zero :
    baryonPairSecondOrder 0 = mesonMassSecondOrder 1 := by
  norm_num [baryonPairSecondOrder, mesonMassSecondOrder]

/-! ### The sixth-order numerics, the `(2,1)` Padé data, and the Goldstone zero (Eqs. 3.4/3.8/3.9)

The sixth-order coefficients are printed to six decimals (`113.558467` etc.) — taken here as the
exact rationals they print, the paper's Eq. 3.9 Padé data satisfies exact relations: every Padé
*numerator* coefficient is the exact decimal sum `a = c₂ + b` (`pade_numerators_exact`), every
*denominator* coefficient rounds `−c₄/c₂` to within `10⁻⁶` (`pade_denominators_round`) — the four
series and the four approximants are one consistent data set. The **Goldstone diagnosis**: the
pion Padé numerator `1 − 0.538093x²` vanishes exactly at `x² = 10⁶/538093 ≈ 1.8584`
(`pion_goldstone_zero`), while the nucleon numerator `1 + 2.187199x²` is strictly positive for
every real `x` (`nucleon_numerator_never_zero`) — massless pion, massive nucleon: the Goldstone
realization of chiral symmetry in the continuum limit. **Honest note**: the paper's quoted mass
ratios at the pion zero (`m_ρ/m_N = .074968`, `m_ω/m_N = .069323`) do *not* reproduce from
ratios of the printed `(2,1)` approximants (which give `.0450` and `.0416`); their evaluation
method is not recoverable from the text, so those two numbers are left unformalized. -/

/-- **[The Padé numerators are exact decimal sums]** in each channel the Eq. 3.9 numerator
coefficient is exactly `c₂ + b` — nucleon `−9.61875 + 11.805949 = 2.187199`, pion
`−10.2225 + 9.684407 = −0.538093`, rho `−10.2075 + 9.730592 = −0.476908`, omega
`−10.1925 + 9.710877 = −0.481623`. -/
theorem pade_numerators_exact :
    ((-9.61875 : ℚ) + 11.805949 = 2.187199)
      ∧ ((-10.2225 : ℚ) + 9.684407 = -0.538093)
      ∧ ((-10.2075 : ℚ) + 9.730592 = -0.476908)
      ∧ ((-10.1925 : ℚ) + 9.710877 = -0.481623) := by
  norm_num

/-- **[The Padé denominators round `−c₄/c₂`]** in each channel the printed denominator coefficient
agrees with `−c₄/c₂` (the `(2,1)` matching value of `pade21_agrees_to_fourth`) to within `10⁻⁶` —
the printed sixth-order coefficients and the printed Padé data are mutually consistent. -/
theorem pade_denominators_round :
    |(113.558467 : ℚ) / 9.61875 - 11.805949| < 1 / 1000000
      ∧ |(98.998850 : ℚ) / 10.2225 - 9.684407| < 1 / 1000000
      ∧ |(99.325022 : ℚ) / 10.2075 - 9.730592| < 1 / 1000000
      ∧ |(98.978114 : ℚ) / 10.1925 - 9.710877| < 1 / 1000000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_sub_lt_iff] <;> constructor <;> norm_num

/-- **[The pion mass vanishes]** the pion Padé numerator has the exact zero `x² = 10⁶/538093`,
within `10⁻⁴` of the paper's `1.8584` — large enough to be consistent with the true zero at
`x² → ∞`, the chiral-Goldstone pion. -/
theorem pion_goldstone_zero :
    ((1 : ℚ) - 0.538093 * (1000000 / 538093) = 0)
      ∧ |(1000000 : ℚ) / 538093 - 1.8584| < 1 / 10000 := by
  constructor
  · norm_num
  · rw [abs_sub_lt_iff]
    constructor <;> norm_num

/-- **[The nucleon mass never vanishes]** the nucleon Padé numerator `1 + 2.187199x²` is strictly
positive for every real coupling — the nucleon stays massive while the pion goes massless: the
Goldstone dichotomy of the spectrum. -/
theorem nucleon_numerator_never_zero (x : ℝ) : 0 < 1 + 2.187199 * x ^ 2 := by
  positivity

/-! ## §I — Hamer–Kogut series analysis and the Ising exact results (PRB 20 (1979) 3859)

Hamer–Kogut analyze the strong-coupling series of the quantum-Hamiltonian Ising, `O(2)`, `O(3)`,
`O(4)` spin chains with the toolkit formalized here at exact level: on a pure power law
`b(x_c − x)^{−γ}` the **ratio method** (their Eq. 3.3) is an identity, not an asymptotic —
`a_{n+1}·(n+1)x_c = a_n·(γ+n)` (`ratio_method_exact`) — the **linear extrapolant** (Eq. 3.4)
recovers `1/x_c` *exactly* (`linear_extrapolant_exact`) and the **slope estimator** (Eq. 3.5)
recovers `γ − 1` exactly (`slope_estimate_exact`); the **Dlog Padé** target (Eq. 3.6) is the
simple pole `γ/(x_c − x)` (`dlog_power_law`); and the **Euler transformation** `z = x/(x+1)`
(Eq. 3.7) maps `x = ∞` to `z = 1` with exact inverse (`euler_transform_maps_infinity`,
`euler_transform_inverse`). The **Ising exact results**: the printed magnetization series
(Eq. 3.13) is coefficient-for-coefficient the binomial expansion of `M = (1 − x⁻²)^{1/8}`
(Eq. 3.14) — `−1/2³, −7/2⁷, −35/2¹⁰, −805/2¹⁵` are exactly `(±)∏(1/8 − i)/k!`
(`ising_magnetization_binomial`): critical point `x_c = 1`, magnetization index `β = 1/8`. The
scaling laws (Eq. 3.16) at `d = 2, ν = 1, β = 1/8` then force `η = 1/4, γ = 7/4, α = 0, δ = 15`
(`ising_scaling_laws`) — all the exact Ising indices. The specific-heat ratio law
`ρ_n = (2n−1)(2n+1)/(2n(2n+2))` (the elliptic-integral structure of the transverse-Ising ground
energy, reproducing Table I/III digit-for-digit) has slope sequence exactly `−(4n+1)/(4(n+1))`
(`ising_slope_sequence`, matching Table III's `−0.625, −0.75, −0.8125, …`) with limit `−1`
(`ising_slope_limit`): `α − 1 = −1`, the logarithmically divergent specific heat, consistent with
`α = 2 − νd = 0`. **Honest layering**: the `O(2)` essential-singularity exponent `σ = 0.7 ± 0.1`,
`η = 0.26 ± 0.03`, and the Migdal `O(4)`↔`SU(2)`-gauge β-function connection are error-barred
numerics and stay at docstring level. -/

/-- **The Taylor coefficients of the pure power law** `(x_c − x)^{−γ}` (up to the overall
constant): `a_n = ∏_{i<n}(γ+i) / (n!·x_cⁿ)`. -/
noncomputable def powerLawCoeff (gam xc : ℝ) (n : ℕ) : ℝ :=
  (∏ i ∈ Finset.range n, (gam + i)) / n.factorial / xc ^ n

/-- **[The ratio method is exact on the power law]** `a_{n+1}·(n+1)·x_c = a_n·(γ+n)` — Hamer–Kogut
Eq. 3.3 sharpened from asymptotic to identity: the coefficient ratios of a pure power-law
singularity carry `x_c` and `γ` exactly. -/
theorem ratio_method_exact (gam xc : ℝ) (hxc : xc ≠ 0) (n : ℕ) :
    powerLawCoeff gam xc (n + 1) * ((n + 1) * xc)
      = powerLawCoeff gam xc n * (gam + n) := by
  unfold powerLawCoeff
  rw [Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : xc ^ n ≠ 0 := pow_ne_zero n hxc
  have h3 : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **[The linear extrapolant is exact]** on the power-law ratios `ρ_n = (1 + (γ−1)/n)/x_c`,
Hamer–Kogut's Eq. 3.4 extrapolant `n·ρ_n − (n−1)·ρ_{n−1}` returns `1/x_c` *identically* — the
critical-point estimator has zero error on the model singularity. -/
theorem linear_extrapolant_exact (gam xc n : ℝ) (hxc : xc ≠ 0) (hn : n ≠ 0)
    (hn1 : n - 1 ≠ 0) :
    n * ((1 + (gam - 1) / n) / xc) - (n - 1) * ((1 + (gam - 1) / (n - 1)) / xc)
      = 1 / xc := by
  field_simp
  ring

/-- **[The slope estimator is exact]** `g_n = n(ρ_n·x_c − 1) = γ − 1` identically — Eq. 3.5's
critical-index estimator on the model singularity. -/
theorem slope_estimate_exact (gam xc n : ℝ) (hxc : xc ≠ 0) (hn : n ≠ 0) :
    n * ((1 + (gam - 1) / n) / xc * xc - 1) = gam - 1 := by
  field_simp
  ring

/-- **[The Dlog of the power law is a simple pole]** `D log (x_c − x)^{−γ} = γ/(x_c − x)` —
Eq. 3.6: the Padé method reads `x_c` off the pole position and `γ` off the residue. -/
theorem dlog_power_law (gam xc x : ℝ) (h : x < xc) :
    HasDerivAt (fun t => -gam * Real.log (xc - t)) (gam / (xc - x)) x := by
  have h1 : HasDerivAt (fun t : ℝ => xc - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub xc
  have h2 : HasDerivAt (fun t => Real.log (xc - t)) ((xc - x)⁻¹ * -1) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (by linarith : xc - x ≠ 0)).comp x h1
  have h3 := h2.const_mul (-gam)
  have hd : gam / (xc - x) = -gam * ((xc - x)⁻¹ * -1) := by
    field_simp
  rw [hd]
  exact h3

/-- **[The Euler transformation inverts exactly]** `z = x/(x+1)` has exact inverse
`x = z/(1−z)` — Eq. 3.7's change of variable loses nothing. -/
theorem euler_transform_inverse (x : ℝ) (hx : x ≠ -1) :
    x / (x + 1) / (1 - x / (x + 1)) = x := by
  have h : x + 1 ≠ 0 := fun hc => hx (by linarith)
  field_simp
  ring

/-- **[The Euler transformation maps `x = ∞` to `z = 1`]** — the strong-coupling limit is brought
to a finite point, the device behind the sharpened `O(2)` analysis. -/
theorem euler_transform_maps_infinity :
    Filter.Tendsto (fun x : ℝ => x / (x + 1)) Filter.atTop (nhds 1) := by
  have h : ∀ᶠ x : ℝ in Filter.atTop, x / (x + 1) = 1 - 1 / (x + 1) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have : (x + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [Filter.tendsto_congr' h]
  have h0 : Filter.Tendsto (fun x : ℝ => 1 / (x + 1)) Filter.atTop (nhds 0) := by
    simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop 1 Filter.tendsto_id)
  simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)).sub h0

/-- **The binomial coefficients of** `(1 − u)^{1/8}`: `c_k = (−1)^k·∏_{i<k}(1/8 − i)/k!`. -/
def isingMagnetizationCoeff (k : ℕ) : ℚ :=
  (-1) ^ k * (∏ i ∈ Finset.range k, ((1 : ℚ) / 8 - i)) / k.factorial

/-- **[The Ising magnetization series is the `1/8`-binomial]** the printed Eq. 3.13 coefficients
`−1/2³, −7/2⁷, −35/2¹⁰, −805/2¹⁵` are exactly the binomial expansion of `M = (1 − x⁻²)^{1/8}`
(Eq. 3.14) through the printed order: critical point `x_c = 1` and magnetization index `β = 1/8`,
both exact. -/
theorem ising_magnetization_binomial :
    isingMagnetizationCoeff 1 = -(1 / 2 ^ 3)
      ∧ isingMagnetizationCoeff 2 = -(7 / 2 ^ 7)
      ∧ isingMagnetizationCoeff 3 = -(35 / 2 ^ 10)
      ∧ isingMagnetizationCoeff 4 = -(805 / 2 ^ 15) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [isingMagnetizationCoeff, Finset.prod_range_succ, Finset.prod_range_zero,
      Nat.factorial]

/-- **[The scaling laws force all the Ising indices]** at `d = 2` with the exact `ν = 1` (from the
terminating gap `F = 2(1−x)`) and `β = 1/8` (from `ising_magnetization_binomial`), the scaling
relations of Eq. 3.16 determine `η = 1/4`, `γ = 7/4`, `α = 0`, `δ = 15` — every remaining Ising
index, exactly. -/
theorem ising_scaling_laws (eta gam alpha delta : ℚ)
    (hbeta : (1 : ℚ) / 8 = 1 / 2 * 1 * (2 - 2 + eta))
    (hgamma : gam = 1 * (2 - eta))
    (halpha : alpha = 2 - 1 * 2)
    (hdelta : delta = (2 + 2 - eta) / (2 - 2 + eta)) :
    eta = 1 / 4 ∧ gam = 7 / 4 ∧ alpha = 0 ∧ delta = 15 := by
  have he : eta = 1 / 4 := by linarith
  refine ⟨he, ?_, by linarith, ?_⟩
  · rw [he] at hgamma
    linarith
  · rw [he] at hdelta
    norm_num at hdelta
    exact hdelta

/-- **[The specific-heat slope sequence, exactly]** the transverse-Ising specific-heat ratios
`ρ_n = (2n−1)(2n+1)/(2n(2n+2))` (the elliptic-integral structure reproducing Tables I/III
digit-for-digit) give the slope estimator `g_n = n(ρ_n − 1) = −(4n+1)/(4(n+1))` identically —
Table III's `−0.625, −0.75, −0.8125, −0.85, …` in closed form. -/
theorem ising_slope_sequence (n : ℝ) (hn : 0 < n) :
    n * ((2 * n - 1) * (2 * n + 1) / (2 * n * (2 * n + 2)) - 1)
      = -(4 * n + 1) / (4 * (n + 1)) := by
  have h1 : (2 * n : ℝ) ≠ 0 := by positivity
  have h2 : (2 * n + 2 : ℝ) ≠ 0 := by positivity
  have h3 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **[The slope limit is `−1`: the specific heat diverges logarithmically]**
`g_n → α − 1 = −1`, i.e. `α = 0` — the exact ratio-method limit agrees with the scaling-law value
`α = 2 − νd = 0` of `ising_scaling_laws`: the Ising specific heat is a logarithm, and the paper's
Table III estimate `g = −1.01 ± 0.02` sits on the exact value. -/
theorem ising_slope_limit :
    Filter.Tendsto (fun n : ℝ => -(4 * n + 1) / (4 * (n + 1))) Filter.atTop
      (nhds (-1)) := by
  have h : ∀ᶠ n : ℝ in Filter.atTop,
      -(4 * n + 1) / (4 * (n + 1)) = -1 + 3 / 4 * (1 / (n + 1)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with n hn
    have h3 : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [Filter.tendsto_congr' h]
  have h0 : Filter.Tendsto (fun n : ℝ => 1 / (n + 1)) Filter.atTop (nhds 0) := by
    simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop 1 Filter.tendsto_id)
  have h1 := h0.const_mul (3 / 4 : ℝ)
  simpa using (tendsto_const_nhds (x := (-1 : ℝ)) (f := Filter.atTop)).add h1

/-! ### Welds: criticality measured in the repo's own carriers

The §I toolkit is not stand-alone: the approach to a critical point runs along the same geometry
as everything above. The Dlog pole *integrates to the invariant scale metric* — the distance to
criticality is a `scaleDistance`, computed by the very `adsRadial_arclength` of §D
(`dlog_pole_arclength`); the `α = 0` logarithmic specific heat of `ising_slope_limit` *is* that
metric distance (`log_specific_heat_distance`); the Euler transformation of Eq. 3.7 is the
hyperbolic square map `z = tanh²ρ` (`euler_transform_hyperbolic`), so at the Schmidt
parametrization the Euler variable is the squared vacuum-Bell decay `e^{−2r/λ_C}` of
`EntropicProperDistance` (`euler_variable_vacuumBell`); and the Ising order parameter measures the
entanglement boost — `M⁸ = 1 − K⁻² = 1/cosh²η` at `K = schmidtNumber η`, i.e. `M = γ^{−1/4}`
(`ising_magnetization_boost`), so the ordered phase is exactly the region of positive scale
distance from criticality (`ising_ordered_iff_entropic_distance`). -/

/-- **[The Dlog pole integrates to the scale metric]** `∫_a^b dt/(x_c − t) = d(x_c − a, x_c − b)`:
the logarithm of the power-law singularity accumulated between two couplings is the invariant
scale distance between their distances-to-criticality — the approach to a critical point runs
along the same geodesic as the §C blocking ladder and the §D holographic radial direction
(reusing `adsRadial_arclength`). -/
theorem dlog_pole_arclength (xc a b : ℝ) (hb : b < xc) (hab : a ≤ b) :
    (∫ t in a..b, (xc - t)⁻¹) = scaleDistance (xc - a) (xc - b) := by
  rw [intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) xc]
  exact adsRadial_arclength (xc - b) (xc - a) (by linarith) (by linarith)

/-- **[The logarithmic specific heat is the scale distance]** for `0 < x < x_c` the `α = 0`
divergence `log(x_c/(x_c − x))` equals `scaleDistance x_c (x_c − x)` — the Ising specific heat
(`ising_slope_limit`) grows as exactly the invariant metric distance of the coupling from
criticality. -/
theorem log_specific_heat_distance (xc x : ℝ) (h0 : 0 < x) (hx : x < xc) :
    Real.log (xc / (xc - x)) = scaleDistance xc (xc - x) := by
  unfold scaleDistance
  rw [abs_of_nonneg (Real.log_nonneg ((one_le_div (by linarith)).mpr (by linarith)))]

/-- **[The Euler transformation is the hyperbolic square map]** at `x = sinh²ρ` the Euler variable
of Eq. 3.7 is `z = tanh²ρ` — the same `tanh` carrier as the Schmidt/rapidity arc: the
strong-coupling limit `x = ∞` is the infinite-rapidity limit `z → 1`. -/
theorem euler_transform_hyperbolic (rho : ℝ) :
    Real.sinh rho ^ 2 / (Real.sinh rho ^ 2 + 1) = Real.tanh rho ^ 2 := by
  have hc : Real.cosh rho ≠ 0 := (Real.cosh_pos rho).ne'
  have hsq : Real.sinh rho ^ 2 + 1 = Real.cosh rho ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq rho
    linarith
  rw [hsq, Real.tanh_eq_sinh_div_cosh, div_pow]

/-- **[The Euler variable is the squared vacuum-Bell decay]** at the Schmidt parametrization
`x = sinh²η` the Euler-transformed coupling equals `e^{−2r/λ_C}` — the square of the vacuum Bell
decay at the entropic proper distance (`entropicProperDistance_vacuumBell`): Hamer–Kogut's
convergence device is motion along the entropic-distance direction. -/
theorem euler_variable_vacuumBell (m c ħ η : ℝ) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    Real.sinh η ^ 2 / (Real.sinh η ^ 2 + 1)
      = Real.exp (-(entropicProperDistance m c ħ η / comptonWavelength m c ħ)) ^ 2 := by
  rw [euler_transform_hyperbolic, entropicProperDistance_vacuumBell m c ħ η hη hlam]

/-- **[The Ising magnetization is an inverse boost power]** at coupling `K = schmidtNumber η` the
eighth power of the magnetization `M = (1 − K⁻²)^{1/8}` is `1/cosh²η` — `M = γ^{−1/4}` with
`γ = cosh η` the boost factor of the entanglement reparametrization: the order parameter is a
pure function of the Schmidt boost. -/
theorem ising_magnetization_boost (η : ℝ) (hη : 0 < η) :
    1 - ((schmidtNumber η)⁻¹) ^ 2 = (Real.cosh η ^ 2)⁻¹ := by
  unfold schmidtNumber
  have hs : Real.sinh η ≠ 0 := (Real.sinh_pos_iff.mpr hη).ne'
  have hc : Real.cosh η ≠ 0 := (Real.cosh_pos η).ne'
  have hid := Real.cosh_sq_sub_sinh_sq η
  field_simp
  linarith

/-- **[The ordered phase is positive entropic distance]** for `K ≥ 1` the Ising order parameter
`1 − K⁻²` is positive exactly when `scaleDistance K 1` is — magnetization is nonzero precisely at
nonzero invariant distance from the critical point `x_c = 1`, which sits at the identity of the
dilation group. -/
theorem ising_ordered_iff_entropic_distance (K : ℝ) (hK : 1 ≤ K) :
    0 < 1 - K⁻¹ ^ 2 ↔ 0 < scaleDistance K 1 := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
  have habs : 0 ≤ scaleDistance K 1 := abs_nonneg _
  have hiff : scaleDistance K 1 = 0 ↔ K = 1 := scaleDistance_eq_zero_iff K 1 hK0 one_pos
  constructor
  · intro h
    rcases habs.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hK1 : K = 1 := hiff.mp heq.symm
      rw [hK1] at h
      norm_num at h
  · intro h
    have hne : K ≠ 1 := fun he => absurd (hiff.mpr he) (ne_of_gt h)
    have h1 : 1 < K := lt_of_le_of_ne hK (Ne.symm hne)
    have hinv : K⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right
      exact h1
    have hpos : (0 : ℝ) < K⁻¹ := inv_pos.mpr hK0
    nlinarith

/-! ### The Pfeuty gap, derived

`ising_scaling_laws` took `ν = 1` from the *quoted* terminating gap series `F = 2(1−x)`
(Hamer–Kogut Eq. 3.15). Here it is derived: Pfeuty's exact transverse-Ising dispersion
`ε(k)² = 4(1 + x² − 2x·cos k)` is minimized exactly at `k = 0` (nothing but `cos k ≤ 1`), where
it equals `4(1−x)²` — so the mass gap is exactly `2(1−x)` on `0 ≤ x ≤ 1`, vanishing linearly at
`x_c = 1`: the critical point and `ν = 1` are theorems, not inputs. -/

/-- **[The dispersion is bounded below by its `k = 0` value]** `(1−x)² ≤ 1 + x² − 2x·cos k` for
`x ≥ 0` — the difference is `2x(1 − cos k) ≥ 0`. -/
theorem ising_dispersion_ge (x k : ℝ) (hx : 0 ≤ x) :
    (1 - x) ^ 2 ≤ 1 + x ^ 2 - 2 * x * Real.cos k := by
  nlinarith [Real.cos_le_one k]

/-- **[The bound is attained at `k = 0`]** the dispersion minimum is `(1−x)²`. -/
theorem ising_dispersion_min (x : ℝ) :
    1 + x ^ 2 - 2 * x * Real.cos 0 = (1 - x) ^ 2 := by
  rw [Real.cos_zero]
  ring

/-- **[The mass gap is exactly `2(1−x)`]** Eq. 3.15 *derived*: on `0 ≤ x ≤ 1` the gap
`ε(0) = √(4(1 + x² − 2x·cos 0)) = 2(1−x)` — the terminating series, with `x_c = 1` and the
linear vanishing `ν = 1` that feeds `ising_scaling_laws`. -/
theorem ising_gap_derived (x : ℝ) (hx1 : x ≤ 1) :
    Real.sqrt (4 * (1 + x ^ 2 - 2 * x * Real.cos 0)) = 2 * (1 - x) := by
  rw [Real.cos_zero, show 4 * (1 + x ^ 2 - 2 * x * 1) = (2 * (1 - x)) ^ 2 by ring,
    Real.sqrt_sq (by linarith)]

/-! ### The essential-singularity discriminator (Eqs. 4.3–4.5)

The paper's central O(2) diagnostic: for an *essential* singularity `f = exp(b(x_c−x)^{−σ})` the
Dlog is a **power** `bσ(x_c−x)^{−σ−1}` (Eq. 4.4) — stronger than any simple pole — while the
*double* Dlog is a simple pole with residue exactly `1+σ` (Eq. 4.5). Against `dlog_power_law`
(simple pole, residue `γ`) this is the exact dichotomy: Dlog-Padé residue `γ` ⇒ algebraic
singularity; Dlog²-Padé residue `1+σ` ⇒ Kosterlitz–Thouless essential singularity. -/

/-- **[Eq. 4.4: the essential singularity's Dlog is a power]**
`D[b(x_c−x)^{−σ}] = bσ(x_c−x)^{−σ−1}` — the logarithmic derivative of
`f = exp(b(x_c−x)^{−σ})` diverges as a power, not a simple pole. -/
theorem essential_dlog (b sig xc x : ℝ) (h : x < xc) :
    HasDerivAt (fun t => b * (xc - t) ^ (-sig))
      (b * sig * (xc - x) ^ (-sig - 1)) x := by
  have hne : xc - x ≠ 0 := by
    have : (0 : ℝ) < xc - x := by linarith
    exact this.ne'
  have h1 : HasDerivAt (fun t : ℝ => xc - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub xc
  have h2 : HasDerivAt (fun t : ℝ => (xc - t) ^ (-sig))
      (-sig * (xc - x) ^ (-sig - 1) * -1) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_rpow_const (p := -sig) (Or.inl hne)).comp x h1
  have h3 := h2.const_mul b
  have hd : b * sig * (xc - x) ^ (-sig - 1)
      = b * (-sig * (xc - x) ^ (-sig - 1) * -1) := by ring
  rw [hd]
  exact h3

/-- **[Eq. 4.5: the double Dlog has residue `1+σ`]** `D log(bσ(x_c−x)^{−σ−1}) = (1+σ)/(x_c−x)` —
one more logarithmic derivative turns the essential singularity into a simple pole whose residue
reads off the exponential index: the discriminator between `γ` (algebraic) and `1+σ`
(Kosterlitz–Thouless). -/
theorem essential_dlog2 (b sig xc x : ℝ) (hb : 0 < b) (hs : 0 < sig) (h : x < xc) :
    HasDerivAt (fun t => Real.log (b * sig * (xc - t) ^ (-sig - 1)))
      ((1 + sig) / (xc - x)) x := by
  have hev : (fun t => Real.log (b * sig * (xc - t) ^ (-sig - 1)))
      =ᶠ[nhds x] fun t => Real.log (b * sig) + (-sig - 1) * Real.log (xc - t) := by
    filter_upwards [eventually_lt_nhds h] with t ht
    have hpos : (0 : ℝ) < xc - t := by linarith
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hpos _).ne',
      Real.log_rpow hpos]
  have h1 : HasDerivAt (fun t : ℝ => xc - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub xc
  have h2 : HasDerivAt (fun t => Real.log (xc - t)) ((xc - x)⁻¹ * -1) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (by
        have : (0 : ℝ) < xc - x := by linarith
        exact this.ne')).comp x h1
  have h3 := (h2.const_mul (-sig - 1)).const_add (Real.log (b * sig))
  have hd : (1 + sig) / (xc - x) = Real.log (b * sig) * 0 + (-sig - 1) * ((xc - x)⁻¹ * -1) := by
    have : (0 : ℝ) < xc - x := by linarith
    field_simp
    ring
  rw [show (fun t => Real.log (b * sig) + (-sig - 1) * Real.log (xc - t)) = _ from rfl] at h3
  exact (h3.congr_of_eventuallyEq hev).congr_deriv (by
    have hpos : (0 : ℝ) < xc - x := by linarith
    field_simp
    ring)


/-! ### The weak-coupling Euler identity (Eq. 5.1)

Asymptotic freedom gives `ξ ~ exp(2π/g)` with `g² = 2/x`; under the Euler map `z = x/(x+1)` the
complement is exactly `1 − z = 1/(x+1)`, so `2π/g = √2·π·√x = √2·π·(1−z)^{−1/2}·√(x/(x+1))` with
the last factor tending to `1` — the weak-coupling essential index is `1+σ = 3/2` *exactly*, which
is how the paper rules the spurious `O(3)/O(4)` weak-coupling transitions in `z` to be artifacts. -/

/-- **[The Euler complement]** `1 − z = 1/(x+1)` exactly. -/
theorem euler_transform_complement (x : ℝ) (hx : x ≠ -1) :
    1 - x / (x + 1) = 1 / (x + 1) := by
  have h : x + 1 ≠ 0 := fun hc => hx (by linarith)
  field_simp
  ring

/-- **[The asymptotic-freedom exponent]** `2π/g = √2·π·√x` at `g = √(2/x)`. -/
theorem weak_coupling_exponent (x : ℝ) (hx : 0 < x) :
    2 * Real.pi / Real.sqrt (2 / x) = Real.sqrt 2 * Real.pi * Real.sqrt x := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hxs : Real.sqrt x ≠ 0 := by positivity
  field_simp
  linear_combination -(Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

/-- **[The complement's inverse square root]** `(1−z)^{−1/2} = √(x+1)`. -/
theorem complement_inv_sqrt (x : ℝ) (hx : 0 < x) :
    1 / Real.sqrt (1 - x / (x + 1)) = Real.sqrt (x + 1) := by
  rw [euler_transform_complement x (by linarith), one_div, ← Real.sqrt_inv]
  congr 1
  rw [one_div, inv_inv]

/-- **[The exponent factorizes across the Euler map]** `√x = √(x+1)·√(x/(x+1))` — so
`2π/g = √2π·(1−z)^{−1/2}·√(x/(x+1))`, the Eq. 5.1 form. -/
theorem weak_coupling_bridge (x : ℝ) (hx : 0 < x) :
    Real.sqrt x = Real.sqrt (x + 1) * Real.sqrt (x / (x + 1)) := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ x + 1)]
  congr 1
  field_simp

/-- **[The residual factor tends to one]** `√(x/(x+1)) → 1` as `x → ∞`: in the weak-coupling limit
`2π/g ~ √2π(1−z)^{−1/2}` exactly — the essential index is `1+σ = 3/2`. -/
theorem weak_coupling_index_limit :
    Filter.Tendsto (fun x : ℝ => Real.sqrt (x / (x + 1))) Filter.atTop (nhds 1) := by
  have h2 : Filter.Tendsto Real.sqrt (nhds 1) (nhds 1) := by
    simpa using Real.continuous_sqrt.tendsto 1
  simpa [Function.comp_def] using h2.comp euler_transform_maps_infinity


/-! ### The `η`-extraction identity (Eq. 4.10) -/

/-- **[`−Dlogχ/DlogF = 2−η` on model power laws]** with `F = (x_c−x)^ν` (so `DlogF = −ν/(x_c−x)`
by `dlog_power_law`) and `χ = F^{−(2−η)} = (x_c−x)^{−ν(2−η)}` (so `Dlogχ = ν(2−η)/(x_c−x)`), the
ratio of the two Dlog residues is exactly `2−η` — the paper's Fig. 2 procedure for reading the
spin-spin correlation index off the series is an exact identity on the scaling hypothesis. -/
theorem eta_extraction (nu eta xc x : ℝ) (hnu : nu ≠ 0) (hx : x ≠ xc) :
    -(nu * (2 - eta) / (xc - x)) / (-nu / (xc - x)) = 2 - eta := by
  have hxc : xc - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp


/-! ### The quantum-statistical dictionary (Eqs. 2.1–2.2 and footnote 13)

`T` maps onto the coupling `x = 1/T`, and the statistical specific heat `c_h = −T·∂²𝔉/∂T²`
becomes a second `x`-derivative of the ground energy. The exact chain rules: the first
temperature derivative of `F(T) = ω(1/T)` is `−T⁻²·ω′(1/T)`
(`free_energy_temperature_deriv`), its second is `2T⁻³ω′ + T⁻⁴ω″`
(`specific_heat_dictionary`), and `−T·(that)` recast at `x = 1/T` is `−x²(2ω′ + xω″)` — the
Barber footnote-13 combination `ω₀′ + 2xω₀″` up to the lattice-constant normalization
(`specific_heat_barber_form`). -/

/-- **[First temperature derivative]** `d/dT ω(1/T) = −T⁻²·ω′(1/T)`. -/
theorem free_energy_temperature_deriv (w w1 : ℝ → ℝ) (T : ℝ) (hT : T ≠ 0)
    (hw : HasDerivAt w (w1 (1 / T)) (1 / T)) :
    HasDerivAt (fun S => w (1 / S)) (-(1 / T ^ 2) * w1 (1 / T)) T := by
  have hinv : HasDerivAt (fun S : ℝ => 1 / S) (-(1 / T ^ 2)) T := by
    simpa [one_div] using hasDerivAt_inv hT
  have hc := hw.comp T hinv
  simpa [Function.comp_def, mul_comm] using hc

/-- **[Second temperature derivative]** `d/dT [−T⁻²·ω′(1/T)] = 2T⁻³·ω′(1/T) + T⁻⁴·ω″(1/T)` —
the quantum specific heat `c_h = −T·(this)` in raw form. -/
theorem specific_heat_dictionary (w1 w2 : ℝ → ℝ) (T : ℝ) (hT : T ≠ 0)
    (hw1 : HasDerivAt w1 (w2 (1 / T)) (1 / T)) :
    HasDerivAt (fun S => -(1 / S ^ 2) * w1 (1 / S))
      (2 / T ^ 3 * w1 (1 / T) + 1 / T ^ 4 * w2 (1 / T)) T := by
  have hinv : HasDerivAt (fun S : ℝ => 1 / S) (-(1 / T ^ 2)) T := by
    simpa [one_div] using hasDerivAt_inv hT
  have hcomp : HasDerivAt (fun S => w1 (1 / S)) (-(1 / T ^ 2) * w2 (1 / T)) T := by
    have hc := hw1.comp T hinv
    simpa [Function.comp_def, mul_comm] using hc
  have hpow : HasDerivAt (fun S : ℝ => S ^ 2) (2 * T) T := by
    simpa using hasDerivAt_pow 2 T
  have hcoef : HasDerivAt (fun S : ℝ => -(1 / S ^ 2)) (2 / T ^ 3) T := by
    have hi := hpow.inv (pow_ne_zero 2 hT)
    have hn : HasDerivAt (fun S : ℝ => -((S ^ 2)⁻¹)) (-(-(2 * T) / (T ^ 2) ^ 2)) T := hi.neg
    have hval : -(-(2 * T) / (T ^ 2) ^ 2) = 2 / T ^ 3 := by
      field_simp
    have hfun : (fun S : ℝ => -(1 / S ^ 2)) = fun S : ℝ => -((S ^ 2)⁻¹) := by
      funext S
      rw [one_div]
    rw [hfun, ← hval]
    exact hn
  have hprod := hcoef.mul hcomp
  have hval2 : 2 / T ^ 3 * w1 (1 / T) + 1 / T ^ 4 * w2 (1 / T)
      = 2 / T ^ 3 * w1 (1 / T) + -(1 / T ^ 2) * (-(1 / T ^ 2) * w2 (1 / T)) := by
    field_simp
  rw [hval2]
  exact hprod

/-- **[The Barber footnote form]** `−T·(2T⁻³ω′ + T⁻⁴ω″) = −x²(2ω′ + xω″)` at `x·T = 1` —
the quantum specific heat in the coupling variable, footnote 13's `ω₀′ + 2xω₀″` combination. -/
theorem specific_heat_barber_form (T x w1v w2v : ℝ) (hT : T ≠ 0) (hx : x * T = 1) :
    -T * (2 / T ^ 3 * w1v + 1 / T ^ 4 * w2v) = -(x ^ 2) * (2 * w1v + x * w2v) := by
  have hxT : x = 1 / T := by
    field_simp
    linarith [hx]
  rw [hxT]
  field_simp

/-! ### The quantum Ising operator anchor (Eqs. 3.8–3.11)

The series of §I descend from the quantum Hamiltonian
`H = (g/2a)Σ[(1−σ₃) − xσ₁σ₁ + hσ₁]` (Eq. 3.8) on the repo's Pauli carrier. At `x⁻¹ = 0` (zero
temperature, Eq. 3.9) the per-bond operator is `1 − σ₁⊗σ₁`: below, the two `σ₁`-aligned states
(Eqs. 3.10a/b), their non-proportionality (the double degeneracy), the exact bond annihilation
for *both* alignments (spontaneously breakable ℤ₂), and the magnetization `M = −1` on the
down-state (Eq. 3.11). -/

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators Kronecker in
/-- **[Eq. 3.10a]** `σ₁|↑⟩ = |↑⟩`: the all-up `σ₁`-eigenstate. -/
theorem pauliX_ground_up : pauliX.mulVec ![1, 1] = ![1, 1] := by
  funext i
  fin_cases i <;> simp [pauliX, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators Kronecker in
/-- **[Eq. 3.10b]** `σ₁|↓⟩ = −|↓⟩`: the all-down eigenstate — the perturbation basis choice. -/
theorem pauliX_ground_down : pauliX.mulVec ![1, -1] = (-1 : ℂ) • ![1, -1] := by
  funext i
  fin_cases i <;> simp [pauliX, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **[The ground doublet]** the two `σ₁`-eigenstates are not proportional: the zeroth-order
ground space is doubly degenerate — the ℤ₂ the model spontaneously breaks. -/
theorem ising_ground_doublet : ¬∃ c : ℂ, (![1, -1] : Fin 2 → ℂ) = c • ![1, 1] := by
  rintro ⟨c, hc⟩
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp at h0 h1
  rw [← h0] at h1
  norm_num at h1

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators Kronecker in
/-- **[The Kronecker product acts factor-wise on product states]**
`(A ⊗ₖ B)·(v ⊗ w) = (A·v) ⊗ (B·w)` — the bond operator sees the two sites independently. -/
theorem kronecker_mulVec_prod {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) (v : Fin n → ℂ) (w : Fin m → ℂ) :
    (A ⊗ₖ B).mulVec (fun p => v p.1 * w p.2)
      = fun p => A.mulVec v p.1 * B.mulVec w p.2 := by
  funext p
  have hL : (A ⊗ₖ B).mulVec (fun q => v q.1 * w q.2) p
      = ∑ i : Fin n, ∑ j : Fin m, A p.1 i * B p.2 j * (v i * w j) := by
    simp [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  have hR : A.mulVec v p.1 * B.mulVec w p.2
      = ∑ i : Fin n, ∑ j : Fin m, A p.1 i * v i * (B p.2 j * w j) := by
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Finset.sum_mul_sum]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators Kronecker in
/-- **[Both alignments have zero bond energy]** for any `σ₁`-eigenstate `v` with eigenvalue
`ε² = 1`, the zeroth-order bond operator `1 − σ₁⊗σ₁` annihilates the product state `v ⊗ v`:
the all-up and all-down configurations are exactly degenerate ground states of Eq. 3.9 — the
spontaneously breakable ℤ₂ doublet. -/
theorem ising_bond_zero_energy (v : Fin 2 → ℂ) (eps : ℂ)
    (hv : pauliX.mulVec v = eps • v) (heps : eps ^ 2 = 1) :
    ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - pauliX ⊗ₖ pauliX).mulVec
        (fun p => v p.1 * v p.2)
      = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, kronecker_mulVec_prod, hv]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  have hfactor : eps * v p.1 * (eps * v p.2) = eps ^ 2 * (v p.1 * v p.2) := by ring
  rw [hfactor, heps]
  ring

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators in
/-- **[Eq. 3.11: the magnetization of the down-state is `−1`]**
`M = ⟨0|σ₁|0⟩/⟨0|0⟩ = −1` on the all-down eigenstate — the spontaneous value at `x⁻¹ = 0`,
whose strong-coupling continuation is the `(1 − x⁻²)^{1/8}` of `ising_magnetization_binomial`. -/
theorem ising_magnetization_down :
    dotProduct (![1, -1] : Fin 2 → ℂ) (pauliX.mulVec (![1, -1] : Fin 2 → ℂ))
      / dotProduct (![1, -1] : Fin 2 → ℂ) (![1, -1] : Fin 2 → ℂ) = -1 := by
  rw [pauliX_ground_down]
  simp [dotProduct, Fin.sum_univ_two]
  norm_num


/-! ### The binomial resummation (Eq. 3.14, analytically)

Mathlib's binomial series closes the loop: `(1 + z)^a` has the power series `binomialSeries ℂ a`
on the unit ball (`one_add_cpow_hasFPowerSeriesOnBall_zero`), whose `k`-th coefficient is
`Ring.choose a k`. The weld below identifies the printed strong-coupling coefficients with those
analytic ones — `isingMagnetizationCoeff k = (−1)^k·Ring.choose (1/8) k` — so Eq. 3.13 *is* the
expansion of `M = (1 − u)^{1/8}` (at `z = −u`, `u = x⁻²`, radius `1`, i.e. down to `x_c = 1`):
Eq. 3.14 as analysis, not just coefficient checks. -/

/-- **[The printed coefficients are the analytic binomial coefficients]**
`isingMagnetizationCoeff k = (−1)^k·Ring.choose (1/8) k`: the strong-coupling series of Eq. 3.13
carries exactly the `binomialSeries` coefficients of `(1+z)^{1/8}`, hence resums to
`M = (1−x⁻²)^{1/8}` on the unit ball by `one_add_cpow_hasFPowerSeriesOnBall_zero`. -/
theorem isingMagnetizationCoeff_eq_choose (k : ℕ) :
    isingMagnetizationCoeff k = (-1) ^ k * Ring.choose ((1 : ℚ) / 8) k := by
  unfold isingMagnetizationCoeff
  have hfact : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [div_eq_iff hfact]
  have hdesc := Ring.descPochhammer_eq_factorial_smul_choose (R := ℚ) ((1 : ℚ) / 8) k
  have hprod : (descPochhammer ℤ k).smeval ((1 : ℚ) / 8)
      = ∏ i ∈ Finset.range k, ((1 : ℚ) / 8 - i) := by
    rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, ← Polynomial.eval_map,
      descPochhammer_map, descPochhammer_eval_eq_prod_range]
  rw [hprod] at hdesc
  rw [hdesc]
  push_cast [nsmul_eq_mul]
  ring

/-! ## §K — the fine-structure ladder in the invariant metric

The atomic length hierarchy of `CasimirLengthHierarchy` — Bohr radius `a₀ = ƛ_C/α`, Compton
wavelength `ƛ_C`, Thomson radius `r_e = α·ƛ_C` (with `r_e = α²·a₀`, `thomson_eq_alpha_sq_bohr`)
— is a *geodesic ladder* of the §B scale metric with the fine-structure constant as its uniform
step. The Compton wavelength is the geometric mean of the outer rungs, `ƛ_C² = a₀·r_e`
(`compton_geometric_mean_of_ladder`), hence their exact metric *midpoint* by
`geometricMean_midpoint` (`compton_metric_midpoint` — pure reuse); and the rung length itself
recovers the constant: `α = exp(−d(ƛ_C, a₀))` (`alpha_isolated_from_ladder`) — a second exact
isolation of `α`, from length ratios in the invariant metric, complementing the charge/screen
route of `EntanglementScreenArea.fineStructure_from_screenBits`. -/

/-- **[The Compton wavelength is the geometric mean of the ladder]** `a₀·r_e = ƛ_C²`: the
fine-structure constant cancels between the two outer rungs. -/
theorem compton_geometric_mean_of_ladder (m c ħ α : ℝ) (hα : α ≠ 0) :
    bohrRadius m c ħ α * thomsonRadius m c ħ α = comptonWavelength m c ħ ^ 2 := by
  unfold bohrRadius thomsonRadius
  field_simp

/-- **[… in square-root form]** `ƛ_C = √(a₀·r_e)`. -/
theorem compton_sqrt_ladder (m c ħ α : ℝ) (hα : α ≠ 0)
    (hlc : 0 ≤ comptonWavelength m c ħ) :
    comptonWavelength m c ħ = Real.sqrt (bohrRadius m c ħ α * thomsonRadius m c ħ α) := by
  rw [compton_geometric_mean_of_ladder m c ħ α hα, Real.sqrt_sq hlc]

/-- **[The Compton wavelength is the metric midpoint of the ladder]** the Bohr and Thomson radii
are exactly equidistant from `ƛ_C` in the invariant scale metric, each at half the total rung —
`geometricMean_midpoint` instantiated on the atomic hierarchy. -/
theorem compton_metric_midpoint (m c ħ α : ℝ) (hα : 0 < α)
    (hlc : 0 < comptonWavelength m c ħ) :
    scaleDistance (comptonWavelength m c ħ) (bohrRadius m c ħ α)
        = 1 / 2 * scaleDistance (bohrRadius m c ħ α) (thomsonRadius m c ħ α)
      ∧ scaleDistance (comptonWavelength m c ħ) (thomsonRadius m c ħ α)
        = 1 / 2 * scaleDistance (bohrRadius m c ħ α) (thomsonRadius m c ħ α) := by
  have hb : 0 < bohrRadius m c ħ α := by
    unfold bohrRadius
    positivity
  have ht : 0 < thomsonRadius m c ħ α := by
    unfold thomsonRadius
    positivity
  have h := geometricMean_midpoint (bohrRadius m c ħ α) (thomsonRadius m c ħ α) hb ht
  rw [← compton_sqrt_ladder m c ħ α hα.ne' hlc.le] at h
  exact h

/-- **[The fine-structure constant isolated from the ladder]** `α = exp(−d(ƛ_C, a₀))`: the
invariant-metric distance from the Compton wavelength to the Bohr radius recovers the
fine-structure constant exactly — `α` from a ratio of measurable lengths, the metric route
complementing the charge/screen route of `fineStructure_from_screenBits`. -/
theorem alpha_isolated_from_ladder (m c ħ α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hlc : 0 < comptonWavelength m c ħ) :
    Real.exp (-scaleDistance (comptonWavelength m c ħ) (bohrRadius m c ħ α)) = α := by
  unfold scaleDistance bohrRadius
  rw [show comptonWavelength m c ħ / (comptonWavelength m c ħ / α) = α from by
    field_simp]
  rw [abs_of_nonpos (Real.log_nonpos hα.le hα1), neg_neg, Real.exp_log hα]

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
  Physlib.Thermodynamics in
/-- **[The two exact isolations agree]** — instantiating the ladder at the physical value
`α = e²/(4πε₀ℏc)` and chaining `alpha_isolated_from_ladder` with
`fineStructure_from_screenBits`: the exponentiated metric distance from the Compton wavelength
to the Bohr radius equals the charge/screen expression,

`exp(−d(ƛ_C, a₀)) = (e/m)²·(log K)² / (ε₀·G·N)`.

The fine-structure constant is eliminated entirely: an exact relation between measurable
lengths (left) and charge-to-mass ratio, Schmidt number, Newton constant and holographic bit
count (right) — the consistency condition tying the metric route to the screen route, and it is
dimensionless on both sides by `Units.PlanckUnitsInformation.ladderRatio_dimensionless` and
`alphaIsolation_dimensionless`. -/
theorem alpha_isolations_agree (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η)
    (hα : 0 < fineStructure e eps0 ħ c) (hα1 : fineStructure e eps0 ħ c ≤ 1)
    (hlc : 0 < comptonWavelength m c ħ) :
    Real.exp (-scaleDistance (comptonWavelength m c ħ)
        (bohrRadius m c ħ (fineStructure e eps0 ħ c)))
      = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
        / (eps0 * G
            * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [alpha_isolated_from_ladder m c ħ _ hα hα1 hlc]
  exact fineStructure_from_screenBits e eps0 m c ħ G η heps hm hc hħ hG hη

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

end

end
