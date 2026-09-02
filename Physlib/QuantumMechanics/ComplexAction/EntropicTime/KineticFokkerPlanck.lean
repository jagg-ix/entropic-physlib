/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

meta import Zil

/-!
# The kinetic Fokker–Planck equation — fundamental solution and hypocoercivity

The degenerate kinetic Fokker–Planck (Kolmogorov) equation carries two exact
structures, one per section below:

* `FundamentalSolution` — the Kolmogorov fundamental solution's algebra, on the
  Auscher–Imbert–Niebel baseline (arXiv:2403.17468): the drift group law, the
  quadratic form of the covariance, and its scaling.
* `Hypocoercivity` — the Dolbeault–Li φ-entropy method: the twisted Lyapunov
  functional satisfying `MᵀP + PM = −P` exactly, whence the sharp `e^{−t}` decay as an
  identity rather than an estimate, with the prefactor-3 bound.

The relativistic sibling with self-consistent fields and friction is
`Vlasov/RelativisticMaxwellFokkerPlanck`, whose growth envelope is the mirror of the
decay proved here.
-/

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck

section FundamentalSolution

/-!
# The kinetic Kolmogorov fundamental solution: Lyapunov structure, scaling, conservation

Auscher, Imbert and Niebel, *Fundamental solutions to Kolmogorov–Fokker–Planck equations
with rough coefficients: existence, uniqueness, upper estimates* (arXiv:2403.17468), build
their theory on the constant-coefficient Kolmogorov example: the explicit Gaussian kernel
whose covariance mixes position and velocity, the kinetic scaling `(t,x,v) ↦ (r²t, r³x, rv)`
that the class respects, the Gaussian upper bound whose exponent carries the *midpoint*
transport correction `x − t(v+v₀)/2`, and the conservation property that drives the Davies
`L²` decay.  The repository already holds the kernel itself
(`EntropicDynamicsLocalTimeFokkerPlanck` §E–F: Hörmander bracket, determinant `D²t⁴/3`,
positivity, smoothness).  This module adds the four structural facts of the paper's baseline
that were missing:

* **§A — the Lyapunov equation.**  The full covariance *matrix*
  `Σ(t) = [[2Dt³/3, Dt²], [Dt², 2Dt]]` (not just its determinant) satisfies the kinetic
  Lyapunov ODE `Σ' = AΣ + ΣAᵀ + 2Q`, with `A` the free-transport drift `[[0,1],[0,0]]` and
  `Q = diag(0, D)` the velocity-only noise.  This is *where* the covariance comes from:
  rank-one noise, spread into position by the same bracket that
  `kineticDiffusionTransportBracket_eq` generates.
* **§B — the midpoint completed square.**  The kernel's exponent is exactly
  `3(x − tv/2)²/(Dt³) + v²/(4Dt)`: the position variable is measured from the *midpoint*
  transport `tv/2`, which is the one-endpoint form of the paper's two-endpoint correction
  `x − x₀ − t(v+v₀)/2` in its Gaussian bounds.
* **§C — kinetic scaling covariance.**  Under `(t,x,v) ↦ (r²t, r³x, rv)` the exponent is
  *invariant* and the kernel picks up exactly `r⁻⁴` — the homogeneous weight of the kinetic
  measure `dx dv` under the paper's scaling, and the reason `t⁴` appears in the determinant.
* **§D — conservation.**  The kernel has unit mass (in iterated form), certifying the
  normalization `√3/(2πDt²)` that the repository's kernel carries.  Conservation is the
  input the paper feeds to Davies' method.

**Honest layering, with the search that backs it.**  This is the constant-coefficient
baseline, exactly.  The paper's actual subject — existence and uniqueness of
fundamental-solution *operators* for rough measurable coefficients, the Davies `L²` decay,
and the equivalence of Gaussian bounds with Moser's `L²–L∞` estimates — was searched for
before being declared absent: grep, filename search, and `#zil_query` under the
`davies/twist` and `moser/caccioppoli/de-giorgi` vocabularies return no formalization (the
repository's "Davies" citations are Davies–Fulling–Unruh; its "Moser" mention is a
docstring reference in the harmonic-gauge module).  The `hypocoercivity/villani` vocabulary
was equally empty when this module was written; that slot is now carried by
the `Hypocoercivity` section below (Dolbeault–Li 2018), which builds on this module.  The closest
existing infrastructure is the C0 contraction semigroup `QFT.PathIntegral.dampedHeatSemigroup`,
which is the natural weld target for a future operator-level formalization.  Conservation
was initially iterated-only; the same search discipline found the Fubini machinery present,
and §D′ now proves the joint-measure form outright.
-/

open Real
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck

/-! ### §A — the covariance matrix and its Lyapunov equation -/

/-- The position–position covariance `2Dt³/3` of the free kinetic process. -/
noncomputable def covXX (D t : ℝ) : ℝ := 2 * D * t ^ 3 / 3

/-- The position–velocity covariance `Dt²`. -/
noncomputable def covXV (D t : ℝ) : ℝ := D * t ^ 2

/-- The velocity–velocity covariance `2Dt`. -/
noncomputable def covVV (D t : ℝ) : ℝ := 2 * D * t

/-- **The kinetic Lyapunov equation, entry by entry**: the covariance solves
`Σ' = AΣ + ΣAᵀ + 2Q` for the free-transport drift `A = [[0,1],[0,0]]` and velocity-only
noise `Q = diag(0,D)`.  Written out, the right-hand side is
`[[2·covXV, covVV], [covVV, 2D]]`, and each entry's derivative matches:

* `covXX' = 2·covXV` — position variance grows only by feeding from the cross term;
* `covXV' = covVV` — the cross term grows only by feeding from velocity variance;
* `covVV' = 2D` — velocity variance alone is directly driven by the noise.

Rank-one noise cascades up to full-rank covariance through exactly the bracket that
`kineticDiffusionTransportBracket_eq` computes: this is Hörmander's condition made
quantitative. -/
theorem covariance_lyapunov (D t : ℝ) :
    HasDerivAt (covXX D) (2 * covXV D t) t
      ∧ HasDerivAt (covXV D) (covVV D t) t
      ∧ HasDerivAt (covVV D) (2 * D) t := by
  refine ⟨?_, ?_, ?_⟩
  · unfold covXX covXV
    have h := ((hasDerivAt_pow 3 t).const_mul (2 * D)).div_const 3
    exact h.congr_deriv (by push_cast; ring)
  · unfold covXV covVV
    have h := (hasDerivAt_pow 2 t).const_mul D
    exact h.congr_deriv (by push_cast; ring)
  · unfold covVV
    have h := (hasDerivAt_id t).const_mul (2 * D)
    exact h.congr_deriv (by ring)

/-- The covariance determinant `covXX·covVV − covXV²` is the repository's
`kineticKolmogorovCovDet D t = D²t⁴/3` — the matrix entries assemble to the determinant the
kernel already carries, with its hypoelliptic `t⁴`. -/
theorem covariance_det_weld (D t : ℝ) :
    covXX D t * covVV D t - covXV D t ^ 2 = kineticKolmogorovCovDet D t := by
  unfold covXX covXV covVV kineticKolmogorovCovDet
  ring

/-! ### §B — the midpoint completed square -/

/-- **The exponent in midpoint form**: the kernel's quadratic form is exactly

  `3(x − tv/2)²/(Dt³) + v²/(4Dt)`.

Position is measured from the midpoint transport `tv/2` — the one-endpoint instance of the
paper's Gaussian-bound correction `x − x₀ − t(v+v₀)/2` — and what remains in `v` is an
ordinary Gaussian of variance `2Dt`.  In particular the exponent is nonnegative wherever
`D,t > 0`, which the mixed form does not display. -/
theorem exponent_midpoint_form (D t x v : ℝ) (hD : D ≠ 0) (ht : t ≠ 0) :
    kineticKolmogorovExponent D t x v
      = 3 * (x - t * v / 2) ^ 2 / (D * t ^ 3) + v ^ 2 / (4 * D * t) := by
  unfold kineticKolmogorovExponent
  field_simp
  ring

/-- The exponent is nonnegative in the physical regime — immediate from the midpoint form,
invisible in the mixed-term form. -/
theorem exponent_nonneg (D t x v : ℝ) (hD : 0 < D) (ht : 0 < t) :
    0 ≤ kineticKolmogorovExponent D t x v := by
  rw [exponent_midpoint_form D t x v hD.ne' ht.ne']
  positivity

/-! ### §C — the kinetic scaling covariance -/

/-- **The kernel's exponent is invariant under the kinetic scaling**
`(t,x,v) ↦ (r²t, r³x, rv)` — the scaling under which the paper's whole equation class is
organized. -/
theorem exponent_kinetic_scaling (D t x v r : ℝ) (hr : r ≠ 0) :
    kineticKolmogorovExponent D (r ^ 2 * t) (r ^ 3 * x) (r * v)
      = kineticKolmogorovExponent D t x v := by
  unfold kineticKolmogorovExponent
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
    try ring

/-- **The kernel is homogeneous of weight `−4` under the kinetic scaling**: the exponent is
invariant and the prefactor scales as `r⁻⁴` — the weight of the phase-space measure `dx dv`
(position weight `3` plus velocity weight `1`), which is also the origin of the
hypoelliptic `t⁴` in the determinant. -/
theorem kernel_kinetic_scaling (D t x v r : ℝ) (hr : 0 < r) :
    kineticKolmogorovKernel D (r ^ 2 * t) (r ^ 3 * x, r * v)
      = r ^ (-4 : ℤ) * kineticKolmogorovKernel D t (x, v) := by
  rw [kineticKolmogorovKernel_factor, kineticKolmogorovKernel_factor,
    exponent_kinetic_scaling D t x v r hr.ne']
  unfold kineticKolmogorovPrefactor
  rw [zpow_neg, show ((4 : ℤ) : ℤ) = (4 : ℕ) from rfl, zpow_natCast]
  field_simp
  try ring

/-! ### §D — conservation -/

/-- The inner (position) integral at fixed velocity: shifting to the midpoint and applying
the one-dimensional Gaussian integral, the `x`-mass is `√(πDt³/3)` times the remaining
velocity Gaussian. -/
theorem kernel_integral_x (D t v : ℝ) (hD : 0 < D) (ht : 0 < t) :
    (∫ x : ℝ, kineticKolmogorovKernel D t (x, v))
      = kineticKolmogorovPrefactor D t * Real.sqrt (Real.pi * (D * t ^ 3) / 3)
          * Real.exp (-(v ^ 2 / (4 * D * t))) := by
  have hbpos : 0 < 3 / (D * t ^ 3) := by positivity
  have hrw : ∀ x : ℝ, kineticKolmogorovKernel D t (x, v)
      = kineticKolmogorovPrefactor D t * Real.exp (-(v ^ 2 / (4 * D * t)))
          * Real.exp (-(3 / (D * t ^ 3)) * (x - t * v / 2) ^ 2) := by
    intro x
    rw [kineticKolmogorovKernel_factor, exponent_midpoint_form D t x v hD.ne' ht.ne']
    rw [show -(3 * (x - t * v / 2) ^ 2 / (D * t ^ 3) + v ^ 2 / (4 * D * t))
        = (-(v ^ 2 / (4 * D * t))) + (-(3 / (D * t ^ 3)) * (x - t * v / 2) ^ 2) from by
      ring]
    rw [Real.exp_add]
    ring
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul]
  have hshift : (∫ x : ℝ, Real.exp (-(3 / (D * t ^ 3)) * (x - t * v / 2) ^ 2))
      = ∫ x : ℝ, Real.exp (-(3 / (D * t ^ 3)) * x ^ 2) :=
    MeasureTheory.integral_sub_right_eq_self (μ := MeasureTheory.volume)
      (fun y => Real.exp (-(3 / (D * t ^ 3)) * y ^ 2)) (t * v / 2)
  rw [hshift, integral_gaussian]
  rw [show Real.pi / (3 / (D * t ^ 3)) = Real.pi * (D * t ^ 3) / 3 from by
    field_simp]
  ring

/-- **Conservation: the kinetic Kolmogorov kernel has unit mass** (iterated form).  The
midpoint square carries the `x`-integral, the ordinary Gaussian carries the `v`-integral,
and the product of the two Gaussian masses is exactly the inverse of the kernel's
prefactor — certifying `√3/(2πDt²)` as *the* normalization.  Conservation is the property
the paper's Davies method runs on. -/
theorem kernel_conservation_iterated (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    (∫ v : ℝ, ∫ x : ℝ, kineticKolmogorovKernel D t (x, v)) = 1 := by
  have hrw : ∀ v : ℝ, (∫ x : ℝ, kineticKolmogorovKernel D t (x, v))
      = kineticKolmogorovPrefactor D t * Real.sqrt (Real.pi * (D * t ^ 3) / 3)
          * Real.exp (-(1 / (4 * D * t)) * v ^ 2) := by
    intro v
    rw [kernel_integral_x D t v hD ht]
    congr 1
    rw [show -(v ^ 2 / (4 * D * t)) = -(1 / (4 * D * t)) * v ^ 2 from by ring]
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul, integral_gaussian]
  rw [show Real.pi / (1 / (4 * D * t)) = Real.pi * (4 * D * t) from by field_simp]
  unfold kineticKolmogorovPrefactor
  rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
  have hAB : Real.pi * (D * t ^ 3) / 3 * (Real.pi * (4 * D * t))
      = (2 * Real.pi * D * t ^ 2) ^ 2 / 3 := by ring
  have hsq : Real.sqrt (Real.pi * (D * t ^ 3) / 3 * (Real.pi * (4 * D * t)))
      = 2 * Real.pi * D * t ^ 2 / Real.sqrt 3 := by
    rw [hAB, Real.sqrt_div (by positivity : (0:ℝ) ≤ (2 * Real.pi * D * t ^ 2) ^ 2),
      Real.sqrt_sq (by positivity)]
  rw [hsq]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-! ### §D′ — conservation in the joint measure: the Fubini form

The iterated statement above fenced its Fubini upgrade; the deep search the fence demanded
found the machinery present (`integrable_prod_iff`, `integral_prod`, Gaussian
integrability), so the fence is discharged by proving the theorem. -/

/-- **The velocity-midpoint completed square**: the same exponent, completed in `v` instead
of `x` — `(v − 3x/2t)²/(Dt) + 3x²/(4Dt³)`.  The two squares are the two Fubini orders. -/
theorem exponent_velocity_midpoint_form (D t x v : ℝ) (hD : D ≠ 0) (ht : t ≠ 0) :
    kineticKolmogorovExponent D t x v
      = (v - 3 * x / (2 * t)) ^ 2 / (D * t) + 3 * x ^ 2 / (4 * D * t ^ 3) := by
  unfold kineticKolmogorovExponent
  field_simp
  ring

/-- The inner (velocity) integral at fixed position. -/
theorem kernel_integral_v (D t x : ℝ) (hD : 0 < D) (ht : 0 < t) :
    (∫ v : ℝ, kineticKolmogorovKernel D t (x, v))
      = kineticKolmogorovPrefactor D t * Real.sqrt (Real.pi * (D * t))
          * Real.exp (-(3 * x ^ 2 / (4 * D * t ^ 3))) := by
  have hrw : ∀ v : ℝ, kineticKolmogorovKernel D t (x, v)
      = kineticKolmogorovPrefactor D t * Real.exp (-(3 * x ^ 2 / (4 * D * t ^ 3)))
          * Real.exp (-(1 / (D * t)) * (v - 3 * x / (2 * t)) ^ 2) := by
    intro v
    rw [kineticKolmogorovKernel_factor,
      exponent_velocity_midpoint_form D t x v hD.ne' ht.ne']
    rw [show -((v - 3 * x / (2 * t)) ^ 2 / (D * t) + 3 * x ^ 2 / (4 * D * t ^ 3))
        = (-(3 * x ^ 2 / (4 * D * t ^ 3)))
            + (-(1 / (D * t)) * (v - 3 * x / (2 * t)) ^ 2) from by ring]
    rw [Real.exp_add]
    ring
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul]
  have hshift : (∫ v : ℝ, Real.exp (-(1 / (D * t)) * (v - 3 * x / (2 * t)) ^ 2))
      = ∫ v : ℝ, Real.exp (-(1 / (D * t)) * v ^ 2) :=
    MeasureTheory.integral_sub_right_eq_self (μ := MeasureTheory.volume)
      (fun y => Real.exp (-(1 / (D * t)) * y ^ 2)) (3 * x / (2 * t))
  rw [hshift, integral_gaussian]
  rw [show Real.pi / (1 / (D * t)) = Real.pi * (D * t) from by field_simp]
  ring

/-- **The kernel is integrable on the joint phase-space measure.**  The velocity slice at
each position is a shifted Gaussian, and the position marginal of the norm is a Gaussian;
`integrable_prod_iff` assembles them. -/
theorem kernel_integrable (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    MeasureTheory.Integrable (kineticKolmogorovKernel D t)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (kineticKolmogorovKernel D t)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (kineticKolmogorovKernel_contDiff D t).continuous.aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · refine MeasureTheory.ae_of_all _ fun x => ?_
    have hbpos : 0 < 1 / (D * t) := by positivity
    have hbase := integrable_exp_neg_mul_sq hbpos
    have hshifted := hbase.comp_sub_right (3 * x / (2 * t))
    have hconst := (hshifted.const_mul
      (kineticKolmogorovPrefactor D t * Real.exp (-(3 * x ^ 2 / (4 * D * t ^ 3)))))
    refine hconst.congr (MeasureTheory.ae_of_all _ fun v => ?_)
    dsimp only
    rw [kineticKolmogorovKernel_factor,
      exponent_velocity_midpoint_form D t x v hD.ne' ht.ne']
    rw [show -((v - 3 * x / (2 * t)) ^ 2 / (D * t) + 3 * x ^ 2 / (4 * D * t ^ 3))
        = (-(3 * x ^ 2 / (4 * D * t ^ 3)))
            + (-(1 / (D * t)) * (v - 3 * x / (2 * t)) ^ 2) from by ring]
    rw [Real.exp_add]
    ring
  · have hbpos : 0 < 3 / (4 * D * t ^ 3) := by positivity
    have hbase := integrable_exp_neg_mul_sq hbpos
    have hconst := hbase.const_mul
      (kineticKolmogorovPrefactor D t * Real.sqrt (Real.pi * (D * t)))
    refine hconst.congr (MeasureTheory.ae_of_all _ fun x => ?_)
    dsimp only
    have hnn : ∀ v : ℝ, ‖kineticKolmogorovKernel D t (x, v)‖
        = kineticKolmogorovKernel D t (x, v) := fun v =>
      Real.norm_of_nonneg (kineticKolmogorovKernel_pos D t hD ht (x, v)).le
    simp only [hnn]
    rw [kernel_integral_v D t x hD ht]
    try rw [show -(3 * x ^ 2 / (4 * D * t ^ 3))
        = -(3 / (4 * D * t ^ 3)) * x ^ 2 from by ring]
    try ring

/-- **Conservation in the joint measure — the Fubini form, no longer fenced**: the kernel
has unit mass over phase space `ℝ × ℝ` with its product volume. -/
theorem kernel_conservation (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    (∫ z : ℝ × ℝ, kineticKolmogorovKernel D t z) = 1 := by
  rw [show (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.volume.prod MeasureTheory.volume from
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.integral_prod _ (kernel_integrable D t hD ht)]
  have hrw : ∀ x : ℝ, (∫ v : ℝ, kineticKolmogorovKernel D t (x, v))
      = (kineticKolmogorovPrefactor D t * Real.sqrt (Real.pi * (D * t)))
          * Real.exp (-(3 / (4 * D * t ^ 3)) * x ^ 2) := by
    intro x
    rw [kernel_integral_v D t x hD ht]
    rw [show -(3 * x ^ 2 / (4 * D * t ^ 3)) = -(3 / (4 * D * t ^ 3)) * x ^ 2 from by ring]
    try ring
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul, integral_gaussian]
  rw [show Real.pi / (3 / (4 * D * t ^ 3)) = Real.pi * (4 * D * t ^ 3) / 3 from by
    field_simp]
  unfold kineticKolmogorovPrefactor
  rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
  have hAB : Real.pi * (D * t) * (Real.pi * (4 * D * t ^ 3) / 3)
      = (2 * Real.pi * D * t ^ 2) ^ 2 / 3 := by ring
  have hsq : Real.sqrt (Real.pi * (D * t) * (Real.pi * (4 * D * t ^ 3) / 3))
      = 2 * Real.pi * D * t ^ 2 / Real.sqrt 3 := by
    rw [hAB, Real.sqrt_div (by positivity : (0:ℝ) ≤ (2 * Real.pi * D * t ^ 2) ^ 2),
      Real.sqrt_sq (by positivity)]
  rw [hsq]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

end FundamentalSolution

section Hypocoercivity

/-!
# φ-entropies and the sharp hypocoercive rate — Dolbeault–Li 2018

Dolbeault and Li, *φ-Entropies: convexity, coercivity and hypocoercivity for Fokker–Planck
and kinetic Fokker–Planck equations*, Math. Models Methods Appl. Sci. **28** (2018) 2637.
This is the paper for the hypocoercivity slot that the deep-search fence in
the `FundamentalSolution` section reported empty; this module now carries its baseline.

* **§A — the φ-entropy family.**  `φ_p(w) = (w^p − 1 − p(w−1))/(p−1)` interpolates between
  the `L²` entropy `φ₂(w) = (w−1)²` (proved as an identity) and the Gibbs entropy
  `φ₁(w) = w·log w − (w−1)`, and the interpolation is *exact* at the endpoint:
  `phiP_tendsto_gibbs` shows the `p → 1` limit of the family is the Gibbs entropy, because
  `φ_p` at fixed `w` is the difference quotient of `p ↦ w^p − 1 − p(w−1)` at `p = 1`, so
  the limit is literally a derivative.
* **§B — the kinetic stationary state.**  On the harmonic phase space the transport field
  `v∂ₓ − x∂ᵥ` annihilates the stationary Gaussian: `transport_annihilates_stationary` is
  the paper's `T f⋆ = 0`, the algebraic reason the Gaussian is invariant although transport
  is anti-self-adjoint and diffusion acts only in `v`.
* **§C — the twisted Fisher form and the sharp rate.**  The paper's functional (1.10)
  interpolates `𝒥_λ = (1−λ)(|∇ₓh|² + |∇ᵥh|²) + λ|∇ₓh + ∇ᵥh|²`.  At the level of the
  gradient pair `(a,b) = (∇ₓh, ∇ᵥh)`, whose drift under the harmonic kinetic Fokker–Planck
  flow is `(a,b)' = (b, −a−b)` (the commutators `[∂ₓ, T] = −∂ᵥ`, `[∂ᵥ, T] = ∂ₓ`,
  `[∂ᵥ, L] = −∂ᵥ` folded into a matrix), three exact statements hold:

  - `twistedFisherForm_coercive`: `(1−λ)|z|² ≤ 𝒥_λ(z) ≤ (1+λ)|z|²` — the form is a norm
    for `λ < 1`, with matrix `[[1,λ],[λ,1]]` and eigenvalues `1 ± λ`;
  - `plain_energy_stalls`: the *untwisted* energy dissipates only through `−2b²`, which
    vanishes on the whole line `b = 0` away from equilibrium — coercivity fails, and this
    single line is the hypocoercivity phenomenon;
  - `twisted_lyapunov_exact`: at `λ = ½` — the value `λ(∞) = ½` of the paper's
    Theorem 1.1 — the derivative of `𝒥_{1/2}` along the drift is **exactly** `−𝒥_{1/2}`.
    Not an inequality: an identity (`MᵀP + PM = −P` for `M = [[0,1],[−1,−1]]`,
    `P = [[1,½],[½,1]]`).  Consequently (`twisted_form_decay`)
    `𝒥_{1/2}(z(t)) = e^{−t}·𝒥_{1/2}(z(0))` for every solution of the gradient drift, and
    (`hypocoercive_energy_decay`) `|z(t)|² ≤ 3e^{−t}|z(0)|²` — the sharp rate `e^{−t}` of
    the paper's Proposition 1.1, with the explicit prefactor `3` an instance of the
    prefactor loss the paper discusses (`𝒞 > 1`, never `1`, because the plain energy is
    not a Lyapunov function).

**Honest layering, with its search.**  Formalized: the φ-family calculus and its Gibbs
endpoint, the stationary-state identity, and the finite-dimensional gradient-pair shadow of
the hypocoercivity mechanism, in which the paper's sharp rate is an exact `2×2` Lyapunov
identity.  Not formalized: the functional level — `𝒥_λ` as an integral over the invariant
measure, Proposition 1.1 for actual solutions of the kinetic equation (1.6), the
`t`-dependent `λ(t)` and `ρ(t)` of Theorem 1.1, and the entropy–entropy-production
inequalities of the paper's §2.  The hypocoercivity vocabulary was searched (grep,
filenames, ZIL query) before this module existed and had zero hits; this module is now the
hit, and the fence in the `FundamentalSolution` section points here.
-/

open Real

/-! ### §A — the φ-entropy family and its Gibbs endpoint -/

/-- **The φ-entropy generator** `φ_p(w) = (w^p − 1 − p(w−1))/(p−1)` — Dolbeault–Li's
interpolating family, `p ∈ (1,2]`. -/
noncomputable def phiP (p w : ℝ) : ℝ := (w ^ p - 1 - p * (w - 1)) / (p - 1)

/-- **The Gibbs entropy generator** `φ₁(w) = w·log w − (w−1)` — the `p → 1` endpoint. -/
noncomputable def gibbsPhi (w : ℝ) : ℝ := w * Real.log w - (w - 1)

/-- The family vanishes at equilibrium: `φ_p(1) = 0`. -/
theorem phiP_one (p : ℝ) : phiP p 1 = 0 := by
  unfold phiP
  rw [Real.one_rpow]
  ring

/-- **The `p = 2` member is the `L²` entropy**: `φ₂(w) = (w−1)²`. -/
theorem phiP_two (w : ℝ) : phiP 2 w = (w - 1) ^ 2 := by
  unfold phiP
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  push_cast
  ring

/-- The numerator of `φ_p` as a function of `p` is differentiable at `p = 1` with
derivative the Gibbs entropy. -/
theorem phiP_numerator_hasDerivAt (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun p : ℝ => w ^ p - 1 - p * (w - 1)) (gibbsPhi w) 1 := by
  have hlin : HasDerivAt (fun p : ℝ => Real.log w * p) (Real.log w) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_mul (Real.log w)
  have hexp := hlin.exp
  have hlin2 : HasDerivAt (fun p : ℝ => p * (w - 1)) (w - 1) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (w - 1)
  have h := (hexp.sub_const 1).sub hlin2
  have hrw : (fun p : ℝ => w ^ p - 1 - p * (w - 1))
      = fun p : ℝ => Real.exp (Real.log w * p) - 1 - p * (w - 1) := by
    funext p
    rw [Real.rpow_def_of_pos hw]
  rw [hrw]
  refine h.congr_deriv ?_
  rw [mul_one, Real.exp_log hw]
  unfold gibbsPhi
  ring

/-- **The Gibbs entropy is the `p → 1` limit of the φ-family** — and the limit is exact
because `φ_p(w)` is the difference quotient of the numerator at `p = 1`: the interpolation
claim of the paper's introduction is literally a derivative. -/
theorem phiP_tendsto_gibbs (w : ℝ) (hw : 0 < w) :
    Filter.Tendsto (fun p => phiP p w) (nhdsWithin 1 {(1 : ℝ)}ᶜ)
      (nhds (gibbsPhi w)) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (phiP_numerator_hasDerivAt w hw)
  refine h.congr' ?_
  filter_upwards with p
  rw [slope_def_field]
  unfold phiP
  rw [Real.rpow_one]
  ring

/-! ### §B — the stationary Gaussian is transport-invariant -/

/-- The stationary phase-space Gaussian `f⋆(x,v) = (2π)⁻¹·e^{−(x²+v²)/2}` (one dimension
of position and one of velocity). -/
noncomputable def stationaryGaussian (x v : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.exp (-((x ^ 2 + v ^ 2) / 2))

/-- The position partial of the stationary Gaussian is `−x·f⋆`. -/
theorem stationaryGaussian_hasDerivAt_x (x v : ℝ) :
    HasDerivAt (fun y => stationaryGaussian y v) (-x * stationaryGaussian x v) x := by
  unfold stationaryGaussian
  have hinner : HasDerivAt (fun y : ℝ => -((y ^ 2 + v ^ 2) / 2)) (-x) x := by
    have h := (((hasDerivAt_pow 2 x).add_const (v ^ 2)).div_const 2).neg
    refine h.congr_deriv ?_
    push_cast
    ring
  have h := (hinner.exp).const_mul (2 * Real.pi)⁻¹
  refine h.congr_deriv ?_
  ring

/-- The velocity partial of the stationary Gaussian is `−v·f⋆`. -/
theorem stationaryGaussian_hasDerivAt_v (x v : ℝ) :
    HasDerivAt (fun u => stationaryGaussian x u) (-v * stationaryGaussian x v) v := by
  unfold stationaryGaussian
  have hinner : HasDerivAt (fun u : ℝ => -((x ^ 2 + u ^ 2) / 2)) (-v) v := by
    have h := (((hasDerivAt_pow 2 v).const_add (x ^ 2)).div_const 2).neg
    refine h.congr_deriv ?_
    push_cast
    ring
  have h := (hinner.exp).const_mul (2 * Real.pi)⁻¹
  refine h.congr_deriv ?_
  ring

/-- **Transport annihilates the stationary state**: `v·∂ₓf⋆ − x·∂ᵥf⋆ = 0` — the paper's
`T f⋆ = 0`, with the partials supplied by the two lemmas above.  The harmonic transport
field is the phase-space rotation generator and the radial Gaussian is rotation-invariant;
this is why the kinetic equation keeps the product Gaussian as equilibrium even though
diffusion acts only in velocity. -/
theorem transport_annihilates_stationary (x v : ℝ) :
    v * (-x * stationaryGaussian x v) - x * (-v * stationaryGaussian x v) = 0 := by
  ring

/-! ### §C — the twisted Fisher form and the sharp hypocoercive rate -/

/-- **The twisted Fisher quadratic form** of the paper's (1.10), at the level of the
gradient pair `(a,b) = (∇ₓh, ∇ᵥh)`:
`𝒥_λ(a,b) = (1−λ)(a² + b²) + λ(a+b)²`. -/
def twistedFisherForm (lam a b : ℝ) : ℝ :=
  (1 - lam) * (a ^ 2 + b ^ 2) + lam * (a + b) ^ 2

/-- **Coercivity of the twisted form**: `(1−λ)|z|² ≤ 𝒥_λ(z) ≤ (1+λ)|z|²` — the quadratic
form has matrix `[[1,λ],[λ,1]]` with eigenvalues `1 ± λ`, so for `λ < 1` twisting keeps a
norm. -/
theorem twistedFisherForm_coercive (lam a b : ℝ) (h0 : 0 ≤ lam) :
    (1 - lam) * (a ^ 2 + b ^ 2) ≤ twistedFisherForm lam a b
      ∧ twistedFisherForm lam a b ≤ (1 + lam) * (a ^ 2 + b ^ 2) := by
  unfold twistedFisherForm
  constructor
  · nlinarith [sq_nonneg (a + b)]
  · nlinarith [sq_nonneg (a - b)]

/-- **The untwisted energy stalls**: along the gradient drift `(a,b)' = (b, −a−b)` the
plain energy `a² + b²` dissipates at rate `−2b²` — which vanishes on the entire line
`b = 0` however large `a` is.  No inequality `d/dt(a²+b²) ≤ −c·(a²+b²)` can hold: this
identity is the failure of coercivity that the twist repairs, i.e. the hypocoercivity
phenomenon. -/
theorem plain_energy_stalls (a b : ℝ) :
    2 * a * b + 2 * b * (-a - b) = -(2 * b ^ 2) := by
  ring

/-- **The exact Lyapunov identity at `λ = ½`** — the sharp-rate engine.  Along the
gradient drift `(a,b)' = (b, −a−b)` of the harmonic kinetic Fokker–Planck flow, the
derivative of the half-twisted form is *exactly* its negative:

  `d𝒥_{1/2} = −𝒥_{1/2}`.

Not an estimate — an identity of quadratic forms (`MᵀP + PM = −P` for the drift matrix
`M = [[0,1],[−1,−1]]` and `P = [[1,½],[½,1]]`).  The value `λ = ½` is the asymptotic
`λ(∞) = ½` of the paper's Theorem 1.1, and the resulting rate `e^{−t}` is the sharp rate
of its Proposition 1.1. -/
theorem twisted_lyapunov_exact (a b : ℝ) :
    (1 - (1 / 2 : ℝ)) * (2 * a * b + 2 * b * (-a - b))
        + (1 / 2 : ℝ) * (2 * (a + b) * (b + (-a - b)))
      = -twistedFisherForm (1 / 2) a b := by
  unfold twistedFisherForm
  ring

/-- **Sharp decay of the twisted form**: for any solution of the gradient drift, the
half-twisted Fisher form decays *exactly* like `e^{−t}` — the closed-form consequence of
the Lyapunov identity, and the paper's sharp rate. -/
theorem twisted_form_decay (a b : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt a (b t) t)
    (hb : ∀ t, HasDerivAt b (-a t - b t) t) (t : ℝ) :
    twistedFisherForm (1 / 2) (a t) (b t)
      = Real.exp (-t) * twistedFisherForm (1 / 2) (a 0) (b 0) := by
  have hQd : ∀ s, HasDerivAt (fun u => twistedFisherForm (1 / 2) (a u) (b u))
      (-twistedFisherForm (1 / 2) (a s) (b s)) s := by
    intro s
    have h1 : HasDerivAt (fun u => (a u) ^ 2 + (b u) ^ 2)
        (2 * a s * b s + 2 * b s * (-a s - b s)) s := by
      have h := ((ha s).pow 2).add ((hb s).pow 2)
      refine h.congr_deriv ?_
      push_cast
      ring
    have h2 : HasDerivAt (fun u => (a u + b u) ^ 2)
        (2 * (a s + b s) * (b s + (-a s - b s))) s := by
      have h := ((ha s).add (hb s)).pow 2
      refine h.congr_deriv ?_
      simp only [Pi.add_apply]
      push_cast
      ring
    have h := (h1.const_mul (1 - (1 / 2 : ℝ))).add (h2.const_mul (1 / 2 : ℝ))
    refine h.congr_deriv ?_
    rw [← twisted_lyapunov_exact (a s) (b s)]
  have hd : ∀ u, HasDerivAt
      (fun r => Real.exp r * twistedFisherForm (1 / 2) (a r) (b r)) 0 u := by
    intro u
    have h := (Real.hasDerivAt_exp u).mul (hQd u)
    refine h.congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero
    (f := fun s => Real.exp s * twistedFisherForm (1 / 2) (a s) (b s))
    (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  simp only [Real.exp_zero, one_mul] at hconst
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  rw [Real.exp_neg, ← hconst, inv_mul_cancel_left₀ hexp]

/-- **Hypocoercive decay of the energy, with its prefactor**:
`|z(t)|² ≤ 3e^{−t}|z(0)|²`.  The rate is the sharp `e^{−t}`; the prefactor
`3 = (1+½)/(1−½)` is the price of passing through the twisted norm, an instance of the
paper's observation that the constant `𝒞` cannot be `1` — the plain energy is not a
Lyapunov function (`plain_energy_stalls`), so decay must be routed through the twist. -/
theorem hypocoercive_energy_decay (a b : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt a (b t) t)
    (hb : ∀ t, HasDerivAt b (-a t - b t) t) (t : ℝ) :
    (a t) ^ 2 + (b t) ^ 2
      ≤ 3 * Real.exp (-t) * ((a 0) ^ 2 + (b 0) ^ 2) := by
  have hlow := (twistedFisherForm_coercive (1 / 2) (a t) (b t) (by norm_num)).1
  have hup := (twistedFisherForm_coercive (1 / 2) (a 0) (b 0) (by norm_num)).2
  have hexp : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hmul : Real.exp (-t) * twistedFisherForm (1 / 2) (a 0) (b 0)
      ≤ Real.exp (-t) * ((1 + 1 / 2) * ((a 0) ^ 2 + (b 0) ^ 2)) :=
    mul_le_mul_of_nonneg_left hup hexp.le
  have hchain := hlow.trans ((twisted_form_decay a b ha hb t).le.trans hmul)
  nlinarith [hchain]

end Hypocoercivity

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.covariance_lyapunov where
  formalizes @ "claim:the-kinetic-covariance-matrix-solves-the-lyapunov-equation-of-free-transport-drift-with-velocity-only-noise-so-rank-one-noise-cascades-to-full-rank-through-the-hormander-bracket",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:auscher-imbert-niebel-2024-fundamental-solutions-to-kolmogorov-fokker-planck-equations-with-rough-coefficients-arxiv-2403-17468",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticDiffusionTransportBracket_eq"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.exponent_midpoint_form where
  formalizes @ "claim:the-kinetic-kernels-exponent-is-exactly-the-midpoint-transport-corrected-position-gaussian-plus-an-ordinary-velocity-gaussian-the-one-endpoint-form-of-the-papers-gaussian-bound-shape",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.kernel_kinetic_scaling where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.exponent_kinetic_scaling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorovKernel_factor",
  formalizes @ "claim:the-kinetic-kernel-is-homogeneous-of-weight-minus-four-under-the-kinetic-scaling-with-invariant-exponent-the-scaling-that-organizes-the-papers-equation-class",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.kernel_conservation_iterated where
  derives @ "claim:the-kinetic-kolmogorov-kernel-has-unit-mass-certifying-its-normalization-conservation-is-the-input-to-the-papers-davies-decay",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticKolmogorovKernel_pos",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.kernel_conservation",
  caveat @ "claim:the-papers-rough-coefficient-operator-theory-davies-l2-decay-and-moser-equivalence-are-not-formalized-searched-grep-filenames-and-zil-query-under-davies-twist-moser-caccioppoli-vocabularies-with-no-hits-the-hypocoercivity-slot-is-now-carried-by-phientropyhypocoercivity-the-repositorys-davies-references-are-davies-fulling-unruh-and-its-c0-semigroup-infrastructure-dampedheatsemigroup-is-the-weld-target-for-a-future-operator-formalization"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.phiP_tendsto_gibbs where
  formalizes @ "claim:the-gibbs-entropy-is-the-p-to-one-limit-of-the-phi-entropy-family-exactly-because-phi-p-is-the-difference-quotient-of-its-numerator-at-p-equals-one",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:dolbeault-li-2018-phi-entropies-convexity-coercivity-and-hypocoercivity-for-fokker-planck-and-kinetic-fokker-planck-equations-m3as-28-2637"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.plain_energy_stalls where
  formalizes @ "claim:the-untwisted-gradient-energy-dissipates-only-through-the-velocity-component-and-stalls-on-the-whole-zero-velocity-gradient-line-the-hypocoercivity-phenomenon-in-one-identity",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.twisted_lyapunov_exact where
  derives @ "claim:at-lambda-one-half-the-twisted-fisher-form-satisfies-an-exact-lyapunov-identity-along-the-kinetic-gradient-drift-so-the-papers-sharp-e-to-minus-t-rate-is-an-identity-not-an-estimate",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:dolbeault-li-2018-phi-entropies-convexity-coercivity-and-hypocoercivity-for-fokker-planck-and-kinetic-fokker-planck-equations-m3as-28-2637",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck.kineticDiffusionTransportBracket_eq"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck.hypocoercive_energy_decay where
  derives @ "claim:the-gradient-energy-decays-at-the-sharp-rate-e-to-minus-t-with-explicit-prefactor-three-routed-through-the-twisted-norm-because-the-plain-energy-is-not-a-lyapunov-function",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-finite-dimensional-gradient-pair-shadow-the-functional-level-with-integrals-over-the-invariant-measure-proposition-one-point-one-for-pde-solutions-and-the-t-dependent-lambda-of-theorem-one-point-one-are-not-formalized"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KineticFokkerPlanck

end

end
