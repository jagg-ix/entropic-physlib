/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.VerlindeCovariantGravity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul

meta import Zil

/- Consolidated from Physlib/Thermodynamics/RelativisticScreenKinematics.lean -/

/-!
# Relativistic screen kinematics: temperature, four-velocity, and proper acceleration

The covariant Verlinde screen (`VerlindeCovariantGravity`) supplies, for a static Schwarzschild
exterior (mass parameter `μ = GM`, areal radius `r`, metric function `f = 1 − 2μ/r`), the redshift
potential `φ = ½ log f`, the redshift factor `e^φ = √f`, and the redshifted normal gradient
`e^φ·(n·∇φ) = μ/r²`.  This module adds the three relativistic-screen kinematic quantities of gu.md
Axiom 16 that were missing:

* `redshiftScreenTemperature_eq` — the **relativistic screen temperature** `T = (ℏ/2π)·e^φ·(n·∇φ)`,
  equal to `(ℏ/2π)·μ/r²`.
* `stationaryFourVelocity_unit_timelike` — the **stationary four-velocity** `u^a = e^{−φ}ξ^a` is a
  unit timelike vector: `e^{−2φ}·ξ² = −1` (its normalization, `ξ² = −f`).
* `properAcceleration_eq` — the **proper acceleration** `a = √f·∂_r φ` (the normal component of
  `a^b = −∇^b φ`) equals `μ/(r²√f)`, the standard static-observer acceleration.
* `redshiftScreenTemperature_eq_redshifted_unruh` — the Tolman–Unruh law: the screen temperature is
  the redshift factor times the local Unruh temperature, `T = e^φ·(ℏ/2π)·a`.

Reuses `killingRedshiftPotential`, `redshiftFactor`, `redshiftedNormalGradient`,
`timelikeKillingNormSq` (`VerlindeCovariantGravity`) and `schwF` (`SchwarzschildRicci`); scope is the
same exact static Schwarzschild exterior (`0 < f`), scalar-valued.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.RelativisticScreenKinematics

open Physlib.Thermodynamics.VerlindeCovariantGravity
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci

/-- **The relativistic screen temperature** `T = (ℏ/2π)·e^φ·(n·∇φ)` — the local Unruh–Tolman
temperature of the static Schwarzschild screen. -/
def redshiftScreenTemperature (ℏ μ r : ℝ) : ℝ :=
  ℏ / (2 * Real.pi) * redshiftedNormalGradient μ r

/-- **The relativistic screen temperature equals `(ℏ/2π)·μ/r²`** (gu.md Axiom 16), using the
redshifted normal gradient `e^φ·(n·∇φ) = μ/r²`. -/
@[zil_level physical_theorem]
theorem redshiftScreenTemperature_eq (ℏ μ r : ℝ) (hr : r ≠ 0) (hf : 0 < schwF μ r) :
    redshiftScreenTemperature ℏ μ r = ℏ / (2 * Real.pi) * (μ / r ^ 2) := by
  rw [redshiftScreenTemperature, redshiftedNormalGradient_eq μ r hr hf]

/-- **The stationary four-velocity `u^a = e^{−φ}ξ^a` is a unit timelike vector.**  Its squared norm
`e^{−2φ}·ξ² = (1/f)·(−f) = −1`, i.e. the redshift-rescaled timelike Killing vector is normalized to
`−1` (the `−+++`/timelike convention). -/
@[zil_level physical_theorem]
theorem stationaryFourVelocity_unit_timelike (μ r : ℝ) (hf : 0 < schwF μ r) :
    (redshiftFactor μ r)⁻¹ ^ 2 * timelikeKillingNormSq μ r = -1 := by
  have hne : schwF μ r ≠ 0 := hf.ne'
  rw [timelikeKillingNormSq, redshiftFactor_eq_sqrt μ r hf, inv_pow, Real.sq_sqrt hf.le]
  field_simp

/-- **The proper acceleration** `a = √f·∂_r φ` — the outward normal component of `a^b = −∇^b φ` for a
static observer. -/
def properAcceleration (μ r : ℝ) : ℝ :=
  Real.sqrt (schwF μ r) * deriv (killingRedshiftPotential μ) r

/-- **The proper acceleration equals `μ/(r²√f)`** (gu.md Axiom 16), the standard static
Schwarzschild-observer acceleration, via `∂_r φ = μ/(r²f)`. -/
@[zil_level physical_theorem]
theorem properAcceleration_eq (μ r : ℝ) (hr : r ≠ 0) (hf : 0 < schwF μ r) :
    properAcceleration μ r = μ / (r ^ 2 * Real.sqrt (schwF μ r)) := by
  have hne : schwF μ r ≠ 0 := hf.ne'
  have hs : Real.sqrt (schwF μ r) ≠ 0 := Real.sqrt_ne_zero'.mpr hf
  rw [properAcceleration, (killingRedshiftPotential_hasDerivAt μ r hr hne).deriv]
  rw [eq_div_iff (by positivity)]
  field_simp
  rw [Real.sq_sqrt hf.le]
  ring

/-- **The Tolman–Unruh law.**  The relativistic screen temperature is the redshift factor `e^φ` times
the local Unruh temperature `(ℏ/2π)·a` built from the proper acceleration: `T = e^φ·(ℏ/2π)·a`.  The
screen (Tolman) temperature is the redshifted local Unruh temperature. -/
@[zil_level bridge_theorem]
theorem redshiftScreenTemperature_eq_redshifted_unruh (ℏ μ r : ℝ) :
    redshiftScreenTemperature ℏ μ r
      = redshiftFactor μ r * (ℏ / (2 * Real.pi) * properAcceleration μ r) := by
  rw [redshiftScreenTemperature, properAcceleration, redshiftedNormalGradient]
  ring

end Physlib.Thermodynamics.RelativisticScreenKinematics

/- ZIL-BEGIN -/

open Zil
open Physlib.Thermodynamics.RelativisticScreenKinematics

zil attach redshiftScreenTemperature_eq where
  supported_by @ "lean:ProbDistribution.normalized",
  formalizes @ "claim:the-relativistic-screen-temperature-equals-h-bar-over-two-pi-times-the-redshift-factor-times-the-normal-gradient-of-the-redshift-potential-equal-to-h-bar-over-two-pi-times-mu-over-r-squared-for-the-static-schwarzschild-screen"

zil attach stationaryFourVelocity_unit_timelike where
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.redshiftFactor_eq_sqrt",
  formalizes @ "claim:the-stationary-four-velocity-e-to-minus-phi-times-the-timelike-killing-vector-is-a-unit-timelike-vector-its-squared-norm-e-to-minus-two-phi-times-killing-norm-squared-equals-minus-one"

zil attach properAcceleration_eq where
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.killingRedshiftPotential_hasDerivAt",
  formalizes @ "claim:the-proper-acceleration-square-root-f-times-the-radial-derivative-of-the-redshift-potential-the-normal-component-of-minus-gradient-phi-equals-mu-over-r-squared-square-root-f-the-static-schwarzschild-observer-acceleration"

zil attach redshiftScreenTemperature_eq_redshifted_unruh where
  formalizes @ "claim:the-tolman-unruh-law-the-relativistic-screen-temperature-is-the-redshift-factor-times-the-local-unruh-temperature-h-bar-over-two-pi-times-the-proper-acceleration"

zil_file_contract physlib.relativisticScreenKinematics where
  promises "The relativistic screen kinematics of the covariant Verlinde screen for the static Schwarzschild exterior, completing gu.md Axiom 16. The relativistic screen temperature equals h bar over two pi times the redshift factor times the normal gradient of the redshift potential, equal to h bar over two pi times mu over r squared. The stationary four-velocity, the redshift factor to the minus one times the timelike Killing vector, is a unit timelike vector: its squared norm e to the minus two phi times the Killing norm squared equals minus one. The proper acceleration, square root f times the radial derivative of the redshift potential, the normal component of minus gradient phi, equals mu over r squared square root f, the standard static Schwarzschild-observer acceleration. And the Tolman-Unruh law: the screen temperature is the redshift factor times the local Unruh temperature built from that proper acceleration, so the screen Tolman temperature is the redshifted local Unruh temperature. Scope is the exact static Schwarzschild exterior with positive metric function, scalar-valued, reusing the redshift potential, redshift factor, redshifted normal gradient, and timelike Killing norm squared of the covariant Verlinde screen."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.redshiftedNormalGradient",
    "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.redshiftFactor",
    "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.killingRedshiftPotential",
    "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.timelikeKillingNormSq"
  ]
  forbids_substitutes [
    "reading the scalar static-Schwarzschild screen kinematics as a general covariant tensor formulation with an explicit four-velocity vector field and Killing vector"
  ]
  witnessed_by [
    redshiftScreenTemperature_eq,
    stationaryFourVelocity_unit_timelike,
    properAcceleration_eq,
    redshiftScreenTemperature_eq_redshifted_unruh
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.relativisticScreenKinematics

/- Consolidated from Physlib/Thermodynamics/AbstractKillingRedshiftKinematics.lean -/

/-!
# Redshift kinematics for an abstract timelike Killing field

Statement 16 of the relational framework defines, from a timelike Killing vector `ξ`, the
redshift potential `φ = ½log(−ξ²)`, the stationary four-velocity `u = e^{−φ}ξ`, and the
acceleration `a = ∇φ`.  The repository carried all three on the **exact Schwarzschild**
profile only (`VerlindeCovariantGravity.killingRedshiftPotential` is `½log(schwF)`, and
`RelativisticScreenKinematics` works through `schwF` throughout).  This module lifts the
kinematics off that ansatz:

* **§A, matrix level** — for *any* metric `g` and *any* vector `ξ` with `ξᵀgξ < 0`, the
  normalized vector `e^{−φ}ξ` has `g`-norm exactly `−1` (`stationary_unit_of_timelike`).
  This is pure quadratic-form algebra plus `exp(log)` — no metric ansatz, no dimension
  restriction, no coordinates.
* **§B, along a foliation** — for an *arbitrary differentiable* Killing-norm profile
  `q(r) = ξ²(r) < 0` (not the Schwarzschild one), the redshift potential
  `φ = ½log(−q)` is differentiable with `φ' = q'/(2q)` (`abstractRedshiftPotential_hasDerivAt`)
  — the acceleration-as-gradient face `a_r = ∂_r φ` of statement 16, for every static
  spherically-foliated profile at once.
* **§C, the weld** — at `q = −schwF` the abstract potential *is* the repository's
  `killingRedshiftPotential`, definitionally.  The Schwarzschild chain is the special case,
  as it should be.

**Honest layering.**  The remaining distance to full statement-16 generality is the tensor
covariant derivative: `a^b = −∇^bφ` as a four-vector equation needs the covariant-derivative
layer on manifold carriers, and `§B` states its foliation component.  The screen-temperature
face `T = (ℏ/2π)e^φ n·∇φ` composes from `§B` with the existing
`RelativisticScreenKinematics.redshiftScreenTemperature_eq` once that transport exists.
-/

@[expose] public section

namespace Physlib.Thermodynamics.AbstractKillingRedshiftKinematics

open Real Matrix

variable {ι : Type*} [Fintype ι]

/-! ### §A — the unit stationary observer, at matrix level -/

/-- The `g`-quadratic form `ξᵀ g ξ` of a vector — the Killing norm squared when `ξ` is the
Killing field. -/
def killingQuadForm (g : Matrix ι ι ℝ) (ξ : ι → ℝ) : ℝ := ξ ⬝ᵥ (g *ᵥ ξ)

/-- The redshift potential of an abstract Killing vector at a point:
`φ = ½ log(−ξᵀgξ)`. -/
noncomputable def redshiftPotentialOf (g : Matrix ι ι ℝ) (ξ : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (-killingQuadForm g ξ)

/-- The quadratic form scales quadratically. -/
theorem killingQuadForm_smul (g : Matrix ι ι ℝ) (ξ : ι → ℝ) (c : ℝ) :
    killingQuadForm g (c • ξ) = c ^ 2 * killingQuadForm g ξ := by
  unfold killingQuadForm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul]
  ring

/-- **The stationary observer is unit timelike, for any metric and any timelike vector**:
if `ξᵀgξ < 0` then `u = e^{−φ}ξ` satisfies `uᵀgu = −1`.  Statement 16's `u = e^{−φ}ξ`
without any metric ansatz — the normalization is an identity of the quadratic form and the
logarithm, not a property of Schwarzschild. -/
theorem stationary_unit_of_timelike (g : Matrix ι ι ℝ) (ξ : ι → ℝ)
    (hξ : killingQuadForm g ξ < 0) :
    killingQuadForm g (Real.exp (-redshiftPotentialOf g ξ) • ξ) = -1 := by
  rw [killingQuadForm_smul]
  have hpos : 0 < -killingQuadForm g ξ := by linarith
  have hexp : Real.exp (-redshiftPotentialOf g ξ) ^ 2 = (-killingQuadForm g ξ)⁻¹ := by
    rw [sq, ← Real.exp_add]
    unfold redshiftPotentialOf
    rw [show -(1 / 2 * Real.log (-killingQuadForm g ξ))
          + -(1 / 2 * Real.log (-killingQuadForm g ξ))
        = -Real.log (-killingQuadForm g ξ) from by ring]
    rw [Real.exp_neg, Real.exp_log hpos]
  rw [hexp, inv_mul_eq_div, div_eq_iff (ne_of_gt hpos)]
  ring

/-! ### §B — the potential's gradient along a foliation, for an arbitrary profile -/

/-- The redshift potential of an abstract Killing-norm profile `q(r) = ξ²(r)`:
`φ(r) = ½ log(−q(r))`.  The Schwarzschild case is `q = −schwF`. -/
noncomputable def abstractRedshiftPotential (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (-q r)

/-- **The acceleration is the potential's gradient, for every profile**: wherever the
Killing norm is timelike (`q(r) < 0`) and differentiable, `φ' = q'/(2q)`.  This is
statement 16's `a = ∇φ` in the foliation direction, freed of the Schwarzschild ansatz:
no form of `q` is assumed beyond differentiability at the point. -/
theorem abstractRedshiftPotential_hasDerivAt (q : ℝ → ℝ) {q' r : ℝ}
    (hq : HasDerivAt q q' r) (hneg : q r < 0) :
    HasDerivAt (abstractRedshiftPotential q) (q' / (2 * q r)) r := by
  have hne : -q r ≠ 0 := by linarith
  have hlog : HasDerivAt (fun s => Real.log (-q s)) ((-q r)⁻¹ * -q') r := by
    have hneg' : HasDerivAt (fun s => -q s) (-q') r := hq.neg
    exact (Real.hasDerivAt_log hne).comp r hneg'
  have hqne : q r ≠ 0 := ne_of_lt hneg
  have h := hlog.const_mul (1 / 2 : ℝ)
  refine h.congr_deriv ?_
  field_simp

/-! ### §C — the Schwarzschild chain is the special case -/

/-- **The abstract potential at the Schwarzschild profile is the repository's redshift
potential**, definitionally: `abstractRedshiftPotential (−schwF μ) = killingRedshiftPotential μ`.
The exact-Schwarzschild chain of `VerlindeCovariantGravity` and
`RelativisticScreenKinematics` is the `q = −schwF` instance of §B. -/
theorem abstractRedshiftPotential_schwarzschild (μ r : ℝ) :
    abstractRedshiftPotential (VerlindeCovariantGravity.timelikeKillingNormSq μ) r
      = VerlindeCovariantGravity.killingRedshiftPotential μ r := rfl

/- ZIL-BEGIN -/

zil attach Physlib.Thermodynamics.AbstractKillingRedshiftKinematics.stationary_unit_of_timelike where
  derives @ "claim:the-stationary-four-velocity-e-to-minus-phi-xi-is-unit-timelike-for-any-metric-and-any-timelike-vector-with-no-metric-ansatz",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.RelativisticScreenKinematics.stationaryFourVelocity_unit_timelike"

zil attach Physlib.Thermodynamics.AbstractKillingRedshiftKinematics.abstractRedshiftPotential_hasDerivAt where
  derives @ "claim:the-redshift-potential-gradient-is-the-foliation-acceleration-for-an-arbitrary-differentiable-killing-norm-profile-not-only-schwarzschild",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-four-vector-form-of-acceleration-as-gradient-needs-the-covariant-derivative-layer-this-is-its-foliation-component"

zil attach Physlib.Thermodynamics.AbstractKillingRedshiftKinematics.abstractRedshiftPotential_schwarzschild where
  formalizes @ "claim:the-repositorys-schwarzschild-redshift-chain-is-definitionally-the-special-case-of-the-abstract-killing-potential",
  epistemic_status @ "consistency-identity"

/- ZIL-END -/

end Physlib.Thermodynamics.AbstractKillingRedshiftKinematics

end

