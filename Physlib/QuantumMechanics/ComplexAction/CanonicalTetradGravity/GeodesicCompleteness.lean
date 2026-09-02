/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation
public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
meta import Zil

/-!
# Geodesic completeness from the Levi-Civita spray

This file closes a precise global-geometric continuation target left open by
the continuum ADM development.  On a global finite-dimensional real chart,
the geodesic equation is written as the autonomous first-order spray

`(x, v)' = (v, -Γ(x)(v,v))`.

The repository's all-real-time ODE theorem then proves that every initial
position and velocity determines a geodesic on all of `ℝ`, provided this
full spray is globally Lipschitz.  The conclusion is actual affine-parameter
completeness on the declared global chart, not merely a bound on the ADM
metric--momentum phase norm.

The final theorem specializes `Γ` to the existing metric-built Christoffel
symbols and simultaneously records that they are torsion-free and
metric-compatible.  Thus the all-time curves are geodesics of the
Levi-Civita connection rather than of an unrelated supplied connection.

## Honest scope

Global Lipschitz regularity of the *whole geodesic spray* is a strong,
explicit continuation hypothesis.  In particular, the spray is quadratic in
velocity, so this premise is not inferred from bounded connection
coefficients or from the ADM phase-norm estimate.  The theorem is a reusable
criterion for a spacetime whose metric data discharge that analytic premise;
it is not an unconditional completeness theorem for arbitrary Einstein data
and it is independent of maximal-Cauchy-development existence.

## References

* R. M. Wald, *General Relativity*, §9.1 and Theorem 10.2.2.
* A. E. Fischer and J. E. Marsden, *The Einstein Evolution Equations as a
  First-Order Quasi-Linear Symmetric Hyperbolic System*, Theorem 4.3
  (the geodesic-spray reduction).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators NNReal

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GeodesicCompleteness

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Matrix

variable {ι : Type*} [Fintype ι]

/-- Position and velocity of a geodesic in a global finite real chart. -/
abbrev CoordinateGeodesicPhase (ι : Type*) :=
  FiniteCoordinateSpace ι × FiniteCoordinateSpace ι

/-- The quadratic Christoffel acceleration `Γ(x)(v,v)`. -/
noncomputable def christoffelAcceleration
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (x v : FiniteCoordinateSpace ι) : FiniteCoordinateSpace ι :=
  coordinateConnectionAction (Γ x) v v

/-- The first-order geodesic spray `(x,v) ↦ (v,-Γ(x)(v,v))`. -/
noncomputable def geodesicSpray
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ) :
    CoordinateGeodesicPhase ι → CoordinateGeodesicPhase ι :=
  fun state => (state.2, -christoffelAcceleration Γ state.1 state.2)

/-- A coordinate geodesic together with its velocity, expressed as the two
first-order equations equivalent to `x'' + Γ(x)(x',x') = 0`. -/
def IsCoordinateGeodesic
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (x v : ℝ → FiniteCoordinateSpace ι) : Prop :=
  ∀ t,
    HasDerivAt x (v t) t ∧
      HasDerivAt v (-christoffelAcceleration Γ (x t) (v t)) t

/-- Affine geodesic completeness on a global real chart: every initial
position and velocity has a geodesic defined for every real parameter. -/
def CoordinateGeodesicallyComplete
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ) : Prop :=
  ∀ x₀ v₀, ∃ x v : ℝ → FiniteCoordinateSpace ι,
    x 0 = x₀ ∧ v 0 = v₀ ∧ IsCoordinateGeodesic Γ x v

/-- The global ODE solution for the spray projects to the two coordinate
geodesic equations. -/
@[zil_level physical_theorem]
theorem coordinateGeodesicallyComplete_of_lipschitzSpray
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (K : ℝ≥0) (hSpray : LipschitzWith K (geodesicSpray Γ)) :
    CoordinateGeodesicallyComplete Γ := by
  intro x₀ v₀
  obtain ⟨phase, hphase0, hphase⟩ :=
    exists_global_solution_of_lipschitz
      (geodesicSpray Γ) (x₀, v₀) K hSpray
  refine ⟨fun t => (phase t).1, fun t => (phase t).2, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst hphase0
  · exact congrArg Prod.snd hphase0
  · intro t
    constructor
    · have hfst :=
        (ContinuousLinearMap.fst ℝ
          (FiniteCoordinateSpace ι) (FiniteCoordinateSpace ι)).hasFDerivAt
          |>.comp_hasDerivAt t (hphase t)
      simpa [Function.comp_def, geodesicSpray] using hfst
    · have hsnd :=
        (ContinuousLinearMap.snd ℝ
          (FiniteCoordinateSpace ι) (FiniteCoordinateSpace ι)).hasFDerivAt
          |>.comp_hasDerivAt t (hphase t)
      simpa [Function.comp_def, geodesicSpray] using hsnd

/-- Under the same spray-Lipschitz premise, two all-time geodesics with the
same initial position and velocity coincide. -/
@[zil_level physical_theorem]
theorem coordinateGeodesic_unique
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (K : ℝ≥0) (hSpray : LipschitzWith K (geodesicSpray Γ))
    {x₁ v₁ x₂ v₂ : ℝ → FiniteCoordinateSpace ι}
    (hgeo₁ : IsCoordinateGeodesic Γ x₁ v₁)
    (hgeo₂ : IsCoordinateGeodesic Γ x₂ v₂)
    (hx : x₁ 0 = x₂ 0) (hv : v₁ 0 = v₂ 0) :
    x₁ = x₂ ∧ v₁ = v₂ := by
  have hevol₁ : ∀ t,
      HasDerivAt (fun s => (x₁ s, v₁ s))
        (geodesicSpray Γ (x₁ t, v₁ t)) t := by
    intro t
    simpa [geodesicSpray] using (hgeo₁ t).1.prodMk (hgeo₁ t).2
  have hevol₂ : ∀ t,
      HasDerivAt (fun s => (x₂ s, v₂ s))
        (geodesicSpray Γ (x₂ t, v₂ t)) t := by
    intro t
    simpa [geodesicSpray] using (hgeo₂ t).1.prodMk (hgeo₂ t).2
  have hphase :
      (fun t => (x₁ t, v₁ t)) = (fun t => (x₂ t, v₂ t)) := by
    apply ODE_solution_unique_univ
      (v := fun _ => geodesicSpray Γ) (s := fun _ => Set.univ)
      (K := K) (t₀ := 0)
    · intro _
      exact hSpray.lipschitzOnWith
    · intro t
      exact ⟨hevol₁ t, Set.mem_univ _⟩
    · intro t
      exact ⟨hevol₂ t, Set.mem_univ _⟩
    · exact Prod.ext hx hv
  constructor
  · funext t
    exact congrArg Prod.fst (congrFun hphase t)
  · funext t
    exact congrArg Prod.snd (congrFun hphase t)

/-- The coordinate Christoffel field produced pointwise from a metric inverse
and the first jet of the metric. -/
noncomputable def metricChristoffelField
    (gInv : FiniteCoordinateSpace ι → Matrix ι ι ℝ)
    (dg : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ) :
    FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ :=
  fun x => christoffelFromMetric (gInv x) (dg x)

/-- The metric-built connection is pointwise torsion-free and
metric-compatible, reusing the repository's general-dimensional
metric-to-Christoffel theorem. -/
@[zil_level physical_theorem]
theorem metricChristoffelField_isLeviCivita [DecidableEq ι]
    (g gInv : FiniteCoordinateSpace ι → Matrix ι ι ℝ)
    (dg : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (hg : ∀ x, (g x)ᵀ = g x)
    (hgi : ∀ x, (gInv x)ᵀ = gInv x)
    (hinv : ∀ x, gInv x * g x = 1)
    (hdg : ∀ x κ, (dg x κ)ᵀ = dg x κ) :
    ∀ x,
      IsTorsionFree (metricChristoffelField gInv dg x) ∧
        IsMetricCompatible
          (metricChristoffelField gInv dg x) (dg x) (g x) := by
  intro x
  exact ⟨christoffelFromMetric_isTorsionFree (gInv x) (dg x) (hdg x),
    christoffelFromMetric_isMetricCompatible (dg x)
      (hg x) (hgi x) (hinv x) (hdg x)⟩

/-- **Levi-Civita geodesic-completeness criterion.** If the spray of the
metric-built Christoffel field is globally Lipschitz on the global chart,
then every initial tangent datum has a unique all-real-affine-parameter
Levi-Civita geodesic.  The conjunction records both the all-time existence
and the torsion-free/metric-compatible identification of the connection. -/
@[zil_level physical_theorem]
theorem metricLeviCivita_coordinateGeodesicallyComplete [DecidableEq ι]
    (g gInv : FiniteCoordinateSpace ι → Matrix ι ι ℝ)
    (dg : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (hg : ∀ x, (g x)ᵀ = g x)
    (hgi : ∀ x, (gInv x)ᵀ = gInv x)
    (hinv : ∀ x, gInv x * g x = 1)
    (hdg : ∀ x κ, (dg x κ)ᵀ = dg x κ)
    (K : ℝ≥0)
    (hSpray : LipschitzWith K
      (geodesicSpray (metricChristoffelField gInv dg))) :
    CoordinateGeodesicallyComplete (metricChristoffelField gInv dg) ∧
      ∀ x,
        IsTorsionFree (metricChristoffelField gInv dg x) ∧
          IsMetricCompatible
            (metricChristoffelField gInv dg x) (dg x) (g x) := by
  exact ⟨coordinateGeodesicallyComplete_of_lipschitzSpray
      (metricChristoffelField gInv dg) K hSpray,
    metricChristoffelField_isLeviCivita g gInv dg hg hgi hinv hdg⟩

/- ZIL-BEGIN -/

zil attach coordinateGeodesicallyComplete_of_lipschitzSpray where
  formalizes @ "claim:a-globally-lipschitz-coordinate-geodesic-spray-has-an-affinely-parameterized-geodesic-on-all-real-times-through-every-initial-position-and-velocity",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.exists_global_solution_of_lipschitz",
  supported_by @ "paper:Fischer-Marsden-1972-Theorem-4.3-geodesic-spray-reduction",
  caveat @ "premise:global-lipschitz-control-is-required-for-the-full-position-velocity-spray-and-is-not-inferred-from-the-existing-adm-phase-norm-bound"

zil attach coordinateGeodesic_unique where
  formalizes @ "claim:all-real-time-coordinate-geodesics-of-a-globally-lipschitz-spray-with-the-same-initial-position-and-velocity-are-identical",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ODE_solution_unique_univ",
  caveat @ "scope:uniqueness-is-on-the-declared-global-coordinate-carrier"

zil attach metricChristoffelField_isLeviCivita where
  formalizes @ "claim:the-pointwise-metric-built-christoffel-field-driving-the-geodesic-spray-is-torsion-free-and-metric-compatible",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric_isTorsionFree",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric_isMetricCompatible",
  caveat @ "premise:the-metric-inverse-and-first-jet-symmetry-identities-are-explicit"

zil attach metricLeviCivita_coordinateGeodesicallyComplete where
  formalizes @ "claim:a-global-chart-whose-metric-built-levi-civita-spray-is-globally-lipschitz-is-affinely-geodesically-complete",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GeodesicCompleteness.coordinateGeodesicallyComplete_of_lipschitzSpray",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GeodesicCompleteness.metricChristoffelField_isLeviCivita",
  caveat @ "scope:this-proves-actual-all-affine-time-geodesics-under-a-strong-spray-continuation-premise-not-unconditional-completeness-for-arbitrary-einstein-data-or-maximal-cauchy-development"

zil_file_contract physlib.leviCivitaGeodesicCompleteness where
  promises "The public spine defines the full first-order Levi-Civita geodesic spray on a global finite real chart. Global Lipschitz control of that spray yields an all-real-affine-parameter geodesic through every initial position and velocity, and ODE uniqueness makes it unique. The metric-specialized theorem reuses the existing metric-to-Christoffel construction to prove that the same connection is torsion-free and metric-compatible."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.exists_global_solution_of_lipschitz",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric_isTorsionFree",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric_isMetricCompatible"
  ]
  forbids_substitutes [
    "calling-an-adm-phase-norm-bound-a-geodesic-completeness-theorem",
    "assuming-the-geodesic-equation-as-a-trajectory-level-premise",
    "using-an-unrelated-connection-without-proving-the-metric-built-levi-civita-identification",
    "claiming-maximal-global-hyperbolicity-from-affine-geodesic-continuation"
  ]
  witnessed_by [
    coordinateGeodesicallyComplete_of_lipschitzSpray,
    coordinateGeodesic_unique,
    metricChristoffelField_isLeviCivita,
    metricLeviCivita_coordinateGeodesicallyComplete
  ]

#zil_formalization_lint physlib.leviCivitaGeodesicCompleteness

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GeodesicCompleteness

end
