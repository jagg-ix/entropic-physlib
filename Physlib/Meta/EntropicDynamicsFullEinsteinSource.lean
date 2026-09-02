/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule
public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
public import Physlib.QuantumMechanics.FrozenLimit
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
meta import Zil

/-!
# The complex Einstein source balance, as a conclusion

The thesis theorem `entropicDynamics_derives_physics` takes the complex Einstein source as an explicit
premise, and `EntropicDynamicsThesisConditionals` discharged only its **weak-field `R₀₀`** component.
The historical theorem `fullComplexEinsteinSource_isConclusion` extracts the complete two-index
algebraic source balance from an already-supplied `ElectroGravitationalFieldEquation`; it is a
projection theorem, not a derivation of that structure or of curvature from a metric. The theorem
`fullComplexEinsteinSource_from_stationary_action` closes the supplied-equation gap:
it constructs the Maxwell stress tensor from `F = dA` and derives the coupled field-equation
structure from explicit metric, gauge, and entropic stationarity premises. Its conclusion includes

  `complexStressEnergy T S + complexGravitationalTensor(einsteinTensor Ric scalarR g) Λ κ = 0`

together with the real Einstein equation `G = κT[F]`, the entropic curvature `Λ = κS`, the source-free
and homogeneous Maxwell equations, and the gauge-squared damping split.

The metric-composed theorem `fullComplexEinsteinSource_from_metricBuilt_stationary_action` additionally
constructs the exact Ricci and scalar inputs from one coordinate metric field. The remaining action gap
is explicit: the post-IBP first variation is not yet derived from one unified continuum
Einstein--Hilbert--Maxwell functional through `HasVarGradientAt`.

The historical thesis capstone `entropicDynamics_derives_physics_variational` takes no Einstein,
Maxwell, entropic-split, or electrogravitic-structure premise. It remains honestly conditional on the
post-integration-by-parts action first variations and their stationarity, and its historical signature
still accepts `Ric` and `scalarR`. Its successor
`entropicDynamics_derives_physics_metricBuilt_variational` replaces those inputs by the metric-built
curvature chain and replaces the three stationarity predicates by one direct-sum first-variation
premise, while continuing to expose the missing underlying-action theorem.

The final theorem folds that result and the previously discharged conditionals back into the public
entropic-dynamics thesis. It retains the thesis's explicit Born-weight
symmetry/refinement/continuity premises, but no longer uses its circular holographic-bit inversion or an
independently assumed complex Einstein source as the gravity conclusions.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexLeviCivitaGravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule
open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics
open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
open Physlib.QuantumMechanics.FrozenLimit
open Physlib.QuantumMechanics.ComplexAction.ComptonClock
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.Thermodynamics
open Filter Topology

@[expose] public section

namespace Physlib.Meta.EntropicDynamicsFullEinsteinSource

/-- **[The complete two-index complex Einstein source balance is a projection of the
electrogravitic system].**
Given the coupled electromagnetic + gravitational field equation, the complex Einstein source balance
`complexStressEnergy T S + complexGravitationalTensor(…) Λ κ = 0` holds as a conclusion (not a premise),
alongside the real Einstein equation `G = κT`, the entropic curvature `Λ = κS`, and the BCJ
sector's scalar damping factorization `exp(−Im E) = exp(−S₁)·exp(−S₂)`. This is stronger than the
weak-field `R₀₀` component, but `Ric` and `scalarR` are inputs and the electrogravitic structure itself
is supplied. -/
@[zil_level physical_theorem]
theorem fullComplexEinsteinSource_isConclusion {ι : Type*}
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (κ m_R m_I c S₁ S₂ : ℝ) (k A : Fin 4 → ℝ)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ m_R m_I c S₁ S₂ k A) :
    complexStressEnergy T S + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S
      ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im) = Real.exp (-S₁) * Real.exp (-S₂) :=
  ⟨H.superoperatorEquations.2.2.2, H.einsteinMaxwell.1, H.einsteinMaxwell.2, H.bcjDoubleCopy⟩

/-- **[The complete algebraic electrogravitic source derived from stationarity].**
This is the non-circular successor of `fullComplexEinsteinSource_isConclusion`: it does not accept an
`ElectroGravitationalFieldEquation` as input. Instead, the Maxwell stress tensor is constructed from
`F = dA`, and the coupled structure is obtained from metric, gauge, and entropic stationarity by
`derive_electrogravitic_field_equation`. The complete complex source balance, its real and imaginary
Einstein sectors, the scalar damping factorization, both Maxwell equations, and the inverse-metric
witness are then conclusions. The Ricci tensor and scalar remain explicit inputs in this historical
variant; the metric-built successor below closes that interface. -/
@[zil_level physical_theorem]
theorem fullComplexEinsteinSource_from_stationary_action
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ m_R m_I c S₁ S₂ : ℝ) (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hInv : AreInverseMetrics g gInv)
    (hmetric :
      IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A)
    (hbcj : IsBCJEntropicStationary m_I c S₁ S₂)
    (hmaxwell : IsElectromagneticStationary k A) :
    (complexStressEnergy (maxwellStressEnergy g gInv (faraday k A)) S
          + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0
        ∧ einsteinFieldEquation Ric scalarR g
          (maxwellStressEnergy g gInv (faraday k A)) κ
        ∧ Λ = κ • S
        ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im)
          = Real.exp (-S₁) * Real.exp (-S₂))
      ∧ AreInverseMetrics g gInv
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0) := by
  obtain ⟨Heg, hInv', hsourceFree, hhomogeneous⟩ :=
    derive_electrogravitic_field_equation Ric scalarR g gInv Λ S
      κ m_R m_I c S₁ S₂ k A hκ hInv hmetric hbcj hmaxwell
  exact
    ⟨fullComplexEinsteinSource_isConclusion Ric scalarR g Λ
      (maxwellStressEnergy g gInv (faraday k A)) S
      κ m_R m_I c S₁ S₂ k A Heg,
      hInv', hsourceFree, hhomogeneous⟩

/-- **[The full complex source with curvature constructed from the metric].**
This is the metric-composed successor of
`fullComplexEinsteinSource_from_stationary_action`. The Ricci tensor and
scalar curvature in every conclusion are produced by the same coordinate
metric field through its Fréchet jets, Levi--Civita connection, connection
curvature and contractions. It therefore closes the previously unconnected
metric-to-curvature interface while retaining the explicit post-IBP
stationarity premise. -/
@[zil_level physical_theorem]
theorem fullComplexEinsteinSource_from_metricBuilt_stationary_action
    (g gInv : FourMetricField) (x : FourCoordinate)
    (Λ S : FourTensor) (κ m_R m_I c S₁ S₂ : ℝ) (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hGeom : IsFourMetricPair g gInv)
    (hmetric : IsElectrograviticMetricStationary
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) (gInv x) Λ S κ k A)
    (hbcj : IsBCJEntropicStationary m_I c S₁ S₂)
    (hmaxwell : IsElectromagneticStationary k A) :
    (complexStressEnergy
          (maxwellStressEnergy (g x) (gInv x) (faraday k A)) S
          + complexGravitationalTensor
              (metricBuiltEinsteinAt g gInv x) Λ κ = 0
        ∧ einsteinFieldEquation
          (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
          (g x) (maxwellStressEnergy (g x) (gInv x) (faraday k A)) κ
        ∧ Λ = κ • S
        ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c).im)
          = Real.exp (-S₁) * Real.exp (-S₂))
      ∧ AreInverseMetrics (g x) (gInv x)
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0)
      ∧ IsTorsionFree (metricBuiltConnectionField g gInv x)
      ∧ IsMetricCompatible
        (metricBuiltConnectionField g gInv x)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g x)
        (g x) := by
  obtain ⟨Heg, hInv', hsourceFree, hhomogeneous, htor, hcompat⟩ :=
    derive_metricBuilt_electrogravitic_field_equation
      g gInv x Λ S κ m_R m_I c S₁ S₂ k A
      hκ hGeom hmetric hbcj hmaxwell
  exact
    ⟨fullComplexEinsteinSource_isConclusion
      (metricBuiltRicciAt g gInv x) (metricBuiltScalarAt g gInv x)
      (g x) Λ (maxwellStressEnergy (g x) (gInv x) (faraday k A)) S
      κ m_R m_I c S₁ S₂ k A Heg,
      hInv', hsourceFree, hhomogeneous, htor, hcompat⟩

/-! ## B. The strengthened entropic-dynamics thesis -/

/-- **[The entropic-dynamics thesis with its gravity conditionals discharged].**
This capstone reuses the historical theorem's four quantum/reversible conclusions and replaces its
old gravity leg by:

* analytic recovery of the reversible complex-action weight as `η → ∞`;
* the non-circular Compton-cell identity `G = ℏ c σ₀⁴`;
* the weak-field Einstein `R₀₀` source derived from the Poisson equation; and
* the full nonlinear complex Einstein source derived from the electrogravitic system.

The Born-weight conclusion remains conditional on the displayed continuous symmetric-refinement
premises, and the nonlinear source remains conditional on the supplied electrogravitic field-equation
structure. -/
@[zil_level physical_theorem]
theorem entropicDynamics_derives_physics_strengthened
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [FiniteDimensional ℂ H]
    {d : Type*} [Fintype d] [DecidableEq d] {sd : ℕ}
    (ħ σ₀ c η cE : ℝ) (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0)
    (F : StaticPoissonField3) (x : StaticPotentialSpace3)
    {ι : Type*} (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (κ m_R m_I c₀ S₁ S₂ : ℝ) (k A : Fin 4 → ℝ)
    (Heg : ElectroGravitationalFieldEquation
      Ric scalarR g Λ T S κ m_R m_I c₀ S₁ S₂ k A) :
    (∀ ρ Φ : ℝ, 0 ≤ ρ → ‖edWaveFunction ρ Φ‖ ^ 2 = ρ)
      ∧ (∀ (Ψ : Ket d) (f : ℝ → ℝ), Continuous f →
          (∀ (j n : ℕ), 0 < n → j ≤ n → f ((j : ℝ) / n) = (j : ℝ) / n) →
          ∀ m : d, f (Complex.normSq (Ψ m)) = Complex.normSq (Ψ m))
      ∧ (∀ (U : E →ₗᵢ[ℂ] E) (s ψ : E), ‖⟪U s, U ψ⟫_ℂ‖ ^ 2 = ‖⟪s, ψ⟫_ℂ‖ ^ 2)
      ∧ (∀ (C : FrozenContext (H := H) (d := d) (sd := sd))
          (q p : SpaceTime sd) (ψ : H) (y : SpaceTime sd) (Γ_inf : ℝ),
          FrozenRecovery C q p ψ y Γ_inf)
      ∧ (Tendsto (fun τ : ℝ => Real.exp (-(entropicAction ħ τ / ħ))) atTop (𝓝 1)
          ∧ sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
              / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η) = ħ * c * σ₀ ^ 4
          ∧ weakFieldRicci00 (laplacianAt3 F.potential x) cE
              = 4 * Real.pi * F.newtonConstant * F.density x / cE ^ 2)
      ∧ (complexStressEnergy T S
            + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0
          ∧ einsteinFieldEquation Ric scalarR g T κ
          ∧ Λ = κ • S
          ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c₀).im)
              = Real.exp (-S₁) * Real.exp (-S₂)) := by
  exact
    ⟨fun ρ Φ hρ => edWaveFunction_modulus_sq ρ Φ hρ,
      fun Ψ f hf hrat m => deutsch_born_unequal Ψ f hf hrat m,
      fun U s ψ => generic_born_rule U s ψ,
      fun C q p ψ y Γ_inf => frozen_limit_recovers_standard_physics C q p ψ y Γ_inf,
      ⟨suppression_tendsto_one ħ,
        newtonG_from_positionVariance σ₀ c ħ η hσ hc hħ hK,
        weakFieldRicci00_at F cE x⟩,
      fullComplexEinsteinSource_isConclusion Ric scalarR g Λ T S
        κ m_R m_I c₀ S₁ S₂ k A Heg⟩

/-- **[The entropic-dynamics thesis with the electrogravitic equations derived variationally].**
This theorem strengthens `entropicDynamics_derives_physics_strengthened` at its remaining nonlinear
gravity premise. It constructs the electromagnetic stress source from `F = dA`; derives the complex
Einstein equation from arbitrary metric stationarity; derives the source-free Maxwell equation from
gauge-potential stationarity; obtains `dF = 0` from exactness; and derives the entropic split from scalar
stationarity. It therefore takes no `ElectroGravitationalFieldEquation` and no field equation as input.

The earlier honest qualifications remain: Born-weight selection uses its displayed symmetry/refinement
premises, and the post-integration-by-parts action first variations plus stationarity are physical
premises rather than consequences of information theory alone. -/
@[zil_level physical_theorem]
theorem entropicDynamics_derives_physics_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [FiniteDimensional ℂ H]
    {d : Type*} [Fintype d] [DecidableEq d] {sd : ℕ}
    (ħ σ₀ c η cE : ℝ) (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0)
    (F : StaticPoissonField3) (x : StaticPotentialSpace3)
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ m_R m_I c₀ S₁ S₂ : ℝ) (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hInv : AreInverseMetrics g gInv)
    (hmetric :
      IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A)
    (hbcj : IsBCJEntropicStationary m_I c₀ S₁ S₂)
    (hmaxwell : IsElectromagneticStationary k A) :
    (∀ ρ Φ : ℝ, 0 ≤ ρ → ‖edWaveFunction ρ Φ‖ ^ 2 = ρ)
      ∧ (∀ (Ψ : Ket d) (f : ℝ → ℝ), Continuous f →
          (∀ (j n : ℕ), 0 < n → j ≤ n → f ((j : ℝ) / n) = (j : ℝ) / n) →
          ∀ m : d, f (Complex.normSq (Ψ m)) = Complex.normSq (Ψ m))
      ∧ (∀ (U : E →ₗᵢ[ℂ] E) (s ψ : E), ‖⟪U s, U ψ⟫_ℂ‖ ^ 2 = ‖⟪s, ψ⟫_ℂ‖ ^ 2)
      ∧ (∀ (C : FrozenContext (H := H) (d := d) (sd := sd))
          (q p : SpaceTime sd) (ψ : H) (y : SpaceTime sd) (Γ_inf : ℝ),
          FrozenRecovery C q p ψ y Γ_inf)
      ∧ (Tendsto (fun τ : ℝ => Real.exp (-(entropicAction ħ τ / ħ))) atTop (𝓝 1)
          ∧ sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
              / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η) = ħ * c * σ₀ ^ 4
          ∧ weakFieldRicci00 (laplacianAt3 F.potential x) cE
              = 4 * Real.pi * F.newtonConstant * F.density x / cE ^ 2)
      ∧ (complexStressEnergy (maxwellStressEnergy g gInv (faraday k A)) S
            + complexGravitationalTensor (einsteinTensor Ric scalarR g) Λ κ = 0
          ∧ einsteinFieldEquation Ric scalarR g
            (maxwellStressEnergy g gInv (faraday k A)) κ
          ∧ Λ = κ • S
          ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c₀).im)
              = Real.exp (-S₁) * Real.exp (-S₂))
      ∧ AreInverseMetrics g gInv
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0) := by
  obtain ⟨Heg, hInv', hsourceFree, hhomogeneous⟩ :=
    derive_electrogravitic_field_equation Ric scalarR g gInv Λ S
      κ m_R m_I c₀ S₁ S₂ k A hκ hInv hmetric hbcj hmaxwell
  obtain ⟨hAmplitude, hBorn, hTransport, hFrozen, hWeak, hFull⟩ :=
    entropicDynamics_derives_physics_strengthened
      (E := E) (H := H) (d := d) (sd := sd)
      ħ σ₀ c η cE hσ hc hħ hK F x Ric scalarR g Λ
      (maxwellStressEnergy g gInv (faraday k A)) S
      κ m_R m_I c₀ S₁ S₂ k A Heg
  exact ⟨hAmplitude, hBorn, hTransport, hFrozen, hWeak, hFull,
    hInv', hsourceFree, hhomogeneous⟩

/-- **[The public entropic-dynamics thesis with metric-built curvature and
one coupled stationarity premise].** This is the metric-composed successor of
`entropicDynamics_derives_physics_variational`. Ricci and scalar curvature
are no longer supplied independently, and the three sector-stationarity
predicates are represented by one direct-sum first variation. The theorem
also exposes the torsion-free and metric-compatible certificates of the
constructed Levi--Civita connection.

The direct-sum carrier is a composition of known first variations, not a
claim that their common continuum field action has already been constructed. -/
@[zil_level physical_theorem]
theorem entropicDynamics_derives_physics_metricBuilt_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [FiniteDimensional ℂ H]
    {d : Type*} [Fintype d] [DecidableEq d] {sd : ℕ}
    (ħ σ₀ c η cE : ℝ) (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0)
    (F : StaticPoissonField3) (xPoisson : StaticPotentialSpace3)
    (g gInv : FourMetricField) (xGeom : FourCoordinate)
    (Λ S : FourTensor) (κ m_R m_I c₀ S₁ S₂ : ℝ)
    (k A : Fin 4 → ℝ)
    (hκ : κ ≠ 0) (hGeom : IsFourMetricPair g gInv)
    (hstationary : IsCoupledElectrograviticStationary
      (metricBuiltRicciAt g gInv xGeom) (metricBuiltScalarAt g gInv xGeom)
      (g xGeom) (gInv xGeom) Λ S κ m_I c₀ S₁ S₂ k A) :
    (∀ ρ Φ : ℝ, 0 ≤ ρ → ‖edWaveFunction ρ Φ‖ ^ 2 = ρ)
      ∧ (∀ (Ψ : Ket d) (f : ℝ → ℝ), Continuous f →
          (∀ (j n : ℕ), 0 < n → j ≤ n → f ((j : ℝ) / n) = (j : ℝ) / n) →
          ∀ m : d, f (Complex.normSq (Ψ m)) = Complex.normSq (Ψ m))
      ∧ (∀ (U : E →ₗᵢ[ℂ] E) (s ψ : E), ‖⟪U s, U ψ⟫_ℂ‖ ^ 2 = ‖⟪s, ψ⟫_ℂ‖ ^ 2)
      ∧ (∀ (C : FrozenContext (H := H) (d := d) (sd := sd))
          (q p : SpaceTime sd) (ψ : H) (y : SpaceTime sd) (Γ_inf : ℝ),
          FrozenRecovery C q p ψ y Γ_inf)
      ∧ (Tendsto (fun τ : ℝ => Real.exp (-(entropicAction ħ τ / ħ))) atTop (𝓝 1)
          ∧ sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
              / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η) = ħ * c * σ₀ ^ 4
          ∧ weakFieldRicci00 (laplacianAt3 F.potential xPoisson) cE
              = 4 * Real.pi * F.newtonConstant * F.density xPoisson / cE ^ 2)
      ∧ (complexStressEnergy
            (maxwellStressEnergy (g xGeom) (gInv xGeom) (faraday k A)) S
            + complexGravitationalTensor
                (metricBuiltEinsteinAt g gInv xGeom) Λ κ = 0
          ∧ einsteinFieldEquation
              (metricBuiltRicciAt g gInv xGeom) (metricBuiltScalarAt g gInv xGeom)
              (g xGeom)
              (maxwellStressEnergy (g xGeom) (gInv xGeom) (faraday k A)) κ
          ∧ Λ = κ • S
          ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c₀).im)
              = Real.exp (-S₁) * Real.exp (-S₂))
      ∧ AreInverseMetrics (g xGeom) (gInv xGeom)
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
        k lam * faraday k A μ ν + k μ * faraday k A ν lam
          + k ν * faraday k A lam μ = 0)
      ∧ IsTorsionFree (metricBuiltConnectionField g gInv xGeom)
      ∧ IsMetricCompatible
        (metricBuiltConnectionField g gInv xGeom)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) g xGeom)
        (g xGeom)
      ∧ FirstBianchi (metricBuiltRiemannAt g gInv xGeom) := by
  obtain ⟨hmetric, hmaxwell, hbcj⟩ :=
    (coupledElectrograviticStationary_iff
      (metricBuiltRicciAt g gInv xGeom) (metricBuiltScalarAt g gInv xGeom)
      (g xGeom) (gInv xGeom) Λ S κ m_I c₀ S₁ S₂ k A).mp hstationary
  have hInv : AreInverseMetrics (g xGeom) (gInv xGeom) :=
    ⟨hGeom.inverse_right xGeom, hGeom.inverse_left xGeom⟩
  obtain ⟨hAmplitude, hBorn, hTransport, hFrozen, hWeak, hFull,
      hInv', hsourceFree, hhomogeneous⟩ :=
    entropicDynamics_derives_physics_variational
      (E := E) (H := H) (d := d) (sd := sd)
      ħ σ₀ c η cE hσ hc hħ hK F xPoisson
      (metricBuiltRicciAt g gInv xGeom) (metricBuiltScalarAt g gInv xGeom)
      (g xGeom) (gInv xGeom) Λ S κ m_R m_I c₀ S₁ S₂ k A
      hκ hInv hmetric hbcj hmaxwell
  have hFull' :
      complexStressEnergy
          (maxwellStressEnergy (g xGeom) (gInv xGeom) (faraday k A)) S
          + complexGravitationalTensor
              (metricBuiltEinsteinAt g gInv xGeom) Λ κ = 0
        ∧ einsteinFieldEquation
            (metricBuiltRicciAt g gInv xGeom) (metricBuiltScalarAt g gInv xGeom)
            (g xGeom)
            (maxwellStressEnergy (g xGeom) (gInv xGeom) (faraday k A)) κ
        ∧ Λ = κ • S
        ∧ Real.exp (-(complexEinsteinEnergy m_R m_I c₀).im)
            = Real.exp (-S₁) * Real.exp (-S₂) := by
    simpa [metricBuiltEinsteinAt] using hFull
  exact ⟨hAmplitude, hBorn, hTransport, hFrozen, hWeak, hFull',
    hInv', hsourceFree, hhomogeneous,
    (metricBuiltConnectionField_isLeviCivita g gInv hGeom xGeom).1,
    (metricBuiltConnectionField_isLeviCivita g gInv hGeom xGeom).2,
    metricBuiltRiemannAt_firstBianchi g gInv hGeom xGeom⟩

end Physlib.Meta.EntropicDynamicsFullEinsteinSource

end

/- ZIL-BEGIN -/

zil attach Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion where
  formalizes @ "claim:the-complete-two-index-complex-einstein-source-balance-real-einstein-equation-entropic-curvature-and-scalar-damping-factorization-are-projections-of-a-supplied-electrogravitic-field-equation-structure",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation.superoperatorEquations",
  caveat @ "premise:the-electrogravitic-field-equation-structure-is-supplied-and-this-theorem-does-not-derive-it-from-the-gauge-sector",
  caveat @ "scope:ricci-and-scalar-curvature-are-inputs-use-the-metric-built-successor-for-the-metric-to-curvature-composition"

zil attach Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_from_stationary_action where
  formalizes @ "claim:the-complete-two-index-complex-einstein-source-real-and-entropic-einstein-sectors-scalar-damping-factorization-and-both-maxwell-equations-are-conclusions-of-coupled-stationarity-with-the-maxwell-stress-source-constructed-from-faraday-d-a",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation",
  supported_by @ "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion",
  caveat @ "premise:stationarity-of-the-post-integration-by-parts-metric-maxwell-and-entropic-first-variations-remains-the-physical-action-principle",
  caveat @ "scope:four-dimensional-momentum-space-source-free-maxwell-carrier-not-a-global-sourced-curved-spacetime-existence-theorem",
  caveat @ "scope:ricci-and-scalar-curvature-are-independent-inputs-in-this-historical-variant"

zil attach Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_from_metricBuilt_stationary_action where
  formalizes @ "claim:the-full-complex-source-balance-and-einstein-maxwell-equations-use-ricci-scalar-and-einstein-tensors-constructed-from-the-same-coordinate-metric-field-and-its-levi-civita-curvature-chain",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation",
  supported_by @ "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion",
  caveat @ "premise:post-integration-by-parts-stationarity-and-a-symmetric-two-sided-metric-inverse-pair-remain-explicit-inputs",
  caveat @ "scope:metric-built-chartwise-field-equation-not-a-global-cauchy-existence-or-unified-einstein-hilbert-maxwell-functional-derivative-theorem"

zil attach Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_metricBuilt_variational where
  formalizes @ "claim:the-public-entropic-dynamics-capstone-uses-ricci-scalar-and-einstein-curvature-constructed-from-one-metric-field-and-one-direct-sum-stationarity-premise-while-exposing-levi-civita-certificates",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticStationary_iff",
  supported_by @ "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_variational",
  caveat @ "premise:the-direct-sum-post-integration-by-parts-first-variation-is-stationary",
  caveat @ "scope:this-closes-the-public-metric-curvature-aggregate-interface-but-does-not-construct-the-underlying-continuum-einstein-hilbert-maxwell-action-or-global-cauchy-solution"

zil_file_contract physlib.entropicDynamicsMetricBuiltVariationalThesis where
  promises "A public entropic-dynamics capstone now replaces independent Ricci and scalar-curvature inputs by the repository metric-to-Levi-Civita-to-Riemann-to-Ricci contraction chain, accepts one direct-sum stationarity premise, and returns torsion-free, metric-compatible, and algebraic first-Bianchi certificates together with the complex Einstein-Maxwell-entropic conclusions."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticStationary_iff",
    "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_variational"
  ]
  forbids_substitutes [
    "supplying Ricci or scalar curvature independently of the metric field",
    "calling the direct-sum first variation an underlying continuum field action",
    "claiming chartwise metric composition proves a global nonlinear Cauchy solution"
  ]
  witnessed_by [
    Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_metricBuilt_variational
  ]

zil_file_contract physlib.entropicDynamicsMetricBuiltElectrograviticSource where
  promises "The strongest metric-composed source theorem no longer accepts independent Ricci or scalar-curvature matrices: both are constructed from the same coordinate metric field through Frechet jets, Levi-Civita connection, Riemann curvature and contraction before entering the variational complex Einstein-Maxwell conclusion."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation",
    "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion"
  ]
  forbids_substitutes [
    "supplying Ricci and scalar curvature independently of the metric field",
    "claiming the post-integration-by-parts first variation is derived from one unified continuum action",
    "claiming chartwise equations prove global nonlinear Cauchy existence"
  ]
  witnessed_by [
    Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_from_metricBuilt_stationary_action
  ]

zil_file_contract physlib.entropicDynamicsElectrograviticStationarySource where
  promises "The strongest full-source theorem no longer takes an ElectroGravitationalFieldEquation as a premise. It constructs the Maxwell stress source from F=dA and derives the coupled complex Einstein, Maxwell, and entropic equations from stationarity, retaining exact inverse-metric data."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation",
    "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion"
  ]
  forbids_substitutes [
    "supplying an electrogravitic field-equation structure as the premise of the strongest source theorem",
    "leaving the electromagnetic stress tensor unrelated to the gauge potential",
    "claiming the finite source-free momentum carrier is global sourced curved Maxwell evolution"
  ]
  witnessed_by [
    Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_from_stationary_action
  ]

zil attach Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_strengthened where
  formalizes @ "claim:the-public-entropic-dynamics-thesis-with-analytic-reversible-convergence-noncircular-compton-cell-newton-coupling-poisson-derived-weak-einstein-source-and-the-full-nonlinear-complex-einstein-source-as-conclusions",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.deutsch_born_unequal",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule.generic_born_rule",
  supported_by @ "lean:Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.weakFieldRicci00_at",
  supported_by @ "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion",
  caveat @ "epistemic:born-weight-selection-still-requires-continuity-and-symmetric-refinement-premises",
  caveat @ "claim:the-full-nonlinear-source-is-derived-inside-the-supplied-electrogravitic-field-equation-structure-not-from-no-physical-input"

zil attach Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_variational where
  formalizes @ "claim:the-public-entropic-dynamics-thesis-with-the-electromagnetic-stress-source-and-complex-einstein-maxwell-equations-derived-from-coupled-action-stationarity-rather-than-a-supplied-electrogravitic-field-equation",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_strengthened",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation",
  caveat @ "epistemic:born-weight-selection-retains-the-displayed-continuity-and-symmetric-refinement-premises",
  caveat @ "premise:coupled-post-integration-by-parts-first-variation-formulas-and-stationarity-are-action-level-physical-inputs",
  caveat @ "scope:finite-momentum-space-source-free-maxwell-carrier-not-general-global-sourced-curved-spacetime-existence"

zil_file_contract physlib.entropicDynamicsVariationalThesis where
  promises "The historical variational entropic-dynamics capstone no longer accepts an electrogravitic field equation. It derives the Maxwell stress source and complete complex Einstein-Maxwell-entropic equation package from explicit stationarity premises, while retaining the earlier reversible-limit, Compton-cell G, and weak-field Poisson conclusions. The metric-built successor is tracked by physlib.entropicDynamicsMetricBuiltVariationalThesis."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_strengthened",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation"
  ]
  forbids_substitutes [
    "supplying an ElectroGravitationalFieldEquation as a premise",
    "claiming unitarity alone derives the Born weight",
    "calling action stationarity a consequence of information theory",
    "calling the momentum-space source-free Maxwell carrier a global sourced PDE"
  ]
  witnessed_by [
    Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_variational
  ]

zil_file_contract physlib.entropicDynamicsFullEinsteinSource where
  promises "The historical projection theorem fullComplexEinsteinSource_isConclusion exposes the complete two-index source balance, real and entropic Einstein sectors, and scalar damping split carried by an explicit ElectroGravitationalFieldEquation. It is classified as a consistency projection, not a gravity-from-gauge derivation. The stationarity-derived and metric-built theorems are tracked by separate contracts."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation.superoperatorEquations",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation.einsteinMaxwell"]
  forbids_substitutes ["only the weak-field R00 component, whereas this projection exposes the complete two-index complex Einstein source balance",
    "claiming this historical projection derives the supplied ElectroGravitationalFieldEquation",
    "calling the scalar damping factorization a general amplitude-level BCJ derivation",
    "claiming Ricci and scalar curvature are constructed from the metric in this historical theorem"]
  witnessed_by [Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion]

zil_file_contract physlib.entropicDynamicsStrengthenedThesis where
  promises "A strengthened entropic-dynamics capstone reuses the historical theorem's Born-amplitude reconstruction, conditional Born-weight selection, unitary transport, and exact frozen-sector reduction, then adds the analytic reversible limit, the non-circular G-free Compton-cell Newton identity, the Poisson-derived weak Einstein source, and the full nonlinear complex Einstein source as a conclusion of the electrogravitic system."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
    "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.deutsch_born_unequal",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule.generic_born_rule",
    "lean:Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.weakFieldRicci00_at",
    "lean:Physlib.Meta.EntropicDynamicsFullEinsteinSource.fullComplexEinsteinSource_isConclusion"
  ]
  forbids_substitutes [
    "claiming the Born weight follows from unitarity alone",
    "reintroducing the circular holographic bit count containing Newton G",
    "taking the complex Einstein source balance as an independent premise",
    "claiming the electrogravitic field-equation structure is derived without physical model input"
  ]
  witnessed_by [
    Physlib.Meta.EntropicDynamicsFullEinsteinSource.entropicDynamics_derives_physics_strengthened
  ]

/- ZIL-END -/
