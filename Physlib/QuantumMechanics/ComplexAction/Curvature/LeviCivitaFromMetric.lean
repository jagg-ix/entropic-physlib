/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# The Levi-Civita connection from a metric, in any dimension

`ConnectionCovariantHessian` supplies the metric covariant derivative `∇_λ g_μν` (`metricCovariantDeriv`),
metric compatibility `∇g = 0` (`IsMetricCompatible`) and torsion-freeness (`IsTorsionFree`) — the *conditions*
defining a Levi-Civita connection — but takes the connection `Γ` as data. This module supplies the missing
*construction*: the Christoffel symbols computed from the metric,
  `Γ^σ_{μν} = ½ g^{σρ}(∂_μ g_{ρν} + ∂_ν g_{ρμ} − ∂_ρ g_{μν})`,
and proves it satisfies both defining conditions in **any** dimension (in particular `n = 4`). This is the
general metric→Christoffel derivation; the `1+1` `weakFieldLeviCivita2` of
`ComptonClock.NewtonianLimitCurvatureAPI` is one instance.

* `christoffelFromMetric` — the Levi-Civita connection `Γ^σ_{μν}` from `gInv` and the metric derivatives `dg`.
* `christoffelFromMetric_isTorsionFree` — `Γ^σ_{μν} = Γ^σ_{νμ}` (symmetric metric derivatives).
* `christoffel_contraction` — the key contraction `Γ^σ_{lμ} g_{σν} = ½(∂_l g_{νμ} + ∂_μ g_{νl} − ∂_ν g_{lμ})`.
* `christoffelFromMetric_isMetricCompatible` — `∇_λ g_μν = 0`, so `christoffelFromMetric` *is* the metric's
  Levi-Civita connection.
* `christoffelFromMetric_isLeviCivita4` — the `n = 4` (spacetime) statement: torsion-free and metric-compatible.

**Honest layering.** All exact. The metric enters through `g` (symmetric), its inverse `gInv` (`gInv·g = 1`,
symmetric) and its partial derivatives `dg` (each symmetric) — the standard hypotheses used throughout
`Curvature`. No coordinate calculus is invoked: `dg κ = ∂_κ g` is supplied as the metric's derivative data.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric

open scoped BigOperators Manifold ContDiff Topology
open Bundle NormedSpace
open Matrix
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

variable {ι : Type*} [Fintype ι]

/-- **The Levi-Civita connection of a metric** `Γ^σ_{μν} = ½ g^{σρ}(∂_μ g_{ρν} + ∂_ν g_{ρμ} − ∂_ρ g_{μν})`,
computed from the inverse metric `gInv` and the metric's partial derivatives `dg` (`dg κ = ∂_κ g`), in the
`Γ : ι → Matrix ι ι ℝ` form `(Γ σ) μ ν = Γ^σ_{μν}`. -/
noncomputable def christoffelFromMetric (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) :
    ι → Matrix ι ι ℝ :=
  fun σ => Matrix.of fun μ ν => (1 / 2) * ∑ ρ, gInv σ ρ * (dg μ ρ ν + dg ν ρ μ - dg ρ μ ν)

/-- **[The Levi-Civita connection is torsion-free] `Γ^σ_{μν} = Γ^σ_{νμ}`** — from the symmetry of the metric
derivatives `∂_κ g_{ab} = ∂_κ g_{ba}`. -/
lemma christoffelFromMetric_isTorsionFree (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
    (hdg : ∀ κ, (dg κ)ᵀ = dg κ) : IsTorsionFree (christoffelFromMetric gInv dg) := by
  intro σ
  ext μ ν
  simp only [Matrix.transpose_apply, christoffelFromMetric, Matrix.of_apply]
  refine congrArg _ (Finset.sum_congr rfl fun ρ _ => ?_)
  rw [show dg ρ ν μ = dg ρ μ ν from by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun (hdg ρ) μ) ν)]
  ring

/-- **[The defining contraction] `Γ^σ_{lμ} g_{σν} = ½(∂_l g_{νμ} + ∂_μ g_{νl} − ∂_ν g_{lμ})`** — contracting
the upper index of the Christoffel symbol against the metric collapses the `g^{σρ}g_{σν}` to `δ^ρ_ν`. -/
lemma christoffel_contraction [DecidableEq ι] {g gInv : Matrix ι ι ℝ} (dg : ι → Matrix ι ι ℝ)
    (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (l μ ν : ι) :
    ∑ σ, (christoffelFromMetric gInv dg σ) l μ * g σ ν
      = (1 / 2) * (dg l ν μ + dg μ ν l - dg ν l μ) := by
  have hsym : ∀ σ ρ, gInv σ ρ = gInv ρ σ := fun σ ρ => by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hgi ρ) σ)
  have key : ∀ ρ : ι, (∑ σ, gInv σ ρ * g σ ν) = (if ρ = ν then (1 : ℝ) else 0) := by
    intro ρ
    have hmul : (∑ σ, gInv σ ρ * g σ ν) = (gInv * g) ρ ν := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun σ _ => by rw [hsym σ ρ]
    rw [hmul, hinv, Matrix.one_apply]
  have step : ∀ σ : ι, (christoffelFromMetric gInv dg σ) l μ * g σ ν
      = (1 / 2) * ∑ ρ, (dg l ρ μ + dg μ ρ l - dg ρ l μ) * (gInv σ ρ * g σ ν) := by
    intro σ
    simp only [christoffelFromMetric, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  have inner : ∀ ρ : ι, (∑ σ, (dg l ρ μ + dg μ ρ l - dg ρ l μ) * (gInv σ ρ * g σ ν))
      = (dg l ρ μ + dg μ ρ l - dg ρ l μ) * (if ρ = ν then (1 : ℝ) else 0) := by
    intro ρ; rw [← Finset.mul_sum, key ρ]
  rw [Finset.sum_congr rfl fun σ _ => step σ, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun ρ _ => inner ρ]
  simp [Finset.sum_ite_eq']

/-- **[The Levi-Civita connection is metric-compatible] `∇_λ g_μν = 0`** (`IsMetricCompatible`): the
`christoffelFromMetric` connection annihilates the metric it was built from. Together with
`christoffelFromMetric_isTorsionFree`, this is the statement that it *is* the metric's Levi-Civita connection —
the metric→Christoffel derivation, in any dimension. -/
lemma christoffelFromMetric_isMetricCompatible [DecidableEq ι] {g gInv : Matrix ι ι ℝ}
    (dg : ι → Matrix ι ι ℝ)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (hdg : ∀ κ, (dg κ)ᵀ = dg κ) :
    IsMetricCompatible (christoffelFromMetric gInv dg) dg g := by
  intro l
  ext μ ν
  simp only [metricCovariantDeriv, Matrix.zero_apply]
  rw [christoffel_contraction dg hgi hinv l μ ν]
  have hgsymm : ∀ a b, g a b = g b a := fun a b => by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hg b) a)
  rw [show (∑ σ, (christoffelFromMetric gInv dg σ) l ν * g μ σ)
        = ∑ σ, (christoffelFromMetric gInv dg σ) l ν * g σ μ from
      Finset.sum_congr rfl fun σ _ => by rw [hgsymm μ σ]]
  rw [christoffel_contraction dg hgi hinv l ν μ]
  have e1 := congrFun (congrFun (hdg l) μ) ν
  have e2 := congrFun (congrFun (hdg μ) ν) l
  have e3 := congrFun (congrFun (hdg ν) l) μ
  simp only [Matrix.transpose_apply] at e1 e2 e3
  linarith [e1, e2, e3]

/-- **[The 4-D (spacetime) Levi-Civita connection]** in `n = 4` (spacetime index `Fin 1 ⊕ Fin 3`), the
`christoffelFromMetric` connection is torsion-free and metric-compatible — the metric→Christoffel derivation
completed in four dimensions. -/
lemma christoffelFromMetric_isLeviCivita4
    {g gInv : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ} (dg : Fin 1 ⊕ Fin 3 → Matrix _ _ ℝ)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (hdg : ∀ κ, (dg κ)ᵀ = dg κ) :
    IsTorsionFree (christoffelFromMetric gInv dg)
      ∧ IsMetricCompatible (christoffelFromMetric gInv dg) dg g :=
  ⟨christoffelFromMetric_isTorsionFree gInv dg hdg,
    christoffelFromMetric_isMetricCompatible dg hg hgi hinv hdg⟩

/-! ## B. Bundled Levi-Civita connection on a finite real chart -/

/-- The model vector space of a finite real coordinate chart. -/
abbrev FiniteCoordinateSpace (ι : Type*) := ι → ℝ

/-- Smoothness at a point of a tangent section on the self-modelled finite real chart. -/
abbrev TangentSectionMDiffAt
    (σ : (x : FiniteCoordinateSpace ι) →
      TangentSpace (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) x)
    (x : FiniteCoordinateSpace ι) : Prop :=
  MDifferentiableAt (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι))
    ((modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)).prod
      (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)))
    (fun y => (⟨y, σ y⟩ :
      TangentBundle (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι))
        (FiniteCoordinateSpace ι))) x

/-- The Christoffel correction `v ↦ Γ(v,u)` as a continuous linear map in the
direction vector `v`. -/
noncomputable def coordinateConnectionAction
    (Γ : ι → Matrix ι ι ℝ) (u : FiniteCoordinateSpace ι) :
    FiniteCoordinateSpace ι →L[ℝ] FiniteCoordinateSpace ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ρ => ∑ μ, ∑ σ, (Γ ρ) μ σ * v μ * u σ
      map_add' := by
        intro v w
        funext ρ
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro μ _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        ring
      map_smul' := by
        intro c v
        funext ρ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro μ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        ring }

@[simp]
lemma coordinateConnectionAction_apply (Γ : ι → Matrix ι ι ℝ)
    (u v : FiniteCoordinateSpace ι) (ρ : ι) :
    coordinateConnectionAction Γ u v ρ =
      ∑ μ, ∑ σ, (Γ ρ) μ σ * v μ * u σ :=
  rfl

lemma coordinateConnectionAction_add (Γ : ι → Matrix ι ι ℝ)
    (u w : FiniteCoordinateSpace ι) :
    coordinateConnectionAction Γ (u + w) =
      coordinateConnectionAction Γ u + coordinateConnectionAction Γ w := by
  ext v ρ
  simp only [coordinateConnectionAction_apply, Pi.add_apply,
    _root_.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma coordinateConnectionAction_smul (Γ : ι → Matrix ι ι ℝ) (c : ℝ)
    (u : FiniteCoordinateSpace ι) :
    coordinateConnectionAction Γ (c • u) = c • coordinateConnectionAction Γ u := by
  ext v ρ
  simp only [coordinateConnectionAction_apply, Pi.smul_apply, smul_eq_mul,
    _root_.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma coordinateConnectionAction_commute_of_torsionFree
    (Γ : ι → Matrix ι ι ℝ) (hΓ : IsTorsionFree Γ)
    (u v : FiniteCoordinateSpace ι) :
    coordinateConnectionAction Γ u v = coordinateConnectionAction Γ v u := by
  ext ρ
  simp only [coordinateConnectionAction_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro σ _
  have hcomp : (Γ ρ) σ μ = (Γ ρ) μ σ := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hΓ ρ) μ) σ
  rw [hcomp]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma tangentSection_differentiableAt
    (σ : (x : FiniteCoordinateSpace ι) →
      TangentSpace (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) x)
    (x : FiniteCoordinateSpace ι) (hσ : TangentSectionMDiffAt σ x) :
    DifferentiableAt ℝ σ x := by
  unfold TangentSectionMDiffAt at hσ
  rw [mdifferentiableAt_section] at hσ
  simp only [trivializationAt_model_space_apply] at hσ
  simpa only [mdifferentiableAt_iff_differentiableAt] using hσ

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary Fréchet derivative of a tangent section on the self-modelled chart. -/
noncomputable def tangentSectionFDeriv
    (σ : (x : FiniteCoordinateSpace ι) →
      TangentSpace (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) x)
    (x : FiniteCoordinateSpace ι) :
    FiniteCoordinateSpace ι →L[ℝ] FiniteCoordinateSpace ι :=
  fderiv ℝ σ x

lemma tangentSectionFDeriv_apply_component [DecidableEq ι]
    (σ : (x : FiniteCoordinateSpace ι) →
      TangentSpace (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) x)
    (x v : FiniteCoordinateSpace ι) (ρ : ι)
    (hσ : ∀ τ, DifferentiableAt ℝ (fun y => σ y τ) x) :
    tangentSectionFDeriv σ x v ρ = fderiv ℝ (fun y => σ y ρ) x v := by
  unfold tangentSectionFDeriv
  rw [fderiv_pi hσ]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma tangentSectionFDeriv_add
    (σ σ' : (x : FiniteCoordinateSpace ι) →
      TangentSpace (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) x)
    (x : FiniteCoordinateSpace ι)
    (hσ : TangentSectionMDiffAt σ x) (hσ' : TangentSectionMDiffAt σ' x) :
    tangentSectionFDeriv (σ + σ') x =
      tangentSectionFDeriv σ x + tangentSectionFDeriv σ' x := by
  exact fderiv_add (tangentSection_differentiableAt σ x hσ)
    (tangentSection_differentiableAt σ' x hσ')

set_option backward.isDefEq.respectTransparency false in
lemma tangentSectionFDeriv_smul
    (σ : (x : FiniteCoordinateSpace ι) →
      TangentSpace (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) x)
    (g : FiniteCoordinateSpace ι → ℝ) (x : FiniteCoordinateSpace ι)
    (hσ : TangentSectionMDiffAt σ x) (hg : DifferentiableAt ℝ g x) :
    tangentSectionFDeriv (g • σ) x =
      g x • tangentSectionFDeriv σ x +
        (fderiv ℝ g x).smulRight (show FiniteCoordinateSpace ι from σ x) := by
  exact fderiv_smul hg (tangentSection_differentiableAt σ x hσ)

set_option backward.isDefEq.respectTransparency false in
/-- **Bundled coordinate covariant derivative.** The repository's Christoffel
field is promoted to Mathlib's coordinate-free `CovariantDerivative`; its
action is the Fréchet derivative plus the usual `Γ(v,σ)` correction. -/
noncomputable def coordinateCovariantDerivative
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ) :
    CovariantDerivative (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι))
      (FiniteCoordinateSpace ι)
      (TangentSpace (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) :
        FiniteCoordinateSpace ι → Type _) where
  toFun σ x := tangentSectionFDeriv σ x + coordinateConnectionAction (Γ x) (σ x)
  isCovariantDerivativeOnUniv := by
    constructor
    · intro σ σ' x hσ hσ' hx
      change tangentSectionFDeriv (σ + σ') x +
          coordinateConnectionAction (Γ x)
            ((show FiniteCoordinateSpace ι from σ x) +
              (show FiniteCoordinateSpace ι from σ' x)) =
        (tangentSectionFDeriv σ x +
          coordinateConnectionAction (Γ x) (show FiniteCoordinateSpace ι from σ x)) +
        (tangentSectionFDeriv σ' x +
          coordinateConnectionAction (Γ x) (show FiniteCoordinateSpace ι from σ' x))
      rw [tangentSectionFDeriv_add σ σ' x hσ hσ']
      rw [coordinateConnectionAction_add]
      module
    · intro σ g x hσ hg hx
      change (show FiniteCoordinateSpace ι →L[ℝ] FiniteCoordinateSpace ι from
          tangentSectionFDeriv (g • σ) x +
            coordinateConnectionAction (Γ x) (g x • (show FiniteCoordinateSpace ι from σ x))) =
        (show FiniteCoordinateSpace ι →L[ℝ] FiniteCoordinateSpace ι from
          g x • (tangentSectionFDeriv σ x + coordinateConnectionAction (Γ x) (σ x)) +
          (show FiniteCoordinateSpace ι →L[ℝ] ℝ from
            mfderiv (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι))
              (modelWithCornersSelf ℝ ℝ) g x).smulRight
                (show FiniteCoordinateSpace ι from σ x))
      rw [tangentSectionFDeriv_smul σ g x hσ
        (mdifferentiableAt_iff_differentiableAt.mp hg)]
      rw [coordinateConnectionAction_smul]
      rw [show mfderiv (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι))
          (modelWithCornersSelf ℝ ℝ) g x = fderiv ℝ g x from mfderiv_eq_fderiv]
      module

lemma coordinateCovariantDerivative_apply
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (σ : FiniteCoordinateSpace ι → FiniteCoordinateSpace ι)
    (x v : FiniteCoordinateSpace ι) (ρ : ι) :
    coordinateCovariantDerivative Γ σ x v ρ =
      tangentSectionFDeriv σ x v ρ +
        ∑ μ, ∑ τ, (Γ x ρ) μ τ * v μ * σ x τ := by
  rfl

lemma coordinateCovariantDerivative_constantBasis_apply [DecidableEq ι]
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (x : FiniteCoordinateSpace ι) (σ μ ρ : ι) :
    coordinateCovariantDerivative Γ (fun _ => Pi.single σ 1) x
      (Pi.single μ 1) ρ = (Γ x ρ) μ σ := by
  rw [coordinateCovariantDerivative_apply]
  simp [tangentSectionFDeriv, Pi.single_apply, Finset.sum_ite_eq']

set_option backward.isDefEq.respectTransparency false in
/-- A coefficientwise torsion-free Christoffel field gives a genuinely
torsion-free bundled covariant derivative. -/
lemma coordinateCovariantDerivative_torsion_eq_zero
    (Γ : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (hΓ : ∀ x, IsTorsionFree (Γ x)) :
    (coordinateCovariantDerivative Γ).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  have hbracket :
      VectorField.mlieBracket (modelWithCornersSelf ℝ (FiniteCoordinateSpace ι)) X Y x =
        tangentSectionFDeriv Y x (X x) - tangentSectionFDeriv X x (Y x) := by
    rw [← VectorField.mlieBracketWithin_univ]
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    rw [VectorField.lieBracketWithin_univ]
    rfl
  rw [hbracket]
  change (tangentSectionFDeriv Y x (X x) +
      coordinateConnectionAction (Γ x) (Y x) (X x)) -
    (tangentSectionFDeriv X x (Y x) +
      coordinateConnectionAction (Γ x) (X x) (Y x)) = _
  rw [coordinateConnectionAction_commute_of_torsionFree (Γ x) (hΓ x) (Y x) (X x)]
  module

/-- The metric-built Christoffel field as a bundled Mathlib covariant derivative
on the finite real chart. -/
noncomputable def metricLeviCivitaCovariantDerivative
    (gInv : FiniteCoordinateSpace ι → Matrix ι ι ℝ)
    (dg : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ) :=
  coordinateCovariantDerivative (fun x => christoffelFromMetric (gInv x) (dg x))

/-- The bundled metric-built connection has zero Mathlib torsion whenever the
metric first-jet matrices are symmetric. -/
lemma metricLeviCivitaCovariantDerivative_torsion_eq_zero
    (gInv : FiniteCoordinateSpace ι → Matrix ι ι ℝ)
    (dg : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (hdg : ∀ x κ, (dg x κ)ᵀ = dg x κ) :
    (metricLeviCivitaCovariantDerivative gInv dg).torsion = 0 := by
  apply coordinateCovariantDerivative_torsion_eq_zero
  intro x
  exact christoffelFromMetric_isTorsionFree (gInv x) (dg x) (hdg x)

/-- The same bundled metric-built connection is coefficientwise compatible
with the metric field from which it is constructed. -/
lemma metricLeviCivitaCovariantDerivative_isMetricCompatible [DecidableEq ι]
    (g gInv : FiniteCoordinateSpace ι → Matrix ι ι ℝ)
    (dg : FiniteCoordinateSpace ι → ι → Matrix ι ι ℝ)
    (hg : ∀ x, (g x)ᵀ = g x) (hgi : ∀ x, (gInv x)ᵀ = gInv x)
    (hinv : ∀ x, gInv x * g x = 1) (hdg : ∀ x κ, (dg x κ)ᵀ = dg x κ) :
    ∀ x, IsMetricCompatible (christoffelFromMetric (gInv x) (dg x)) (dg x) (g x) := by
  intro x
  exact christoffelFromMetric_isMetricCompatible (dg x) (hg x) (hgi x) (hinv x) (hdg x)

end Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric

end
