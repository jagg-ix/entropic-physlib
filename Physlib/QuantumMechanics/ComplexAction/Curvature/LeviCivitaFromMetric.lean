/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian

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

All exact. The metric enters through `g` (symmetric), its inverse `gInv` (`gInv·g = 1`,
symmetric) and its partial derivatives `dg` (each symmetric) — the standard hypotheses used throughout
`Curvature`. No coordinate calculus is invoked: `dg κ = ∂_κ g` is supplied as the metric's derivative data.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric

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
theorem christoffelFromMetric_isTorsionFree (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ)
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
theorem christoffel_contraction [DecidableEq ι] {g gInv : Matrix ι ι ℝ} (dg : ι → Matrix ι ι ℝ)
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
theorem christoffelFromMetric_isMetricCompatible [DecidableEq ι] {g gInv : Matrix ι ι ℝ}
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
theorem christoffelFromMetric_isLeviCivita4
    {g gInv : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ} (dg : Fin 1 ⊕ Fin 3 → Matrix _ _ ℝ)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) (hdg : ∀ κ, (dg κ)ᵀ = dg κ) :
    IsTorsionFree (christoffelFromMetric gInv dg)
      ∧ IsMetricCompatible (christoffelFromMetric gInv dg) dg g :=
  ⟨christoffelFromMetric_isTorsionFree gInv dg hdg,
    christoffelFromMetric_isMetricCompatible dg hg hgi hinv hdg⟩

end Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric

end
