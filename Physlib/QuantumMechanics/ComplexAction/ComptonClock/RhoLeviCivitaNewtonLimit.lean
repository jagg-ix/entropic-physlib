/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Algebra.AlmostCommutativeLeviCivita
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI

/-!
# From the almost-commutative Levi-Civita connection to Newton and standard General Relativity

The almost-commutative (`ρ`) Levi-Civita connection of `Mathematics.Algebra.AlmostCommutativeLeviCivita`
(Ngakeu 2007) contains ordinary Riemannian geometry as its `ρ ≡ 1` (commutative) limit: Ngakeu's own remark
that "the classical case is recovered for `G = {e}` and `ρ = 1`". This module makes that convergence explicit
and chains it to the concrete Newtonian / standard-GR limit already established in `NewtonianLimitCurvatureAPI`.

* **§A — the `ρ ≡ 1` reduction.** At the trivial commutation factor the `ρ`-curvature, torsion-free and
  metric-compatibility conditions, and the symmetrized Ricci tensor collapse to their ordinary Riemannian
  forms (`rhoCurvature_trivialFactor`, `isRhoTorsionFree_trivialFactor_iff`, `isRhoCompatible_trivialFactor_iff`,
  `symmetrizedRicci_trivialFactor_symm`).
* **§B — convergence to Newton and standard GR.** `almostCommutative_to_newton` bundles the endpoints already
  proved for the concrete weak-field metric: the metric's Levi-Civita connection
  (`weakFieldLeviCivita2 = christoffelFromMetric`), its Ricci curvature `R₀₀ = ∇²Φ/c²` (up to an explicit
  `O(c⁻⁴)` correction), and the geodesic acceleration `ẍ = −∇Φ` — the standard-GR structures whose weak-field
  limit is Newton's gravity (`∇²Φ = 4πGρ` via `NewtonianAndGRLimit.weakField_einstein_poisson`).

**Honest layering.** §A are exact `ρ ≡ 1` reductions of the abstract framework. §B re-bundles the exact
concrete-geometry results of `NewtonianLimitCurvatureAPI` / `NewtonianAndGRLimit`; the identification of the
abstract `ρ`-Levi-Civita connection with the concrete `christoffelFromMetric` is the classical-limit content,
established via the shared `Curvature.LeviCivitaFromMetric` connection.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.RhoLeviCivitaNewtonLimit

open Physlib.Mathematics.Algebra.AlmostCommutative
open Physlib.Mathematics.Algebra.AlmostCommutativeLeviCivita
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Matrix


variable {G : Type*} [AddCommGroup G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {D : Type*} [AddCommGroup D] [Module k D]

@[simp] lemma trivialFactor_factor (a b : G) : (trivialFactor G k).factor a b = (1 : k) := rfl

/-- **[`ρ ≡ 1` curvature] `R(X,Y)Z = ∇_X∇_YZ − ∇_Y∇_XZ − ∇_{[X,Y]}Z`** — at the trivial factor the
`ρ`-curvature is the ordinary Riemann curvature operator. -/
lemma rhoCurvature_trivialFactor (deg : D → G) (br nabla : D → D → D) (X Y Z : D) :
    rhoCurvature (trivialFactor G k) deg br nabla X Y Z
      = nabla X (nabla Y Z) - nabla Y (nabla X Z) - nabla (br X Y) Z := by
  simp [rhoCurvature]

/-- **[`ρ ≡ 1` torsion-free] `[V,W] = ∇_VW − ∇_WV`** — the ordinary torsion-free condition. -/
lemma isRhoTorsionFree_trivialFactor_iff (deg : D → G) (br nabla : D → D → D) :
    IsRhoTorsionFree (trivialFactor G k) deg br nabla ↔ ∀ V W, br V W = nabla V W - nabla W V := by
  simp [IsRhoTorsionFree]

omit [AddCommGroup D] [Module k D] in
/-- **[`ρ ≡ 1` metric compatibility] `X·⟨V,W⟩ = ⟨∇_XV,W⟩ + ⟨V,∇_XW⟩`** — the ordinary metric-compatibility. -/
lemma isRhoCompatible_trivialFactor_iff (deg : D → G) (act : D → A → A) (g : D → D → A)
    (nabla : D → D → D) :
    IsRhoCompatible (trivialFactor G k) deg act g nabla
      ↔ ∀ X V W, act X (g V W) = g (nabla X V) W + g V (nabla X W) := by
  simp [IsRhoCompatible]

omit [AddCommGroup D] [Module k D] in
/-- **[`ρ ≡ 1` Ricci is symmetric] `Ricci(U,V) = Ricci(V,U)`** — the ordinary symmetric Ricci tensor. -/
lemma symmetrizedRicci_trivialFactor_symm (deg : D → G) (trR : D → D → A) (U V : D) :
    symmetrizedRicci (trivialFactor G k) deg trR U V = symmetrizedRicci (trivialFactor G k) deg trR V U := by
  rw [symmetrizedRicci_rho_symm (trivialFactor G k) deg trR U V, trivialFactor_factor, one_smul]


/-- **[The classical (`ρ ≡ 1`) Levi-Civita connection converges to Newton and standard GR]** for the weak-field
metric, its Levi-Civita connection *is* the metric's connection (`weakFieldLeviCivita2 = christoffelFromMetric`,
metric-compatible and torsion-free), its Ricci curvature is `R₀₀ = ∇²Φ/c²` up to an explicit `O(c⁻⁴)`
correction, and the geodesic acceleration is Newton's gravity `ẍ = −∇Φ`. Together with
`NewtonianAndGRLimit.weakField_einstein_poisson` (`∇²Φ = 4πGρ`) this is the full Newtonian / standard-GR limit
of the almost-commutative Levi-Civita connection at `ρ ≡ 1`. -/
lemma almostCommutative_to_newton (A dΦ d2Φ c : ℝ) (hA : A ≠ 0) (hc : c ≠ 0) :
    weakFieldLeviCivita2 A (2 * dΦ / c ^ 2)
        = christoffelFromMetric (weakFieldMetric2Inv A) (weakFieldMetricDeriv2 (2 * dΦ / c ^ 2))
      ∧ ricciFromConnection (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2))
          (weakFieldConnDeriv2 A (2 * dΦ / c ^ 2) (2 * d2Φ / c ^ 2)) 0 0
          = weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A)
      ∧ geodesicAcceleration (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2)) ![c, 0] 1 = -dΦ :=
  ⟨weakFieldLeviCivita2_eq_christoffelFromMetric A (2 * dΦ / c ^ 2) hA,
    weakField_ricci00_from_connection_newtonian A dΦ d2Φ c hA hc,
    weakField_geodesic_x_eq_newton A dΦ c hc⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.RhoLeviCivitaNewtonLimit

end
