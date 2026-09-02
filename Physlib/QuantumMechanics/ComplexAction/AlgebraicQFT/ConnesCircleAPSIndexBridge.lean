/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry
meta import Zil

/-!
# Continuum circle APS/index bridge

This thin adapter connects the continuum circle formalization to the repository's common
Connes--Atiyah--Singer carrier.  It reuses, rather than restates, the proved self-adjoint/Fredholm
circle Dirac, the sharp `s > 1/2` Sobolev trace and closed APS domain, the exact heat identity, and
the meromorphic dimension-spectrum pole.

The odd-dimensional ungraded circle Dirac has index zero.  Its zero top-degree index density is a
concrete instance of the repository carrier, not a proof of the general characteristic-form
Atiyah--Singer or APS boundary-index theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge

open Filter MeasureTheory Topology
open ConnesCircleSpectralGeometry
open ConnesAtiyahSingerKasparov

/-- The continuum circle Dirac packaged in the repository's common Atiyah--Singer index carrier.
The analytic index is the previously computed Fredholm index; the odd-dimensional top-degree
Chern-character component is zero. -/
def circleAtiyahSingerIndexData :
    AtiyahSingerIndexData PUnit.{1} circleDirac.domain (L2Sequence ℤ) where
  diracPlus := circleDirac.toFun
  ahatDensity := fun _ => 1
  chernCharacterDensity := fun _ => 0
  volume := 0
  density_integrable := by simp
  index_formula := by
    rw [circleDirac_index_eq_zero]
    simp

/-- The packaged analytic index is the genuine continuum Fredholm index and equals zero. -/
theorem circleAtiyahSingerIndexData_analyticIndex_eq_zero :
    analyticIndex circleAtiyahSingerIndexData.diracPlus = 0 := by
  simpa [circleAtiyahSingerIndexData, analyticIndex] using circleDirac_index_eq_zero

/-- The displayed topological-density side of the odd circle package is also zero. -/
theorem circleAtiyahSingerIndexData_topologicalIndex_eq_zero :
    (∫ x : PUnit.{1}, circleAtiyahSingerIndexData.ahatDensity x *
      circleAtiyahSingerIndexData.chernCharacterDensity x
      ∂circleAtiyahSingerIndexData.volume) = 0 := by
  simp [circleAtiyahSingerIndexData]

/-- The circle package is consumed by the repository's generic Atiyah--Singer certificate API:
its analytic Fredholm index equals its displayed topological-density integral. -/
theorem circleAtiyahSingerIndexData_index_formula :
    (analyticIndex circleAtiyahSingerIndexData.diracPlus : ℝ) =
      ∫ x : PUnit.{1}, circleAtiyahSingerIndexData.ahatDensity x *
        circleAtiyahSingerIndexData.chernCharacterDensity x
        ∂circleAtiyahSingerIndexData.volume :=
  circleAtiyahSingerIndexData.index_formula

/-- The critical continuum noncommutative-geometric spine on the circle, assembled without new
analytic assumptions: the Dirac operator is closed Fredholm with index zero; every sharp normal
Sobolev trace above `s = 1/2` is split-surjective and induces a closed APS domain; the heat trace has
the exact Poisson transformation; and the dimension zeta has its genuine pole at dimension one. -/
theorem circleContinuumIndexAPSHeatZeta_spine :
    ClosedFredholm circleDirac ∧
      analyticIndex circleDirac.toFun = 0 ∧
      (∀ (s : ℝ) (hs : (1 / 2 : ℝ) < s),
        (circleCylinderSobolevTraceAt s hs).comp circleCylinderConstantExtension =
            ContinuousLinearMap.id ℂ (L2Sequence ℤ) ∧
          Function.Surjective (circleCylinderSobolevTraceAt s hs) ∧
          IsClosed (circleCylinderAPSBoundaryConditionAt s hs : Set CircleCylinderH1)) ∧
      (∀ t : ℝ, 0 < t →
        circleHeatTrace t = Real.sqrt (Real.pi / t) *
          circleHeatTrace (Real.pi ^ 2 / t)) ∧
      Tendsto (fun s : ℂ => (s - 1) * circleDimensionZeta s)
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) (nhds (2 : ℂ)) := by
  refine ⟨circleDirac_closedFredholm, circleDirac_index_eq_zero, ?_, ?_,
    circleDimensionZeta_residue_one⟩
  · intro s hs
    exact ⟨circleCylinderSobolevTraceAt_comp_extension s hs,
      circleCylinderSobolevTraceAt_surjective s hs,
      circleCylinderAPSBoundaryConditionAt_isClosed s hs⟩
  · intro t ht
    exact circleHeatTrace_poisson t ht

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge.circleAtiyahSingerIndexData_analyticIndex_eq_zero where
  formalizes @ "claim:the-continuum-circle-dirac-instantiates-the-common-atiyah-singer-carrier-and-has-analytic-index-zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_index_eq_zero",
  caveat @ "epistemic:exact-odd-circle-fredholm-index-instance-with-zero-top-degree-density-not-the-general-atiyah-singer-or-aps-characteristic-form-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge.circleAtiyahSingerIndexData_index_formula where
  formalizes @ "claim:the-concrete-continuum-circle-package-is-consumed-by-the-repository-generic-atiyah-singer-index-formula-api",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.AtiyahSingerIndexData.analyticIndex_eq_topologicalIndex",
  caveat @ "epistemic:certificate-instantiation-for-the-flat-odd-circle-not-a-derivation-of-the-general-local-index-density"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge.circleContinuumIndexAPSHeatZeta_spine where
  formalizes @ "claim:one-public-continuum-circle-spine-combines-fredholm-index-sharp-sobolev-trace-closed-aps-domain-heat-poisson-identity-and-dimension-zeta-pole",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_closedFredholm",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTraceAt_comp_extension",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderAPSBoundaryConditionAt_isClosed",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleHeatTrace_poisson",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDimensionZeta_residue_one",
  caveat @ "claim:continuum-flat-circle-capstone-not-the-global-curved-manifold-aps-index-formula-elliptic-regularity-or-characteristic-form-transgression"

zil_file_contract physlib.connesCircleAPSIndexBridge where
  promises "A thin, dependency-reusing bridge from the continuum circle Dirac and sharp Sobolev/APS boundary construction to the repository's common Connes--Atiyah--Singer index carrier, plus one public theorem exposing the Fredholm-index, trace, APS-domain, heat-kernel and dimension-spectrum chain."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_closedFredholm",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_index_eq_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTraceAt_comp_extension",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTraceAt_surjective",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderAPSBoundaryConditionAt_isClosed",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleHeatTrace_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDimensionZeta_residue_one",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov.AtiyahSingerIndexData"]
  forbids_substitutes ["a finite-mode circle truncation relabelled as a continuum APS theorem",
    "an assertion of the arbitrary-manifold Atiyah--Singer or APS characteristic-form formula"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge.circleAtiyahSingerIndexData_analyticIndex_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge.circleAtiyahSingerIndexData_topologicalIndex_eq_zero,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge.circleAtiyahSingerIndexData_index_formula,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge.circleContinuumIndexAPSHeatZeta_spine]

/- ZIL-END -/
