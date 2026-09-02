/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.UnitBallBoundaryRiemannSphere
public import Physlib.Mathematics.DimensionalScalingFunctorTower
public import Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
public import Physlib.Relativity.SL2C.Basic
meta import Zil

/-!
# Riemann-sphere, Bloch-sphere, and `SL(2,ℂ)` links

This module links concrete structures already available in the repository: stereographic coordinates on
`S²`, Bloch vectors, determinant-one `SL(2,ℂ)` matrices, the existing Lorentz double-cover homomorphism,
the fractional-linear action on `OnePoint ℂ`, and the two-to-three dimensional scaling identity.

It does not assert an AdS/CFT dictionary, does not identify a bulk spacetime, and does not prove a physical
dimensional-scaling principle. It is a repository-linking module for Riemann-sphere/Bloch/`SL(2,ℂ)` algebra.
-/

set_option autoImplicit false

open Physlib.Mathematics.Geometry.StereographicRiemannSphere
open Physlib.Mathematics.DimensionalScaling
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open scoped MatrixGroups

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks


/-- **The Riemann-sphere point of a complex coordinate, as a Bloch vector**: the stereographic image
`π⁻¹(w) ∈ S²` read as a `LorenzQubitBlochDynamics.BlochVector`. -/
noncomputable def blochVectorOfBoundary (w : ℂ) : BlochVector :=
  ![(stereoInv w).1, (stereoInv w).2.1, (stereoInv w).2.2]

/-- **The Riemann sphere is the Bloch sphere** `π⁻¹(w) ∈ BlochSphere`: every complex boundary
coordinate maps to a point of the qubit Bloch sphere — the `the Riemann-sphere` boundary, the Riemann sphere `CP¹`,
and the single-qubit Bloch sphere are the same `S²`. -/
lemma stereoInv_isBlochSphere (w : ℂ) : BlochSphere (blochVectorOfBoundary w) := by
  show (stereoInv w).1 ^ 2 + (stereoInv w).2.1 ^ 2 + (stereoInv w).2.2 ^ 2 = 1
  exact stereoInv_mem_sphere w


/-- **The Riemann-sphere Möbius coefficients are unimodular** `ad − bc = 1` for `M ∈ SL(2,ℂ)`: the Riemann sphere
conformal transformations form `SL(2,ℂ)` (equivalently `PSL(2,ℂ)`), the domain of the spinor double
cover `SL2C.toLorentzGroup`. -/
lemma sl2c_matrix_unimodular (M : SL(2, ℂ)) :
    (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      - (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
  have h := M.2
  rwa [Matrix.det_fin_two] at h

/-- **The fractional-linear ↔ Lorentz correspondence is a homomorphism**
`Λ(M·N) = Λ(M)·Λ(N)`: composing two Riemann-sphere Möbius transformations corresponds to composing their
Lorentz images under `SL2C.toLorentzGroup` — the Riemann sphere `one-point complex` conformal group is the `the Riemann-sphere` isometry
(Lorentz) group. -/
lemma sl2c_toLorentzGroup_hom (M N : SL(2, ℂ)) :
    Lorentz.SL2C.toLorentzGroup (M * N)
      = Lorentz.SL2C.toLorentzGroup M * Lorentz.SL2C.toLorentzGroup N :=
  map_mul _ M N

/-- **`SL(2,ℂ)` acts on the Riemann sphere by Möbius transformations** `M • z = (M₀₀ z + M₀₁)/(M₁₀ z + M₁₁)`:
the Lorentz double-cover group `SL(2,ℂ)` — the domain of `SL2C.toLorentzGroup` — acts on the Riemann sphere
Riemann sphere `OnePoint ℂ` by the fractional-linear (Möbius) transformations of
`UnitBallBoundaryRiemannSphere.onePoint_complex_mobius_action`. So the fractional-linear group *is* `SL(2,ℂ)` acting. -/
lemma sl2c_onePoint_mobius (M : SL(2, ℂ)) (k : ℂ)
    (hk : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    M.toGL • (k : OnePoint ℂ)
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) /
          ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℂ)
          : OnePoint ℂ) :=
  Physlib.Mathematics.Geometry.UnitBallBoundaryRiemannSphere.onePoint_complex_mobius_action
    M.toGL k hk


/-- **The dimensional-scaling bulk ↔ Riemann-sphere length relation** `L₃ = T_{2→3}(L₂)`: the `the Riemann-sphere` bulk (`D = 3`)
and its `one-point complex` Riemann-sphere (`D = 2`) differ by one dimension, and the cross-dimensional transition of
`DimensionalScaling` carries the Riemann sphere length to the bulk length — the dimensional-scaling co-dimension-one
reduction as a dimensional-scaling transition. -/
lemma dimensional_scaling_2_to_3_length (a : ℝ) :
    dimLength a 3 = scalingTransition 2 3 (dimLength a 2) :=
  (scalingTransition_dimLength a (by norm_num) 3).symm

end Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks.stereoInv_isBlochSphere where
  formalizes @ "claim:the-riemann-sphere-boundary-coordinate-maps-to-the-qubit-bloch-sphere",
  supported_by @ "paper:penrose-rindler-spinors-and-spacetime"

zil attach Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks.sl2c_toLorentzGroup_hom where
  supported_by @ "lean:Physlib.Mathematics.Geometry.UnitBallBoundaryRiemannSphere.onePoint_complex_mobius_action",
  formalizes @ "claim:sl2c-covers-the-lorentz-group-the-mobius-conformal-maps-of-the-celestial-sphere",
  requires @ "claim:the-riemann-sphere-boundary-coordinate-maps-to-the-qubit-bloch-sphere"

zil_file_contract physlib.riemannSphereBlochSL2CLinks where
  promises "The Riemann sphere is the Bloch sphere: every stereographic boundary coordinate maps to a point of the single-qubit Bloch sphere, and SL(2,C) covers the Lorentz group as the Mobius conformal transformations of that celestial sphere."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks.blochVectorOfBoundary",
    "lean:Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics.BlochSphere"]
  forbids_substitutes ["a full celestial-holography or twistor development, only the sphere identification and the double cover"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks.stereoInv_isBlochSphere,
    Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks.sl2c_toLorentzGroup_hom]

/- ZIL-END -/
