/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.AdS3ConformalBoundary
public import Physlib.Mathematics.DimensionalScalingFunctorTower
public import Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
public import Physlib.Relativity.SL2C.Basic

/-!
# Linking the `AdS₃` conformal boundary and dimensional scaling to the rest of the repo

Three bridges tying `AdSCFT.AdS3ConformalBoundary`, `Mathematics.Geometry.StereographicRiemannSphere`,
and `Mathematics.DimensionalScalingFunctorTower` to existing repo content.

* **§A — the Riemann-sphere boundary is the qubit Bloch sphere.** The stereographic image of a complex
 boundary coordinate is a Bloch vector on the `LorenzQubitBlochDynamics.BlochSphere`
 (`boundary_isBlochSphere`): the `AdS₃` conformal boundary `= CP¹ = ` Riemann sphere `= ` the single-
 qubit Bloch sphere `= S²` — one and the same `2`-sphere.
* **§B — the boundary conformal group is the Lorentz double cover.** The unimodular Möbius group of the
 boundary is `SL(2,ℂ)` (`boundary_sl2c_unimodular`), the domain of PhysLean's spinor double cover
 `SL2C.toLorentzGroup : SL(2,ℂ) →* LorentzGroup 3`; that cover is a homomorphism, so composing
 boundary conformal maps corresponds to composing Lorentz transformations
 (`boundary_conformal_lorentz_hom`); and `SL(2,ℂ)` genuinely *acts* on the boundary by Möbius maps
 `M • z = (M₀₀ z + M₀₁)/(M₁₀ z + M₁₁)` (`boundary_sl2c_mobius`). This is the `AdS₃` isometry
 `= CFT₂` conformal `= ` Lorentz identification.
* **§C — dimensional scaling realizes the holographic reduction.** The holographic principle is
 co-dimension one (`AdS₃` bulk `D = 3` → `CFT₂` boundary `D = 2`); the cross-dimensional step of
 `DimensionalScaling` relates the bulk and boundary lengths, `L₃ = L₂·√(3/2)`
 (`holographic_bulk_boundary_length`).

Proven: the boundary point is a Bloch-sphere vector; the boundary Möbius
coefficients are unimodular; the double cover is multiplicative; the bulk/boundary length relation.
Interpretive: that these three `2`-spheres (boundary, Riemann, Bloch) are the *same* sphere, that
`SL(2,ℂ)` is the *full* boundary conformal group, and the holographic reading of the co-dimension-one
step, are the standard dictionary.

No new axioms.
-/

set_option autoImplicit false

open Physlib.Mathematics.Geometry.StereographicRiemannSphere
open Physlib.Mathematics.DimensionalScaling
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open scoped MatrixGroups

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalBoundaryRepoLinks

/-! ## §A — the Riemann-sphere boundary is the qubit Bloch sphere -/

/-- **The boundary point of a complex coordinate, as a Bloch vector**: the stereographic image
`π⁻¹(w) ∈ S²` read as a `LorenzQubitBlochDynamics.BlochVector`. -/
noncomputable def blochVectorOfBoundary (w : ℂ) : BlochVector :=
  ![(stereoInv w).1, (stereoInv w).2.1, (stereoInv w).2.2]

/-- **The conformal boundary is the Bloch sphere** `π⁻¹(w) ∈ BlochSphere`: every complex boundary
coordinate maps to a point of the qubit Bloch sphere — the `AdS₃` boundary, the Riemann sphere `CP¹`,
and the single-qubit Bloch sphere are the same `S²`. -/
theorem boundary_isBlochSphere (w : ℂ) : BlochSphere (blochVectorOfBoundary w) := by
  show (stereoInv w).1 ^ 2 + (stereoInv w).2.1 ^ 2 + (stereoInv w).2.2 ^ 2 = 1
  exact stereoInv_mem_sphere w

/-! ## §B — the boundary conformal group is the Lorentz double cover `SL(2,ℂ)` -/

/-- **The boundary Möbius coefficients are unimodular** `ad − bc = 1` for `M ∈ SL(2,ℂ)`: the boundary
conformal transformations form `SL(2,ℂ)` (equivalently `PSL(2,ℂ)`), the domain of the spinor double
cover `SL2C.toLorentzGroup`. -/
theorem boundary_sl2c_unimodular (M : SL(2, ℂ)) :
    (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      - (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
  have h := M.2
  rwa [Matrix.det_fin_two] at h

/-- **The boundary conformal ↔ Lorentz correspondence is a homomorphism**
`Λ(M·N) = Λ(M)·Λ(N)`: composing two boundary Möbius transformations corresponds to composing their
Lorentz images under `SL2C.toLorentzGroup` — the boundary `CFT₂` conformal group is the `AdS₃` isometry
(Lorentz) group. -/
theorem boundary_conformal_lorentz_hom (M N : SL(2, ℂ)) :
    Lorentz.SL2C.toLorentzGroup (M * N)
      = Lorentz.SL2C.toLorentzGroup M * Lorentz.SL2C.toLorentzGroup N :=
  map_mul _ M N

/-- **`SL(2,ℂ)` acts on the boundary by Möbius transformations** `M • z = (M₀₀ z + M₀₁)/(M₁₀ z + M₁₁)`:
the Lorentz double-cover group `SL(2,ℂ)` — the domain of `SL2C.toLorentzGroup` — acts on the boundary
Riemann sphere `OnePoint ℂ` by the boundary conformal (Möbius) transformations of
`AdS3ConformalBoundary.boundary_mobius_action`. So the boundary conformal group *is* `SL(2,ℂ)` acting. -/
theorem boundary_sl2c_mobius (M : SL(2, ℂ)) (k : ℂ)
    (hk : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    M.toGL • (k : OnePoint ℂ)
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) /
          ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℂ)
          : OnePoint ℂ) :=
  AdS3ConformalBoundary.boundary_mobius_action M.toGL k hk

/-! ## §C — dimensional scaling realizes the holographic reduction -/

/-- **The holographic bulk ↔ boundary length relation** `L₃ = T_{2→3}(L₂)`: the `AdS₃` bulk (`D = 3`)
and its `CFT₂` boundary (`D = 2`) differ by one dimension, and the cross-dimensional transition of
`DimensionalScaling` includes the boundary length to the bulk length — the holographic co-dimension-one
reduction as a dimensional-scaling transition. -/
theorem holographic_bulk_boundary_length (a : ℝ) :
    dimLength a 3 = scalingTransition 2 3 (dimLength a 2) :=
  (scalingTransition_dimLength a (by norm_num) 3).symm

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalBoundaryRepoLinks
