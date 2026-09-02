/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame
public import Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks

/-!
# The tetrahedral null tetrad on the Riemann / celestial / Bloch sphere

`RiemannSphereBlochSL2CLinks.stereoInv_isBlochSphere` proves the `AdS₃` boundary, the Riemann sphere `CP¹`,
the celestial sphere, and the single-qubit Bloch sphere are **the same `S²`**. This file places the four
directions of `TetrahedralLorentzFrame` — the null tetrad / qubit SIC frame — literally *on* that sphere, with
their complex Riemann coordinates and the `SL(2,ℂ)` Möbius action.

* **§A — the four directions are on the sphere.** `tetraBloch i = vᵢ/√3` (the normalized `TetrahedralLorentzFrame.tetraVec`);
  `tetraBloch_mem_sphere` (`‖vᵢ/√3‖² = 1`, `BlochSphere (tetraBloch i)`): the four tetrahedral SIC directions
  are four points of the Riemann / celestial / Bloch sphere.
* **§B — their Riemann coordinates.** `tetraBoundary i = π(tetraBloch i)` (stereographic projection to `ℂ`);
  **`tetraBloch_eq_boundary`** (`π⁻¹(π(vᵢ/√3)) = vᵢ/√3 = blochVectorOfBoundary(tetraBoundary i)`): each
  tetrahedral point *is* the Riemann-sphere boundary point of its complex coordinate — using the genuine
  bijection `StereographicRiemannSphere.stereoInv_stereoProj` (`Z = ±1/√3 ≠ 1`, off the north pole).
* **§C — the `SL(2,ℂ)` Möbius action.** **`tetraBoundary_sl2c_mobius`**: the Lorentz double cover `SL(2,ℂ)`
  acts on the tetrahedral boundary coordinates by Möbius transformations
  (`RiemannSphereBlochSL2CLinks.sl2c_onePoint_mobius`). The finite tetrahedral subgroup
  `2T ⊂ SU(2) ⊂ SL(2,ℂ)` (`TetrahedralLorentzFrame.binaryTetraCoordinates`) is the Möbius group permuting the
  four points — the classic tetrahedron-on-the-Riemann-sphere, the local-Lorentz `SO(1,3)` rotation of the
  null tetrad realized as boundary conformal transformations.

**Honest layering.** Exact: the sphere membership of the four normalized tetrahedral directions, their
identification with the Riemann-sphere boundary points of their stereographic coordinates (via the
`stereoInv_stereoProj` bijection), and the `SL(2,ℂ)` Möbius action on those coordinates (via
`sl2c_onePoint_mobius`). Interpretive (docstring): the identification of the four points with a regular
tetrahedron and of `2T` with its Möbius symmetry group.

## References

* Riemann/celestial/Bloch sphere identity (`RiemannSphereBlochSL2CLinks.stereoInv_isBlochSphere`);
  stereographic bijection (`StereographicRiemannSphere.stereoInv_stereoProj`); `SL(2,ℂ)` Möbius action
  (`sl2c_onePoint_mobius`). Places `TetrahedralLorentzFrame` (`tetraVec`, `binaryTetraCoordinates`,
  `tetra_sic_overlap`) on the boundary sphere.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.Mathematics.Geometry.StereographicRiemannSphere
open Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
open scoped MatrixGroups

noncomputable section

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TetrahedralCelestialSphere


/-- The `i`-th **normalized tetrahedral direction** `vᵢ/√3` as a `BlochVector` (a unit vector, a point of the
Riemann / celestial / Bloch sphere). -/
def tetraBloch (i : Fin 4) : BlochVector := fun a => tetraVec i a / Real.sqrt 3

/-- **The four tetrahedral SIC directions are on the sphere** `‖vᵢ/√3‖² = 1`: they are four points of the
Riemann / celestial / Bloch `S²` (`RiemannSphereBlochSL2CLinks.stereoInv_isBlochSphere`). -/
lemma tetraBloch_mem_sphere (i : Fin 4) : BlochSphere (tetraBloch i) := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [BlochSphere, tetraBloch, div_pow, h3]
  fin_cases i <;> simp only [tetraVec] <;> norm_num

/-- The `Z`-coordinate `±1/√3` is off the north pole `Z = 1`. -/
lemma tetraBloch_Z_ne_one (i : Fin 4) : tetraBloch i 2 ≠ 1 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  intro h
  have hsq : (tetraBloch i 2) ^ 2 = 1 / 3 := by
    simp only [tetraBloch, div_pow, h3]; fin_cases i <;> simp only [tetraVec] <;> norm_num
  rw [h] at hsq; norm_num at hsq


/-- The **complex Riemann-sphere coordinate** of the `i`-th tetrahedral direction, `π(vᵢ/√3) ∈ ℂ`. -/
def tetraBoundary (i : Fin 4) : ℂ :=
  stereoProj (tetraBloch i 0) (tetraBloch i 1) (tetraBloch i 2)

/-- **Each tetrahedral point is the Riemann-sphere boundary point of its coordinate**
`blochVectorOfBoundary (π(vᵢ/√3)) = vᵢ/√3`: the four SIC directions are genuinely on the Riemann sphere, via
the `stereoInv_stereoProj` bijection (they lie off the north pole, `Z = ±1/√3 ≠ 1`). -/
lemma tetraBloch_eq_boundary (i : Fin 4) :
    blochVectorOfBoundary (tetraBoundary i) = tetraBloch i := by
  have hsph : (tetraBloch i 0) ^ 2 + (tetraBloch i 1) ^ 2 + (tetraBloch i 2) ^ 2 = 1 :=
    tetraBloch_mem_sphere i
  simp only [tetraBoundary, blochVectorOfBoundary,
    stereoInv_stereoProj _ _ _ hsph (tetraBloch_Z_ne_one i)]
  funext a; fin_cases a <;> rfl


/-- **`SL(2,ℂ)` acts on the tetrahedral boundary coordinates by Möbius transformations**
`M • zᵢ = (M₀₀ zᵢ + M₀₁)/(M₁₀ zᵢ + M₁₁)`: the Lorentz double cover rotates the four null directions of the
tetrahedron by boundary conformal (Möbius) maps (`RiemannSphereBlochSL2CLinks.sl2c_onePoint_mobius`). The finite
tetrahedral subgroup `2T ⊂ SU(2) ⊂ SL(2,ℂ)` (`TetrahedralLorentzFrame.binaryTetraCoordinates`) is the Möbius
symmetry group of this four-point configuration on the Riemann sphere. -/
lemma tetraBoundary_sl2c_mobius (M : SL(2, ℂ)) (i : Fin 4)
    (hk : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * tetraBoundary i +
        (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    M.toGL • (tetraBoundary i : OnePoint ℂ)
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * tetraBoundary i +
            (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) /
          ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * tetraBoundary i +
            (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℂ) : OnePoint ℂ) :=
  sl2c_onePoint_mobius M (tetraBoundary i) hk

end Physlib.QuantumMechanics.ComplexAction.TetrahedralCelestialSphere
