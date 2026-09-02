/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyEulerGaussBonnet
public import Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks

/-!
# The general `d`-dimensional Regge action on its holographic boundary (Ambjørn–Savvidy ↔ AdS/CFT)

The Ambjørn–Savvidy **general `d`-dimensional Regge / Hilbert–Einstein action**
`reggeEinsteinHilbert σ ω s = Σ σ·ω` (`AmbjornSavvidyEulerGaussBonnet.generalDim_hilbertEinstein_eq_regge`,
hep-th/9606140 Eq. 91) is the *bulk* gravitational action of a triangulated `d`-manifold. This module places that
bulk action on the **holographic boundary** already built in `RiemannSphereBlochSL2CLinks`:

* the **co-dimension-one reduction** is the dimensional-scaling transition
  `dimensional_scaling_2_to_3_length` (`dimLength a 3 = scalingTransition 2 3 (dimLength a 2)`, unchanged);
* the **boundary** is the Riemann sphere `S² ∖ {N} ≃ ℂ` via `stereoInv_stereoProj`;
* the **boundary conformal group** is `SL(2,ℂ)` acting by Möbius transformations (`sl2c_onePoint_mobius`),
  unimodular (`sl2c_matrix_unimodular`) and homomorphic to the `AdS₃` isometry / Lorentz group
  (`sl2c_toLorentzGroup_hom`).

* **§A — the Regge action reduces holographically.** **`reggeAction_holographic_reduction`** — replacing every
  edge's *bulk* holographic length `dimLength a 3` by its *boundary* image `scalingTransition 2 3 (dimLength a 2)`
  leaves the whole Regge sum `Σ σ·ω` intact, term by term (the co-dimension-one reduction inside the action).
* **§B — the holographic-boundary assembly.** **`ambjornSavvidy_holographic_boundary`** — one statement bundling
  the reduction with the boundary geometry: the reduced Regge action `= Σ (boundary length)·ω`, the boundary point
  lies on the Riemann sphere `S² ≃ ℂ`, the boundary conformal group is unimodular `SL(2,ℂ)`, and its
  composition law is the `AdS₃` Lorentz homomorphism.
* **§C — the boundary conformal (Möbius) action.** **`holographicReggeBoundary_mobius`** — the explicit Möbius
  transformation `M • k = (M₀₀k + M₀₁)/(M₁₀k + M₁₁)` by which `SL(2,ℂ)` acts on the boundary the reduced Regge
  action lives on.

**Honest layering.** §A is an exact `Finset.sum` identity built on the existing `dimensional_scaling_2_to_3_length`
dimensional-scaling theorem (reused, unchanged). §B/§C **reuse** `stereoInv_stereoProj`,
`sl2c_matrix_unimodular`, `sl2c_toLorentzGroup_hom` and `sl2c_onePoint_mobius` verbatim. The *physical*
AdS/CFT holographic correspondence — that a `d`-dimensional bulk gravity action is dual to a `(d−1)`-dimensional
boundary conformal field theory — is recorded through this reuse, not re-derived: what is proved here is the exact
dimensional-scaling reduction of the Regge action and the concrete Riemann-sphere / `SL(2,ℂ)` boundary geometry it
lands on.

## References

* J. Ambjørn, G. K. Savvidy, hep-th/9606140, Eq. 91 (general `d`-dimensional Regge action). Links
  `AmbjornSavvidyEulerGaussBonnet` to `RiemannSphereBlochSL2CLinks`
  (`dimensional_scaling_2_to_3_length`, `sl2c_onePoint_mobius`) and
  `Mathematics.Geometry.StereographicRiemannSphere` (`stereoInv_stereoProj`).


-/

set_option autoImplicit false

open scoped Real BigOperators MatrixGroups
open Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl
open Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
open Physlib.Mathematics.DimensionalScaling
open Physlib.Mathematics.Geometry.StereographicRiemannSphere

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyHolographicBoundary


/-- **The general `d`-dimensional Regge action reduces holographically, edge by edge.** With every edge carrying
the *bulk* holographic length `dimLength a 3` (`AdS₃`, `D = 3`), the Regge / Hilbert–Einstein action
`Σ (dimLength a 3)·ω` equals the same sum with the *boundary* image length `scalingTransition 2 3 (dimLength a 2)`
(`CFT₂`, `D = 2`) — the co-dimension-one holographic reduction `dimensional_scaling_2_to_3_length` applied inside
the Ambjørn–Savvidy action `reggeEinsteinHilbert = Σ σ·ω`. -/
lemma reggeAction_holographic_reduction {ι : Type*} (ω : ι → ℝ) (s : Finset ι) (a : ℝ) :
    reggeEinsteinHilbert (fun _ => dimLength a 3) ω s
      = reggeEinsteinHilbert (fun _ => scalingTransition 2 3 (dimLength a 2)) ω s := by
  simp only [reggeEinsteinHilbert, dimensional_scaling_2_to_3_length]


/-- **The Ambjørn–Savvidy Regge action on its holographic boundary.** One statement bundling the full chain: the
bulk Regge action `Σ (dimLength a 3)·ω` **reduces** (co-dimension one) to the boundary form
`Σ (scalingTransition 2 3 (dimLength a 2))·ω`; the boundary is the **Riemann sphere** `S² ∖ {N} ≃ ℂ`
(`stereoInv (stereoProj X Y Z) = (X,Y,Z)`); the boundary conformal group is **unimodular** `SL(2,ℂ)`
(`ad − bc = 1`); and its composition law is the `AdS₃` **Lorentz homomorphism** `Λ(MN) = Λ(M)Λ(N)`. -/
lemma ambjornSavvidy_holographic_boundary {ι : Type*} (ω : ι → ℝ) (s : Finset ι) (a : ℝ)
    (X Y Z : ℝ) (hsph : X ^ 2 + Y ^ 2 + Z ^ 2 = 1) (hN : Z ≠ 1) (M N : SL(2, ℂ)) :
    reggeEinsteinHilbert (fun _ => dimLength a 3) ω s
        = reggeEinsteinHilbert (fun _ => scalingTransition 2 3 (dimLength a 2)) ω s
      ∧ stereoInv (stereoProj X Y Z) = (X, Y, Z)
      ∧ (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1
          - (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1
      ∧ Lorentz.SL2C.toLorentzGroup (M * N)
          = Lorentz.SL2C.toLorentzGroup M * Lorentz.SL2C.toLorentzGroup N :=
  ⟨reggeAction_holographic_reduction ω s a, stereoInv_stereoProj X Y Z hsph hN,
    sl2c_matrix_unimodular M, sl2c_toLorentzGroup_hom M N⟩


/-- **`SL(2,ℂ)` acts on the holographic Regge boundary by Möbius transformations**
`M • k = (M₀₀k + M₀₁)/(M₁₀k + M₁₁)` — the explicit conformal action (`sl2c_onePoint_mobius`) of the boundary
group on the Riemann sphere `OnePoint ℂ` that the holographically reduced Ambjørn–Savvidy Regge action lives on. -/
lemma holographicReggeBoundary_mobius (M : SL(2, ℂ)) (k : ℂ)
    (hk : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    M.toGL • (k : OnePoint ℂ)
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) /
          ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * k + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℂ)
          : OnePoint ℂ) :=
  sl2c_onePoint_mobius M k hk

end Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidyHolographicBoundary
