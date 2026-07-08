/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

/-!
# The quaternion Hopf frame is a rigid orthonormal pair — the dual-sphere defect is `≡ 1`

Runs the quaternion Hopf map of `Hopf.QuaternionIsoclinicHopfFibration` through the **dual-sphere fiber
decomposition** of `Hopf.DualSphereFiberDecomposition` (`crossSphereDefect ξ η = |ξ×η|² = ‖ξ‖²‖η‖² − ⟨ξ,η⟩²`,
the cross-sphere alignment whose vanishing is the "2D collapse" `ξ ∥ η`).

Conjugation by a unit quaternion is the `SO(3)` rotation of the `SU(2) → SO(3)` double cover, so the two
Hopf direction-vectors built from the orthogonal imaginary units `i, j`,

 `ξ = Im(q·i·q̄)`, `η = Im(q·j·q̄)` (`frameVec q imagUnit`, `frameVec q jUnit`),

are *always orthogonal* (`frame_inner_zero`: `⟨ξ,η⟩ = 0` for **every** `q`, not just unit), each of squared
length `(normSq q)²` (`frame_imagUnit_normSq`, `frame_jUnit_normSq`). Hence the dual-sphere cross-alignment
is **maximal and rigid**:

 `crossSphereDefect ξ η = (normSq q)⁴` (`frame_crossSphereDefect`), `= 1` on `S³`
 (`hopf_frame_orthonormal`).

So `Hopf.DualSphereFiberDecomposition`'s 2D-collapse (`crossSphereDefect = 0`, `ξ ∥ η`) **never happens** for
the quaternion Hopf frame: the geometric and the second direction-sphere are perpeticular by construction —
the rigidity of the spinor → orthonormal-frame map (the `SO(3)` image of the double cover `hopf_neg`).

This is the concrete cross-check between the two Hopf realizations: the quaternion fibration
(`Hopf.QuaternionIsoclinicHopfFibration`) feeds direction vectors into the dual-sphere decomposition
(`Hopf.DualSphereFiberDecomposition`), and they agree — the cross-sphere alignment evaluates to the unit-sphere
value `1`, witnessing that `{q i q̄, q j q̄, q k q̄}` is an orthonormal frame. (Compare the ℂ²/Pauli
realization `Hopf.FibrationSpinorMap`, whose `S¹` fiber is the *left* global phase, dual to the *right*
coset fiber `hopf_fiber` here.)

Proven: `⟨ξ,η⟩ = 0` and `‖ξ‖² = ‖η‖² = (normSq q)²` as polynomial identities (so
`crossSphereDefect = (normSq q)⁴`), and `= 1` on the unit sphere, reusing the repo's `crossSphereDefect`,
`sphereInner`, `sphereNormSq`, `crossSphereDefect_unit`. The `SO(3)`/orthonormal-frame reading is the
geometric interpretation; the algebra is unconditional.

## References

* The Lagrange cross-sphere identity (`Hopf.DualSphereFiberDecomposition`); the quaternion Hopf fibration and
 `SU(2) → SO(3)` double cover (`Hopf.QuaternionIsoclinicHopfFibration`).

No additional assumptions.
-/

set_option autoImplicit false

open Quaternion
open Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionIsoclinicHopfFibration
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionHopfDualSphere

/-- The second imaginary unit `j = (0,0,1,0)`. -/
def jUnit : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

/-- **The Hopf direction vector** of `q` about the imaginary axis `v`: the `ℝ³` imaginary part of the
conjugate `q·v·q̄`. For `v = i` this is the Bloch vector of `hopf q`. -/
def frameVec (q v : ℍ[ℝ]) : Fin 3 → ℝ :=
  ![(q * v * star q).imI, (q * v * star q).imJ, (q * v * star q).imK]

/-- **[The two Hopf directions are always orthogonal]** `⟨Im(q·i·q̄), Im(q·j·q̄)⟩ = 0` for *every* `q` —
conjugation preserves `⟨i,j⟩ = 0`. The geometric and second direction-spheres never align. -/
theorem frame_inner_zero (q : ℍ[ℝ]) :
    sphereInner (frameVec q imagUnit) (frameVec q jUnit) = 0 := by
  simp only [sphereInner, frameVec, imagUnit, jUnit, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **[The `i`-direction has squared length `(normSq q)²`]** `‖Im(q·i·q̄)‖² = (normSq q)²`. -/
theorem frame_imagUnit_normSq (q : ℍ[ℝ]) :
    sphereNormSq (frameVec q imagUnit)
      = (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) ^ 2 := by
  simp only [sphereNormSq, sphereInner, frameVec, imagUnit, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **[The `j`-direction has squared length `(normSq q)²`]** `‖Im(q·j·q̄)‖² = (normSq q)²`. -/
theorem frame_jUnit_normSq (q : ℍ[ℝ]) :
    sphereNormSq (frameVec q jUnit)
      = (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) ^ 2 := by
  simp only [sphereNormSq, sphereInner, frameVec, jUnit, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **[The dual-sphere cross-alignment of the Hopf frame]** `crossSphereDefect ξ η = (normSq q)⁴` — the
Lagrange identity with `⟨ξ,η⟩ = 0` and `‖ξ‖²‖η‖² = (normSq q)⁴`. -/
theorem frame_crossSphereDefect (q : ℍ[ℝ]) :
    crossSphereDefect (frameVec q imagUnit) (frameVec q jUnit) = (normSq q) ^ 4 := by
  rw [crossSphereDefect_lagrange, frame_imagUnit_normSq, frame_jUnit_normSq, frame_inner_zero,
    Quaternion.normSq_def']
  ring

/-- **[The quaternion Hopf frame is a rigid orthonormal pair]** for `q ∈ S³` (`normSq q = 1`),
`crossSphereDefect (Im(q·i·q̄)) (Im(q·j·q̄)) = 1`. The dual-sphere alignment evaluates to the unit-sphere
value: the two Hopf direction-spheres are orthonormal (`⟨ξ,η⟩ = 0`, `‖ξ‖ = ‖η‖ = 1`), so the "2D collapse"
`ξ ∥ η` of `Hopf.DualSphereFiberDecomposition` never occurs — `{q i q̄, q j q̄, q k q̄}` is the `SO(3)` image of
the double cover (`hopf_neg`). -/
theorem hopf_frame_orthonormal (q : ℍ[ℝ]) (hq : normSq q = 1) :
    crossSphereDefect (frameVec q imagUnit) (frameVec q jUnit) = 1 := by
  rw [frame_crossSphereDefect, hq, one_pow]

end Physlib.QuantumMechanics.ComplexAction.Hopf.QuaternionHopfDualSphere

end

end
