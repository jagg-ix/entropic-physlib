/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

/-!
# One cyclic identity, four faces: tetrad first Bianchi in the BCJ Jacobi family

Links the Jacobi–Ricci–Bianchi tetrad result to the repo's BCJ color–kinematics double-copy web. Van den
Bergh's central observation — *the first Bianchi identity is the Jacobi identity* — is the **gravity face** of
the same three-term cyclic identity that runs through color–kinematics duality:

| face | identity | source |
|---|---|---|
| gauge **color** Jacobi | `c_s + c_t + c_u = 0` | `BCJColorKinematicsDuality.color_jacobi` |
| gauge **kinematic** Jacobi (`= dF=0`, the EM first Bianchi) | `n_s + n_t + n_u = 0` | `BCJColorKinematicsDuality.kinematic_jacobi` |
| **gravity** first Bianchi | `R_{a[bcd]} = 0` | `Curvature.JacobiRicciBianchiTetrad` / `LeviCivita.BianchiValidation.FirstBianchi` |
| **frame** Jacobi (Lie) | `⁅x,⁅y,z⁆⁆ + ⟲ = 0` | `Curvature.JacobiRicciBianchiTetrad.frame_jacobi` |

All four are instances of `cyclicSum … = 0` — the single cyclic operator of `Curvature.JacobiRicciBianchiTetrad`.

* `cyclicSum_first_index` — the cyclic sum of a first-index-only function over three labels is the plain
 triple sum (so a three-channel `X_s+X_t+X_u` *is* a `cyclicSum`).
* `color_jacobi_cyclicSum`, `kinematic_jacobi_cyclicSum` — the BCJ color and kinematic Jacobi identities as
 `cyclicSum`-vanishings.
* `jacobi_bianchi_double_copy_family` — the main result: all four faces, written in the one `cyclicSum`/Jacobi
 form, from a single BCJ duality, a first-Bianchi Riemann tensor, and any Lie ring.

Proven: each face is recast into the common `cyclicSum`/`lie_jacobi` form, reusing the
existing BCJ structure fields, `FirstBianchi`, and the tetrad results — no new identities are asserted, the
content is the *unification*. The dynamical double copy (KLT, the gravity-from-gauge map) lives in the BCJ
files; this only ties the algebraic cyclic identities together.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, *New relations for gauge-theory amplitudes*, Phys. Rev. D **78**
 (2008) 085011, doi:10.1103/PhysRevD.78.085011; arXiv:0805.3993 [hep-ph] — color–kinematics duality, the
 color/kinematic Jacobi identities `c_s+c_t+c_u=0`, `n_s+n_t+n_u=0`.
* N. Van den Bergh, *On the relation between the Einstein field equations and the Jacobi–Ricci–Bianchi
 system*, Class. Quantum Grav. **31** (2014) 145007, doi:10.1088/0264-9381/31/14/145007;
 arXiv:1302.6448v3 [gr-qc] (10 June 2013) — first Bianchi `R_{a[bcd]}=0` = frame Jacobi (Eqs (14)–(15), p. 3).
* `Physlib` (`BCJDoubleCopy.ColorKinematicsDoubleCopy.BCJColorKinematicsDuality`, `Curvature.JacobiRicciBianchiTetrad`,
 `LeviCivita.BianchiValidation.FirstBianchi`).

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation (FirstBianchi)

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily

/-- **[A three-channel sum is a cyclic sum]** the cyclic sum of a function depending only on its first index,
evaluated on three distinct labels, is the plain triple sum `g 0 + g 1 + g 2` — so any `X_s + X_t + X_u`
(color/kinematic Jacobi) is a `cyclicSum`. -/
theorem cyclicSum_first_index {M : Type*} [AddCommMonoid M] (g : Fin 3 → M) :
    cyclicSum (fun (i : Fin 3) _ _ => g i) 0 1 2 = g 0 + g 1 + g 2 := rfl

/-- **[The BCJ color Jacobi is a cyclic sum]** `c_s + c_t + c_u = 0` recast as `cyclicSum … = 0` — the gauge
color face of the cyclic identity. -/
theorem color_jacobi_cyclicSum (d : BCJColorKinematicsDuality) :
    cyclicSum (fun (i : Fin 3) _ _ => (![d.c_s, d.c_t, d.c_u] : Fin 3 → ℝ) i) 0 1 2 = 0 := by
  rw [cyclicSum_first_index]; exact d.color_jacobi

/-- **[The BCJ kinematic Jacobi is a cyclic sum]** `n_s + n_t + n_u = 0` recast as `cyclicSum … = 0` — the
gauge kinematic face (the `dF = 0` EM first Bianchi of color–kinematics duality). -/
theorem kinematic_jacobi_cyclicSum (d : BCJColorKinematicsDuality) :
    cyclicSum (fun (i : Fin 3) _ _ => (![d.n_s, d.n_t, d.n_u] : Fin 3 → ℝ) i) 0 1 2 = 0 := by
  rw [cyclicSum_first_index]; exact d.kinematic_jacobi

/-- **[One cyclic identity, four faces]** the BCJ color Jacobi, the BCJ kinematic Jacobi (`= dF=0`), the
gravity first Bianchi `R_{a[bcd]}=0`, and the frame Lie Jacobi are all the same `cyclicSum`/`lie_jacobi`
vanishing — Van den Bergh's "first Bianchi = Jacobi" placed in the color–kinematics double-copy family. -/
theorem jacobi_bianchi_double_copy_family
    (d : BCJColorKinematicsDuality)
    {κ : Type*} [Fintype κ] (Rie : κ → κ → κ → κ → ℝ) (hFB : FirstBianchi Rie)
    {L : Type*} [LieRing L] :
    cyclicSum (fun (i : Fin 3) _ _ => (![d.c_s, d.c_t, d.c_u] : Fin 3 → ℝ) i) 0 1 2 = 0
      ∧ cyclicSum (fun (i : Fin 3) _ _ => (![d.n_s, d.n_t, d.n_u] : Fin 3 → ℝ) i) 0 1 2 = 0
      ∧ (∀ a b c e, cyclicSum (Rie a) b c e = 0)
      ∧ (∀ x y z : L, ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0) :=
  ⟨color_jacobi_cyclicSum d, kinematic_jacobi_cyclicSum d,
    (firstBianchi_iff_cyclicSum Rie).mp hFB, fun x y z => frame_jacobi x y z⟩

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily

end
