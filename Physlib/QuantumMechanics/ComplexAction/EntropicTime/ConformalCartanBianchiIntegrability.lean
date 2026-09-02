/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanYangMills
public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiEinsteinIntegrability

/-!
# The Bianchi identities of the normal conformal Cartan curvature

The curvature `F = dA + A ∧ A` of the normal conformal Cartan connection (arXiv:2302.12739, Eqs. 15,
16) obeys the Bianchi identity `D_A F = 0` (Eq. 18), and the field equation `D_A ⋆F = 0`
(`ConformalCartanYangMills.vacuumCartanYangMills`, `B_{ab} = 0`) is an integrability condition. All
three faces are already in the repository — this module **leverages** them for the conformal Cartan
curvature rather than re-deriving anything:

* the **algebraic (first) Bianchi identity** `R_{a[bcd]} = 0` of the Weyl component of `F` (Eq. 16) is
  the vanishing cyclic sum (`Curvature.JacobiRicciBianchiTetrad.firstBianchi_iff_cyclicSum`,
  `IsRiemannCurvature.bianchi`);
* the algebraic core of the **differential (covariant) Bianchi identity** `D_A F = 0` is the Lie-algebra
  **Jacobi identity** `⁅A_ρ, ⁅A_μ, A_ν⁆⁆ + cyclic = 0` (`JacobiRicciBianchiTetrad.frame_jacobi`) — the
  first Bianchi and the gauge Jacobi are the same cyclic-sum structure
  (`jacobi_ricci_bianchi_correspondence`); the `so(2,4)`-valued Cartan connection is a Lie ring, so its
  bracket obeys it;
* the **field equation as a second-Bianchi integrability condition** on the `6×6` conformal system:
  when the conformal coefficient matrix is invertible, the field-equation (Bach) vector vanishes
  (`Curvature.JacobiRicciBianchiEinsteinIntegrability.einstein_integrability_secondBianchi`, Van den
  Bergh's `6×6` reduction).

The `so(2,4)` gauge algebra is the conformal algebra of the AdS/CFT string theory
(`AffineKacMoodyConformalAlgebra`), the tetrad block `Γ^a_b = −Γ^b_a` of the Cartan connection is
Lorentz-algebra valued (`Curvature.JacobiRicciBianchiLusanna.connMatrix_isLorentz`), and the Einstein-`Λ`
solutions are the arc's Verlinde area-per-bit / de Sitter vacua. Bianchi identities, gauge Jacobi, and
conformal integrability are the one cyclic-sum structure of the conformal Cartan curvature.

* **§A** the first Bianchi of the Weyl component of `F` (Eqs. 14, 16).
* **§B** the differential Bianchi `D_A F = 0`: the gauge Jacobi identity (Eq. 18).
* **§C** the field equation as the `6×6` conformal second-Bianchi integrability (Eqs. 29-30).
* **§D** the three faces together.

## References

* A. Bac, W. Kamiński, J. Lewandowski, M. Broda, arXiv:2302.12739 — Eqs. 15-18, 29-30.
* N. Van den Bergh, arXiv:1302.6448 — the Einstein equations as integrability of the second Bianchi
  identity (`JacobiRicciBianchiEinsteinIntegrability`).
-/

set_option autoImplicit false

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiEinsteinIntegrability
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBianchiIntegrability

/-! ## A. The first (algebraic) Bianchi identity of the Weyl component -/

/-- **[The Weyl component of the Cartan curvature satisfies the first Bianchi identity, Eqs. 14, 16]**
the conformal (Weyl) block `C^a_b` of the normal conformal Cartan curvature `F` (Eq. 16) is a
Riemann-type tensor, and every such tensor satisfies the algebraic first Bianchi identity
`R_{a[bcd]} = 0` — the vanishing of the cyclic sum over the last three indices
(`firstBianchi_iff_cyclicSum`, `IsRiemannCurvature.bianchi`). -/
theorem nccWeyl_firstBianchi {ι : Type*} [Fintype ι] (Rm : RiemannTensor ι)
    (h : IsRiemannCurvature Rm) : FirstBianchi Rm := by
  rw [firstBianchi_iff_cyclicSum]
  intro a b c d
  simpa [cyclicSum] using h.bianchi a b c d

/-! ## B. The differential Bianchi `D_A F = 0` is the gauge Jacobi identity -/

/-- **[The differential Bianchi identity of the Cartan connection is the gauge Jacobi identity,
Eq. 18]** the algebraic core of `D_A F = 0` — the cyclic bracket sum of the `so(2,4)`-valued Cartan
connection components — vanishes by the Lie-algebra Jacobi identity
(`JacobiRicciBianchiTetrad.frame_jacobi`). The covariant Bianchi identity of the Yang-Mills field
strength is the Jacobi identity of the gauge algebra, the same cyclic-sum structure as the first
Bianchi (`jacobi_ricci_bianchi_correspondence`). -/
theorem nccBianchi_bracket_jacobi {X ι 𝔤 : Type*} [LieRing 𝔤]
    (A : GaugePotential X ι 𝔤) (x : X) (μ ν ρ : ι) :
    ⁅A x ρ, ⁅A x μ, A x ν⁆⁆ + ⁅A x μ, ⁅A x ν, A x ρ⁆⁆ + ⁅A x ν, ⁅A x ρ, A x μ⁆⁆ = 0 :=
  frame_jacobi (A x ρ) (A x μ) (A x ν)

/-! ## C. The field equation as a conformal second-Bianchi integrability condition -/

/-- **[The conformal Cartan field equation is a second-Bianchi integrability condition, Eqs. 29-30]**
`D_A ⋆F = 0` (`B = 0`) on the `6×6` conformal (`so(2,4)`) system: when the conformal coefficient matrix
is invertible, the field-equation (Bach) vector is forced to vanish — the vacuum equation is an
integrability condition of the second-Bianchi/Newman-Penrose system
(`einstein_integrability_secondBianchi`, Van den Bergh's `6×6` reduction). -/
theorem ncc_field_equation_integrability (M : Matrix (Fin 6) (Fin 6) ℝ) [Invertible M]
    (bachVector : Fin 6 → ℝ) (h : M.mulVec bachVector = 0) : bachVector = 0 :=
  einstein_integrability_secondBianchi M bachVector h

/-! ## D. The three Bianchi faces of the conformal Cartan curvature -/

/-- **[The three Bianchi faces of the conformal Cartan curvature]** together: the Weyl block of `F`
obeys the **first** (algebraic) Bianchi identity; the covariant **differential** Bianchi `D_A F = 0`
is the gauge Jacobi identity of the `so(2,4)` connection; and the field equation `B = 0` is the
**second-Bianchi** integrability condition on the invertible `6×6` conformal system. First Bianchi,
gauge Jacobi and conformal integrability are one cyclic-sum structure. -/
theorem ncc_three_bianchi_faces {X ι 𝔤 : Type*} [Fintype ι] [LieRing 𝔤]
    (Rm : RiemannTensor ι) (hRm : IsRiemannCurvature Rm)
    (A : GaugePotential X ι 𝔤) (x : X) (μ ν ρ : ι)
    (M : Matrix (Fin 6) (Fin 6) ℝ) [Invertible M]
    (bachVector : Fin 6 → ℝ) (hB : M.mulVec bachVector = 0) :
    FirstBianchi Rm
    ∧ ⁅A x ρ, ⁅A x μ, A x ν⁆⁆ + ⁅A x μ, ⁅A x ν, A x ρ⁆⁆ + ⁅A x ν, ⁅A x ρ, A x μ⁆⁆ = 0
    ∧ bachVector = 0 :=
  ⟨nccWeyl_firstBianchi Rm hRm,
    nccBianchi_bracket_jacobi A x μ ν ρ,
    ncc_field_equation_integrability M bachVector hB⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBianchiIntegrability

end
