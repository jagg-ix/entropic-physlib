/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanBachEinstein

/-!
# The normal conformal Cartan connection as a Yang-Mills gauge field

Bac, Kamiński, Lewandowski and Broda (arXiv:2302.12739) build gravity as the **Yang-Mills theory of
the normal conformal Cartan connection** — the `so(2,4)`-valued gauge potential `A` (Eq. 3). Its
structures are exactly the repository's gauge-field dynamics
(`Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics`):

* the curvature `F = dA + A ∧ A` (Eq. 15) is `yangMillsCurvature deriv A` — the field strength
  `F_{μν} = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]`, a genuine antisymmetric two-form;
* the conformal rescaling / (pseudo)rotation `A' = h⁻¹ A h + h⁻¹ dh` (Eq. 8) is
  `gaugeTransformPotential`, and the covariant transformation `F' = h⁻¹ F h` (Eq. 19) is
  `gaugeTransformCurvature`;
* the vacuum field equation `D_A ⋆F = 0` (Eq. 30, equivalent to the Bach tensor `B = 0`, Eq. 29) is
  `YangMillsEquation` with vanishing source.

The Cartan-Yang-Mills Lagrangian `L_CYM = ½ F^I_J ∧ ⋆F^J_I` (Eq. 23) and the symplectic current
potential `Θ = δA^I_J ∧ ⋆F^J_I` (Eq. 31) are **conformally invariant** (Eqs. 24, 32): under the gauge
transformation the trace-paired curvature is unchanged, `tr(F' G') = tr(F G)`, by cyclicity of the
matrix trace. This is the conformal invariance that makes the whole construction well-defined at the
conformal boundary — formalized here on the gauge machinery, not asserted.

(Mathlib supplies the exterior-calculus side directly: `extDeriv` with `extDeriv_extDeriv` (the
nilpotency `d² = 0`, whence the abelian Bianchi identity `dF = d²A = 0`) and the `domCoprod` wedge
product of alternating forms; the coordinate field strength `yangMillsCurvature` is their component
form, and reduces to `dA` in the abelian case, `yangMillsCurvature_eq_exteriorDerivative_of_comm`.)

* **§A** the Cartan curvature is an antisymmetric Yang-Mills two-form (Eqs. 6, 15).
* **§B** conformal (gauge) invariance of the trace-paired curvature — the Lagrangian and symplectic
  potential (Eqs. 24, 32).
* **§C** the vacuum field equation `D_A ⋆F = 0` and the link to Bach-flatness: Einstein metrics solve
  it (`ConformalCartanBachEinstein.bach_einstein_vanishes`).

## References

* A. Bac, W. Kamiński, J. Lewandowski, M. Broda, arXiv:2302.12739 — Eqs. 3, 8, 15, 19, 23-32.
* Repo carriers: `YangMillsGaugeDynamics.{yangMillsCurvature, gaugeTransformPotential,
  gaugeTransformCurvature, YangMillsEquation}`; Mathlib `extDeriv`, `extDeriv_extDeriv`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Matrix

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanYangMills

/-! ## A. The Cartan curvature is an antisymmetric Yang-Mills two-form -/

/-- **[The normal conformal Cartan curvature is an antisymmetric two-form, Eqs. 6, 15]** the curvature
`F = dA + A∧A` of the `so(2,4)`-valued Cartan connection is the Yang-Mills field strength
`yangMillsCurvature`, antisymmetric in its two form indices — `F_{μν} = −F_{νμ}`. -/
theorem nccCurvature_antisymm {X ι : Type*} {n : ℕ}
    (deriv : GaugePartial X ι (Matrix (Fin n) (Fin n) ℝ))
    (A : GaugePotential X ι (Matrix (Fin n) (Fin n) ℝ)) (x : X) (μ ν : ι) :
    yangMillsCurvature deriv A x μ ν = -yangMillsCurvature deriv A x ν μ :=
  yangMillsCurvature_antisymm deriv A x μ ν

/-! ## B. Conformal (gauge) invariance of the Cartan-Yang-Mills Lagrangian -/

/-- **[Gauge invariance of the trace-paired curvature]** `tr((h⁻¹ F h)(h⁻¹ G h)) = tr(F G)` when
`h⁻¹ h = 1`. Cyclicity of the matrix trace makes the pairing invariant under the gauge (conformal
rescaling / pseudorotation) transformation — the algebraic heart of the conformal invariance of the
Cartan-Yang-Mills Lagrangian and symplectic potential. -/
theorem gauge_invariant_trace {n : ℕ} (U Uinv F G : Matrix (Fin n) (Fin n) ℝ)
    (hUi : Uinv * U = 1) :
    (U * F * Uinv * (U * G * Uinv)).trace = (F * G).trace := by
  have h1 : U * F * Uinv * (U * G * Uinv) = U * (F * G) * Uinv := by
    have hre : U * F * Uinv * (U * G * Uinv) = U * F * (Uinv * U) * G * Uinv := by noncomm_ring
    rw [hre, hUi]; noncomm_ring
  rw [h1, Matrix.trace_mul_comm, ← mul_assoc, hUi, one_mul]

/-- **[The Cartan-Yang-Mills Lagrangian is conformally invariant, Eqs. 24, 32]** the trace-paired
gauge-transformed curvatures satisfy `tr(F' G') = tr(F G)` with `F' = gaugeTransformCurvature`,
`G' = gaugeTransformCurvature` — the conformal invariance of `L_CYM = ½ F^I_J ∧ ⋆F^J_I` (Eq. 24) and the
symplectic current potential `Θ = δA^I_J ∧ ⋆F^J_I` (Eq. 32). The current is finite at the conformal
boundary precisely because of this invariance. -/
theorem cartanYangMills_gauge_invariant {X ι : Type*} {n : ℕ}
    (U Uinv : X → Matrix (Fin n) (Fin n) ℝ) (F G : GaugeCurvature X ι (Matrix (Fin n) (Fin n) ℝ))
    (x : X) (μ ν : ι) (hUi : Uinv x * U x = 1) :
    (gaugeTransformCurvature U Uinv F x μ ν * gaugeTransformCurvature U Uinv G x μ ν).trace
      = (F x μ ν * G x μ ν).trace := by
  simp only [gaugeTransformCurvature_apply]
  exact gauge_invariant_trace (U x) (Uinv x) (F x μ ν) (G x μ ν) hUi

/-! ## C. The vacuum field equation and Bach-flatness -/

/-- **[The vacuum Cartan-Yang-Mills equation, Eq. 30]** the field equation of the Cartan-Yang-Mills
theory is `D_A ⋆F = 0` — the source-free Yang-Mills equation `YangMillsEquation deriv A F 0`
(`yangMillsDivergence deriv A F ν x = 0`). By Eqs. 20-22, 29 this is equivalent to the vanishing of the
**Bach tensor** `B = 0`, so the Einstein metrics — which are Bach flat
(`ConformalCartanBachEinstein.bach_einstein_vanishes`), including the arc's de Sitter vacuum with
`Λ = 12π/(ℓ_P² N)` — are solutions of the conformal Cartan-Yang-Mills gravity. -/
def vacuumCartanYangMills {X ι : Type*} [Fintype ι]
    (deriv : GaugePartial X ι (Matrix (Fin 6) (Fin 6) ℝ))
    (A : GaugePotential X ι (Matrix (Fin 6) (Fin 6) ℝ))
    (F : GaugeCurvature X ι (Matrix (Fin 6) (Fin 6) ℝ)) : Prop :=
  YangMillsEquation deriv A F 0

/-- **[The vacuum Cartan-Yang-Mills equation is the vanishing covariant divergence of the curvature]**
`D_μ F^{μν} = 0` — the Bach-flatness condition in Yang-Mills form. -/
theorem vacuumCartanYangMills_iff {X ι : Type*} [Fintype ι]
    (deriv : GaugePartial X ι (Matrix (Fin 6) (Fin 6) ℝ))
    (A : GaugePotential X ι (Matrix (Fin 6) (Fin 6) ℝ))
    (F : GaugeCurvature X ι (Matrix (Fin 6) (Fin 6) ℝ)) :
    vacuumCartanYangMills deriv A F ↔ ∀ ν x, yangMillsDivergence deriv A F ν x = 0 :=
  Iff.rfl

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConformalCartanYangMills
