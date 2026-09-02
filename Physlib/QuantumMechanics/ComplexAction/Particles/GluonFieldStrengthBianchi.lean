/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition
meta import Zil

/-!
# The gluon field strength and the homogeneous Yang–Mills equation

The QCD gluon field strength is the non-Abelian curvature of the `SU(3)` gauge connection `A`,

`F_{μν} = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]`,

whose commutator `[A_μ, A_ν]` is the **gluon self-interaction**.  This is exactly the curvature two-form
(`CurvatureTwoFormBianchi.curvatureTwoForm`), so the **homogeneous Yang–Mills equation**
`D_μ F_{νρ} + D_ν F_{ρμ} + D_ρ F_{μν} = 0` is a *derived* theorem — the Bianchi identity
`curvatureTwoForm_bianchi` — not a hypothesis.  (The existing `YangMillsGaugeDynamics` carries the
*inhomogeneous* equation `D_μ F^{μν} = J`; this supplies the missing homogeneous partner.)

For an Abelian gauge group (`[A_μ, A_ν] = 0`, e.g. the photon) the self-interaction vanishes and
`F_{μν} = ∂_μ A_ν − ∂_ν A_μ` is the Maxwell field strength, whose homogeneous equation is the source-free
`∂_{[μ}F_{νρ]} = 0` (`dF = 0`).

* `gluonFieldStrength` — `F_{μν}` of the gauge connection.
* `gluonFieldStrength_antisymm` — `F_{μν} = −F_{νμ}`.
* `gluonFieldStrength_abelian` — Abelian reduction `F = ∂A − ∂A` (no gluon self-interaction).
* `abelianGluon_homogeneous_maxwell` — the Abelian homogeneous Maxwell equation `∂_{[μ}F_{νρ]} = 0`.

Honest scope: the field-strength geometry, its Abelian reduction and the (Abelian) homogeneous field
equation; the non-Abelian homogeneous equation is the Bianchi identity `curvatureTwoForm_bianchi`, and the
inhomogeneous `D_μ F^{μν} = J` (`YangMillsGaugeDynamics`) is not derived from an `∫F²` action here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi

open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature
open Physlib.QuantumMechanics.ComplexAction.Curvature.CurvatureTwoFormBianchi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The gluon field strength** `F_{μν} = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]` — the non-Abelian curvature of
the `SU(3)` gauge connection `A` (the commutator is the gluon self-interaction). -/
def gluonFieldStrength (A : ι → Matrix ι ι ℝ) (dA : ι → ι → Matrix ι ι ℝ) (μ ν : ι) : Matrix ι ι ℝ :=
  dA μ ν - dA ν μ + A μ * A ν - A ν * A μ

/-- The gluon field strength is the curvature two-form of the connection. -/
theorem gluonFieldStrength_eq_curvatureTwoForm (A : ι → Matrix ι ι ℝ) (dA : ι → ι → Matrix ι ι ℝ)
    (μ ν : ι) : gluonFieldStrength A dA μ ν = curvatureTwoForm A dA μ ν := rfl

/-- **The gluon field strength is antisymmetric** `F_{μν} = −F_{νμ}`. -/
@[zil_level physical_theorem]
theorem gluonFieldStrength_antisymm (A : ι → Matrix ι ι ℝ) (dA : ι → ι → Matrix ι ι ℝ) (μ ν : ι) :
    gluonFieldStrength A dA μ ν = -gluonFieldStrength A dA ν μ := by
  unfold gluonFieldStrength; abel

/-- **Abelian reduction of the gluon field strength** — when the gauge potential commutes
(`[A_μ, A_ν] = 0`, an Abelian group), the self-interaction vanishes and `F_{μν} = ∂_μ A_ν − ∂_ν A_μ`, the
Maxwell field strength. -/
@[zil_level physical_theorem]
theorem gluonFieldStrength_abelian (A : ι → Matrix ι ι ℝ) (dA : ι → ι → Matrix ι ι ℝ) (μ ν : ι)
    (hab : A μ * A ν = A ν * A μ) :
    gluonFieldStrength A dA μ ν = dA μ ν - dA ν μ := by
  unfold gluonFieldStrength; rw [hab]; abel

/-- **The homogeneous Yang–Mills equation** for the gluon field strength — the cyclic sum of its
gauge-covariant derivatives vanishes.  This is the Bianchi identity `curvatureTwoForm_bianchi`, a *derived*
theorem, the homogeneous partner of the inhomogeneous `D_μ F^{μν} = J`. -/
theorem gluon_homogeneous_yangMills_equation (A : ι → Matrix ι ι ℝ) (dA : ι → ι → Matrix ι ι ℝ)
    (ddA : ι → ι → ι → Matrix ι ι ℝ) (μ ν ρ : ι) (hsym : ∀ a b c, ddA a b c = ddA b a c) :
    gaugeCovariantDerivCurvature A dA ddA μ ν ρ + gaugeCovariantDerivCurvature A dA ddA ν ρ μ
      + gaugeCovariantDerivCurvature A dA ddA ρ μ ν = 0 :=
  curvatureTwoForm_bianchi A dA ddA μ ν ρ hsym

/-- **The Abelian homogeneous Maxwell equation** `∂_{[μ}F_{νρ]} = 0` (`dF = 0`) — for an Abelian field
strength `F_{μν} = ∂_μ A_ν − ∂_ν A_μ`, the cyclic sum of ordinary partial derivatives vanishes by commuting
mixed partials (`ddA μ ν ρ = ∂_μ∂_ν A_ρ`). -/
@[zil_level physical_theorem]
theorem abelianGluon_homogeneous_maxwell (ddA : ι → ι → ι → Matrix ι ι ℝ) (μ ν ρ : ι)
    (hsym : ∀ a b c, ddA a b c = ddA b a c) :
    (ddA μ ν ρ - ddA μ ρ ν) + (ddA ν ρ μ - ddA ν μ ρ) + (ddA ρ μ ν - ddA ρ ν μ) = 0 := by
  rw [hsym ν μ ρ, hsym ρ μ ν, hsym ρ ν μ]
  abel

end Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi

zil attach gluonFieldStrength_antisymm where
  formalizes @ "claim:the-qcd-gluon-field-strength-the-non-abelian-curvature-of-the-su-three-gauge-connection-is-antisymmetric-in-its-two-spacetime-indices"

zil attach gluonFieldStrength_abelian where
  supported_by @ "lean:curvatureTwoForm_bianchi",
  formalizes @ "claim:the-gluon-field-strength-reduces-to-the-maxwell-field-strength-partial-a-minus-partial-a-when-the-gauge-potential-commutes-abelian-group-the-gluon-self-interaction-commutator-vanishing"

zil attach abelianGluon_homogeneous_maxwell where
  formalizes @ "claim:the-abelian-homogeneous-maxwell-equation-the-cyclic-sum-of-partial-derivatives-of-the-abelian-field-strength-vanishes-d-f-equals-zero-by-commuting-mixed-partials"

zil_file_contract physlib.gluonFieldStrengthBianchi where
  promises "The QCD gluon field strength and the homogeneous Yang-Mills equation. The gluon field strength is the non-Abelian curvature of the SU(3) gauge connection, the antisymmetrized partial derivative of the potential plus the potential commutator, whose commutator is the gluon self-interaction; it is exactly the curvature two-form. The field strength is antisymmetric in its two spacetime indices. For an Abelian gauge group where the potential commutes and the self-interaction vanishes, it reduces to the Maxwell field strength, the antisymmetrized partial derivative of the potential. The homogeneous Yang-Mills equation, the cyclic sum of gauge-covariant derivatives of the field strength vanishing, is the derived Bianchi identity, the homogeneous partner of the inhomogeneous divergence equals current equation. The Abelian homogeneous Maxwell equation, the cyclic sum of partial derivatives of the Abelian field strength vanishing, holds by commuting mixed partials. Honest scope: the field-strength geometry, its Abelian reduction and homogeneous equation; the inhomogeneous equation is not derived from an action integral here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.curvatureTwoForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CurvatureTwoFormBianchi.gaugeCovariantDerivCurvature"
  ]
  forbids_substitutes [
    "reading the homogeneous field equation and Abelian reduction as a derivation of the inhomogeneous Yang-Mills equation from an F-squared action or the QCD running coupling"
  ]
  witnessed_by [
    gluonFieldStrength_antisymm,
    gluonFieldStrength_abelian,
    abelianGluon_homogeneous_maxwell
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.gluonFieldStrengthBianchi
