/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition
meta import Zil

/-!
# Covariant conservation of the non-Abelian Yang–Mills source current

The non-Abelian field equation `D_μ F^{μν} = J^ν` is consistent only if its source is *covariantly*
conserved.  Unlike the Abelian case (where commuting partials suffice), here the second covariant
derivatives do not commute; the obstruction is the **Ricci identity** `[D_μ, D_ν] M = [F_{μν}, M]`
(`CovariantDerivativeCurvature.ricci_identity`).  Applied to `M = F^{μν}` the correction is the self-
commutator `[F_{νμ}, F^{μν}]`, which vanishes term-by-term because `F` is antisymmetric (`[−X, X] = 0`).
The remaining symmetric contraction vanishes as before.  Hence

`D_ν D_μ F^{μν} = 0`  — the covariant current `J^ν = D_μ F^{μν}` is covariantly conserved.

* `fieldStrength_self_commutator_zero` — `[F_{νμ}, F^{μν}] = 0` (the Ricci correction, term-by-term).
* `nonabelian_current_conservation` — `∑_{μν} D_ν D_μ F^{μν} = 0`.

Honest scope: the algebraic conservation from the pointwise second-covariant-derivative data satisfying the
Ricci identity (`hricci`, discharged at jet level by `ricci_identity`) and the antisymmetry of `F`; the
spacetime integral is not carried.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The field-strength self-commutator vanishes** `[F_{νμ}, F^{μν}] = 0` — the Ricci-identity correction
to the covariant current divergence is zero term-by-term, since `F_{νμ} = −F^{μν}` and `[−X, X] = 0`. -/
@[zil_level physical_theorem]
theorem fieldStrength_self_commutator_zero (F : ι → ι → Matrix ι ι ℝ)
    (hFanti : ∀ μ ν, F μ ν = -F ν μ) (μ ν : ι) :
    F ν μ * F μ ν - F μ ν * F ν μ = 0 := by
  rw [hFanti ν μ, neg_mul, mul_neg]
  abel

/-- **Covariant conservation of the non-Abelian source current** `∑_{μν} D_ν D_μ F^{μν} = 0`.  With
`D2 a b c d = D_a D_b F^{cd}`, the Ricci identity `D2 a b c d − D2 b a c d = [F_{ab}, F^{cd}]` (discharged at
jet level by `ricci_identity`) and the antisymmetry of `F` (in both the field indices and hence `D2`'s last
two), the covariant divergence of the current `D_μ F^{μν}` vanishes. -/
@[zil_level bridge_theorem]
theorem nonabelian_current_conservation (D2 : ι → ι → ι → ι → Matrix ι ι ℝ) (F : ι → ι → Matrix ι ι ℝ)
    (hFanti : ∀ μ ν, F μ ν = -F ν μ)
    (hD2anti : ∀ a b c d, D2 a b c d = -D2 a b d c)
    (hricci : ∀ a b c d, D2 a b c d - D2 b a c d = F a b * F c d - F c d * F a b) :
    (∑ μ, ∑ ν, D2 ν μ μ ν) = 0 := by
  -- S = ∑ D2 ν μ μ ν, T = ∑ D2 μ ν μ ν.  Ricci ⇒ S = T; antisymmetry ⇒ T = −S; hence S = −S = 0.
  have hST : (∑ μ, ∑ ν, D2 ν μ μ ν) = ∑ μ, ∑ ν, D2 μ ν μ ν := by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [hricci ν μ μ ν]
    exact fieldStrength_self_commutator_zero F hFanti μ ν
  have hT : (∑ μ, ∑ ν, D2 μ ν μ ν) = -(∑ μ, ∑ ν, D2 ν μ μ ν) := by
    have e1 : (∑ μ, ∑ ν, D2 μ ν μ ν) = ∑ μ, ∑ ν, -D2 μ ν ν μ :=
      Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => hD2anti μ ν μ ν
    have e2 : (∑ μ, ∑ ν, -D2 μ ν ν μ) = -∑ μ, ∑ ν, D2 μ ν ν μ := by
      simp only [Finset.sum_neg_distrib]
    have e3 : (∑ μ, ∑ ν, D2 μ ν ν μ) = ∑ μ, ∑ ν, D2 ν μ μ ν := Finset.sum_comm
    rw [e1, e2, e3]
  have hSS : (∑ μ, ∑ ν, D2 ν μ μ ν) = -(∑ μ, ∑ ν, D2 ν μ μ ν) := hST.trans hT
  have h2 : (2 : ℝ) • (∑ μ, ∑ ν, D2 ν μ μ ν) = 0 := by
    rw [two_smul]; nth_rewrite 1 [hSS]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation

zil attach fieldStrength_self_commutator_zero where
  supported_by @ "lean:ricci_identity",
  formalizes @ "claim:the-yang-mills-field-strength-self-commutator-f-nu-mu-times-f-mu-nu-minus-f-mu-nu-times-f-nu-mu-vanishes-because-the-field-strength-is-antisymmetric-and-the-commutator-of-minus-x-with-x-is-zero"

zil attach nonabelian_current_conservation where
  formalizes @ "claim:the-non-abelian-yang-mills-source-current-is-covariantly-conserved-the-covariant-divergence-of-the-field-strength-covariant-divergence-d-nu-d-mu-f-mu-nu-vanishes-the-ricci-identity-correction-being-the-vanishing-field-strength-self-commutator-and-the-symmetric-contraction-vanishing-by-antisymmetry",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.ricci_identity"

zil_file_contract physlib.yangMillsCovariantCurrentConservation where
  promises "Covariant conservation of the non-Abelian Yang-Mills source current. The non-Abelian field equation, the covariant divergence of the field strength equals the current, is consistent only if its source is covariantly conserved. Unlike the Abelian case the second covariant derivatives do not commute; the obstruction is the Ricci identity, the commutator of two covariant derivatives on an endomorphism equals the commutator of the curvature with that endomorphism. Applied to the field strength the correction is the field-strength self-commutator, F nu mu times F mu nu minus F mu nu times F nu mu, which vanishes term by term because the field strength is antisymmetric and the commutator of minus X with X is zero. The remaining symmetric contraction vanishes by antisymmetry. Hence the covariant divergence of the current, the double sum over mu and nu of the second covariant derivative of F upper mu nu, vanishes, so the covariant current is covariantly conserved. Honest scope: the algebraic conservation from the pointwise second-covariant-derivative data satisfying the Ricci identity, discharged at jet level by the Ricci identity theorem, and the antisymmetry of the field strength; the spacetime integral is not carried."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.ricci_identity"
  ]
  forbids_substitutes [
    "reading the algebraic covariant conservation from Ricci-identity jet data as the full spacetime-integrated conservation law"
  ]
  witnessed_by [
    fieldStrength_self_commutator_zero,
    nonabelian_current_conservation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.yangMillsCovariantCurrentConservation
