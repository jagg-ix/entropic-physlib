/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition
meta import Zil

/-!
# Conservation of the Yang–Mills source current (Abelian case)

The inhomogeneous field equation `∂_μ F^{μν} = J^ν` is consistent only if its source is conserved.  For the
Abelian (Maxwell) field strength the current `J^ν = ∂_μ F^{μν}` obeys

`∂_ν J^ν = ∂_ν ∂_μ F^{μν} = 0`,

because the second-derivative operator `∂_ν ∂_μ` is **symmetric** in `(μ,ν)` (commuting mixed partials) while
the field strength `F^{μν}` is **antisymmetric** — and a symmetric-times-antisymmetric contraction vanishes.
So the field equation cannot be posited with an arbitrary source; the source is automatically conserved.

* `sum_sum_antisymm_zero` — a double sum of an antisymmetric family vanishes (`g μ ν = −g ν μ ⇒ ∑∑ g = 0`).
* `abelian_current_conservation` — `∂_ν ∂_μ F^{μν} = 0` from commuting partials and the antisymmetry of `F`.

Honest scope: the algebraic conservation identity from the pointwise-jet second-derivative data (`∂∂F`
symmetric in the two derivative indices) and the antisymmetry of `F`; the non-Abelian covariant version
`D_ν D_μ F^{μν} = 0` (which additionally uses the Ricci identity) is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A double sum of an antisymmetric family vanishes** `g μ ν = −g ν μ ⇒ ∑_μ ∑_ν g μ ν = 0`. -/
@[zil_level structural]
theorem sum_sum_antisymm_zero {M : Type*} [AddCommGroup M] [Module ℝ M] (g : ι → ι → M)
    (hg : ∀ μ ν, g μ ν = -g ν μ) :
    (∑ μ, ∑ ν, g μ ν) = 0 := by
  have hSS : (∑ μ, ∑ ν, g μ ν) = -∑ μ, ∑ ν, g μ ν := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ν _ => hg ν μ
  have h2 : (2 : ℝ) • (∑ μ, ∑ ν, g μ ν) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hSS]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **Conservation of the Abelian source current** `∂_ν ∂_μ F^{μν} = 0`.  With `dd a b c d = ∂_a ∂_b F_{cd}`,
commuting mixed partials (`dd` symmetric in its first two indices) and the antisymmetry of the field
strength (`dd` antisymmetric in its last two), the divergence of the current `∂_μ F^{μν}` vanishes — the
field equation `∂_μ F^{μν} = J^ν` forces `∂_ν J^ν = 0`. -/
@[zil_level physical_theorem]
theorem abelian_current_conservation (dd : ι → ι → ι → ι → Matrix ι ι ℝ)
    (hcomm : ∀ a b c d, dd a b c d = dd b a c d)
    (hantisym : ∀ a b c d, dd a b c d = -dd a b d c) :
    (∑ μ, ∑ ν, dd ν μ μ ν) = 0 := by
  refine sum_sum_antisymm_zero (fun μ ν => dd ν μ μ ν) fun μ ν => ?_
  rw [hcomm μ ν ν μ, hantisym ν μ ν μ, neg_neg]

end Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation

zil attach sum_sum_antisymm_zero where
  formalizes @ "claim:a-double-sum-over-two-indices-of-an-antisymmetric-family-g-mu-nu-equals-minus-g-nu-mu-vanishes"

zil attach abelian_current_conservation where
  supported_by @ "lean:sum_sum_antisymm_zero",
  formalizes @ "claim:the-abelian-yang-mills-maxwell-source-current-is-conserved-the-divergence-of-the-field-strength-divergence-partial-nu-partial-mu-f-mu-nu-vanishes-because-the-symmetric-second-derivative-contracts-with-the-antisymmetric-field-strength-to-zero-so-the-field-equation-forces-a-conserved-source"

zil_file_contract physlib.yangMillsCurrentConservation where
  promises "Conservation of the Abelian Yang-Mills source current. The inhomogeneous field equation, the divergence of the field strength equals the current, is consistent only if its source is conserved. A double sum over two indices of an antisymmetric family, where g of mu nu equals minus g of nu mu, vanishes. For the Abelian Maxwell field strength the current, the partial-mu divergence of F upper mu nu, has vanishing divergence: the partial-nu partial-mu of F upper mu nu is zero, because the second-derivative operator is symmetric in the two derivative indices, commuting mixed partials, while the field strength is antisymmetric, and a symmetric-times-antisymmetric contraction vanishes. So the field equation cannot be posited with an arbitrary source; the source is automatically conserved. Honest scope: the algebraic conservation identity from the pointwise-jet second-derivative data and the antisymmetry of the field strength; the non-Abelian covariant version, which additionally uses the Ricci identity, is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects []
  forbids_substitutes [
    "reading the Abelian partial-derivative current conservation as the non-Abelian covariant conservation D-nu D-mu F equals zero, which additionally requires the Ricci identity"
  ]
  witnessed_by [
    sum_sum_antisymm_zero,
    abelian_current_conservation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.yangMillsCurrentConservation
