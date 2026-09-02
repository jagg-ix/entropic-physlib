/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic

/-!
# A component-based exterior calculus on a frame

A self-contained exterior calculus for the tetrad/frame formalism — the differential-form machinery
(wedge `∧`, interior product `⌟`, exterior derivative `d`) that Weyl–Cartan gravity
(Babourova–Frolov 1998, Eqs. A.1–A.8, 3.2) is written in. Forms are components over a finite frame
index `ι`; the calculus is built up to the degrees the Cartan structure equations use.

* **§A — forms and the wedge product.** `OneForm`, `TwoForm` (`IsAntisym`); `wedge α β = α⊗β − β⊗α`,
  antisymmetric (`wedge_isAntisym`) and graded-anticommutative (`wedge_anticomm`).
* **§B — the interior product `ι_v = v ⌟`.** `interiorOne`, `interiorTwo`; the **anti-derivation
  Leibniz** `ι_v(α ∧ β) = (ι_v α) β − (ι_v β) α` (`interior_wedge_leibniz`) and nilpotency
  `ι_v ∘ ι_v = 0` on antisymmetric `2`-forms (`interior_interior_zero`).
* **§C — the exterior derivative `d`.** `extDeriv` (the antisymmetrized gradient
  `(dα)_ij = ∂_i α_j − ∂_j α_i`), antisymmetric (`extDeriv_isAntisym`); the **Poincaré `d² = 0`**
  `d(df) = 0` for a symmetric Hessian (`extDeriv_of_symmetric_hessian_zero`).
* **§D — the Weyl–Cartan application.** The **dilatonic field strength** `dQ` is the exterior
  derivative of the Weyl one-form (`dilatonicFieldStrength`), an antisymmetric closed `2`-form — the
  homothetic curvature `Rᵃ_α = ½ dQ` (Eq. A.8); the **Weyl force one-form** `ē_σ ⌟ dQ` is its interior
  product (Eq. 3.2), which vanishes for a vanishing field strength.

**Honest layering.** Everything here is proven from the component definitions: the wedge/interior
identities, the anti-derivation Leibniz, `d² = 0`. The exterior derivative is the algebraic
antisymmetrized gradient (a given component-derivative), not tied to a smooth-manifold `d`; that is the
level at which the tetrad-formalism Cartan equations operate.

## References

* H. Cartan, exterior differential calculus; Babourova–Frolov [`Babourova:1998ah`] Eqs. (A.1)–(A.8),
  (3.2) (the `⌟`, `∧`, `d` the paper uses).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ExteriorCalculusFrame

variable {ι : Type*}


/-- A **1-form** on the frame `ι` — a covector of components. -/
abbrev OneForm (ι : Type*) := ι → ℝ

/-- A **2-form** on the frame `ι` — a two-index component array (antisymmetric when it is a genuine
form, `IsAntisym`). -/
abbrev TwoForm (ι : Type*) := ι → ι → ℝ

/-- **Antisymmetry** `ω_ij = −ω_ji` — the defining property of a 2-form. -/
def IsAntisym (ω : TwoForm ι) : Prop := ∀ i j, ω i j = - ω j i

/-- **The wedge product of two 1-forms** `(α ∧ β)_ij = α_i β_j − α_j β_i`. -/
def wedge (α β : OneForm ι) : TwoForm ι := fun i j => α i * β j - α j * β i

/-- The wedge of two 1-forms is a genuine (antisymmetric) 2-form. -/
lemma wedge_isAntisym (α β : OneForm ι) : IsAntisym (wedge α β) := fun i j => by
  unfold wedge; ring

/-- **Graded anticommutativity** `α ∧ β = −(β ∧ α)`. -/
lemma wedge_anticomm (α β : OneForm ι) (i j : ι) : wedge α β i j = - wedge β α i j := by
  unfold wedge; ring


/-- **The interior product of a vector with a 1-form** `ι_v α = vⁱ α_i` — a scalar. -/
def interiorOne [Fintype ι] (v : ι → ℝ) (α : OneForm ι) : ℝ := ∑ i, v i * α i

/-- **The interior product of a vector with a 2-form** `(ι_v ω)_j = vⁱ ω_ij` — a 1-form. -/
def interiorTwo [Fintype ι] (v : ι → ℝ) (ω : TwoForm ι) : OneForm ι := fun j => ∑ i, v i * ω i j

/-- **The anti-derivation (graded Leibniz) rule for `⌟`**: `ι_v(α ∧ β) = (ι_v α) β − (ι_v β) α` — the
interior product is an anti-derivation over the wedge. -/
lemma interior_wedge_leibniz [Fintype ι] (v : ι → ℝ) (α β : OneForm ι) (j : ι) :
    interiorTwo v (wedge α β) j = interiorOne v α * β j - interiorOne v β * α j := by
  unfold interiorTwo interiorOne wedge
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Nilpotency of the interior product** `ι_v ∘ ι_v = 0` on any antisymmetric 2-form: the symmetric
`vⁱvʲ` contracted with the antisymmetric `ω_ij` vanishes. -/
lemma interior_interior_zero [Fintype ι] (v : ι → ℝ) (ω : TwoForm ι) (hanti : IsAntisym ω) :
    interiorOne v (interiorTwo v ω) = 0 := by
  unfold interiorOne interiorTwo
  simp_rw [Finset.mul_sum]
  have step : (∑ j, ∑ i, v j * (v i * ω i j)) = ∑ j, ∑ i, -(v i * (v j * ω j i)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hanti i j]; ring
  have step2 : (∑ j, ∑ i, -(v i * (v j * ω j i))) = -(∑ j, ∑ i, v j * (v i * ω i j)) := by
    simp only [Finset.sum_neg_distrib]; congr 1; exact Finset.sum_comm
  rw [step, step2] at *; linarith [step]


/-- **The exterior derivative of a 1-form** `(dα)_ij = ∂_i α_j − ∂_j α_i`, the antisymmetrization of a
given component gradient `∂α_ij`. -/
def extDeriv (gradAlpha : ι → ι → ℝ) : TwoForm ι := fun i j => gradAlpha i j - gradAlpha j i

/-- The exterior derivative is a genuine (antisymmetric) 2-form. -/
lemma extDeriv_isAntisym (gradAlpha : ι → ι → ℝ) : IsAntisym (extDeriv gradAlpha) := fun i j => by
  unfold extDeriv; ring

/-- **Poincaré `d² = 0`**: for a function with symmetric Hessian `∂_i ∂_j f = ∂_j ∂_i f`, the exterior
derivative of its differential vanishes — `d(df) = 0`. -/
lemma extDeriv_of_symmetric_hessian_zero (hess : ι → ι → ℝ) (hsym : ∀ i j, hess i j = hess j i)
    (i j : ι) : extDeriv hess i j = 0 := by
  unfold extDeriv; rw [hsym i j]; ring


/-- **The dilatonic field strength** `dQ` — the exterior derivative of the Weyl one-form `Q`
(Babourova–Frolov: the homothetic curvature `Rᵃ_α = ½ dQ`, Eq. A.8). -/
def dilatonicFieldStrength (gradQ : ι → ι → ℝ) : TwoForm ι := extDeriv gradQ

/-- The dilatonic field strength is an antisymmetric (Faraday-like) 2-form. -/
lemma dilatonicFieldStrength_isAntisym (gradQ : ι → ι → ℝ) :
    IsAntisym (dilatonicFieldStrength gradQ) := extDeriv_isAntisym gradQ

/-- **The Weyl force one-form** `ē_σ ⌟ dQ` — the interior product of the frame vector with the
dilatonic field strength (the Lorentz-like Weyl force of Eq. 3.2). -/
def weylForceForm [Fintype ι] (v : ι → ℝ) (gradQ : ι → ι → ℝ) : OneForm ι :=
  interiorTwo v (dilatonicFieldStrength gradQ)

/-- **The Weyl force vanishes when the field strength does** (`dQ = 0`, a metric/no-Weyl space): no
dilatonic field strength ⟹ no Weyl force — the exterior-calculus form of Corollary 3. -/
lemma weylForceForm_zero_of_no_fieldStrength [Fintype ι] (v : ι → ℝ) (gradQ : ι → ι → ℝ)
    (h : ∀ i j, dilatonicFieldStrength gradQ i j = 0) (j : ι) : weylForceForm v gradQ j = 0 := by
  unfold weylForceForm interiorTwo; simp [h]

end Physlib.QuantumMechanics.ComplexAction.ExteriorCalculusFrame
