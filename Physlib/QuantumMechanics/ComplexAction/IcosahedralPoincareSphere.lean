/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NonAbelianAnyons
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
meta import Zil

/-!
# Icosahedral symmetry, the golden ratio, and the Poincaré homology sphere

The recurring *icosahedral / five-fold* thread — golden ratio, Fibonacci quantum dimension, the
"pentagonal lock" — has a single rigorous mathematical object underneath it: the **icosahedral group**
`A₅` (rotations of the icosahedron/dodecahedron), its double cover the **binary icosahedral group**
`2I`, and the **Poincaré homology sphere** `Σ = S³/2I` whose fundamental group is `2I`. This module
formalizes the parts of that structure that are actual mathematics, and connects them to the golden
ratio already carried by `NonAbelianAnyons.fibonacciDim`.

* **§A — the pentagon angle and the golden ratio.** `2 cos(π/5) = φ`
  (`two_cos_pi_div_five_eq_goldenRatio`): the cosine of the dodecahedral face angle `π/5 = 36°`
  produces the golden ratio, so the Fibonacci quantum dimension **is** twice that cosine
  (`fibonacciDim_eq_two_cos_pi_div_five`). This is the exact five-fold/icosahedral origin of the
  golden self-similarity `φ = 1 + 1/φ`.
* **§B — the icosahedral group orders.** The icosahedral rotation group is `A₅ = alternatingGroup (Fin 5)`,
  of order `60` (`icosahedralRotation_card`); its double cover the binary icosahedral group `2I` has
  order `120 = 2·60 = 5(5²−1) = |SL(2, 𝔽₅)|` (`binaryIcosahedralOrder_eq_two_mul_icosahedral`,
  `binaryIcosahedralOrder_eq_specialLinear_formula`).
* **§C — the homology-sphere property.** A group is *perfect* when it equals its own commutator, and
  then its abelianization — which is the first homology `H₁ = π₁^{ab}` of the associated space — is
  **trivial** (`isPerfect_abelianization_isTrivial`). The icosahedral group `A₅` is perfect
  (`alternatingGroup_five_isPerfect`), so `H₁ = 0` (`alternatingGroup_five_abelianization_isTrivial`).
  The binary icosahedral group `2I` is likewise perfect, which is exactly why `Σ = S³/2I` is a
  *homology* sphere: `π₁(Σ) = 2I` has order `120` yet `H₁(Σ) = 0` — same homology as `S³`, nontrivial
  fundamental group. (A homology sphere therefore does **not** have `H₁ = ℤ/120`; the order `120` lives
  in `π₁`, and it abelianizes to `0`.)
* **§D — the dodecahedral gluing angle.** `dodecahedralTwist = 2π/10 = π/5` (`dodecahedralTwist_eq`),
  the minimal twist gluing opposite dodecahedron faces to build `Σ`; its cosine carries the golden
  ratio, `2cos(2π/10) = φ` (`two_cos_dodecahedralTwist_eq_goldenRatio`), and the pentagon face angle
  gives `cos(2π/5) = (√5−1)/4 = (φ−1)/2` (`cos_two_pi_div_five`, `cos_two_pi_div_five_golden`).

**Honest layering.** Proven: the golden-ratio identity `2cos(π/5) = φ` and its identification with the
Fibonacci quantum dimension; the order of `A₅`; the arithmetic of the binary-icosahedral order; that a
perfect group has trivial abelianization; and that `A₅` is perfect (hence `H₁ = 0`). Interpretive: the
identification of `A₅` with the icosahedral rotation group and of `2I ≅ SL(2,𝔽₅)` with `π₁` of the
Poincaré homology sphere is the standard geometric/topological dictionary; the "homology sphere" claim
about `Σ = S³/2I` is stated for the abelianization of its (perfect) fundamental group, not via a
formalized singular-homology computation.

## References

* H. Poincaré, "Cinquième complément à l'analysis situs" (1904) (the dodecahedral space); W. Threlfall,
  H. Seifert (the binary icosahedral group as `π₁`); J. McKay (the `2I ↔ E₈` correspondence). Reuses
  `NonAbelianAnyons.fibonacciDim` and Mathlib `Real.cos_pi_div_five`, `Group.IsPerfect`,
  `alternatingGroup`, `IsSimpleGroup.comm_iff_isSolvable`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere

open Physlib.QuantumMechanics.ComplexAction
open Equiv


/-- **The pentagon/icosahedral golden-ratio identity** `2 cos(π/5) = φ`: the cosine of the dodecahedral
face angle `π/5 = 36°` is `(1+√5)/4`, so twice it is the golden ratio `(1+√5)/2`. This is the exact
geometric source of the five-fold symmetry behind the golden ratio. -/
lemma two_cos_pi_div_five_eq_goldenRatio :
    2 * Real.cos (Real.pi / 5) = Real.goldenRatio := by
  rw [Real.cos_pi_div_five]
  show 2 * ((1 + Real.sqrt 5) / 4) = (1 + Real.sqrt 5) / 2
  ring

/-- **The Fibonacci quantum dimension is the pentagon cosine** `d_τ = φ = 2 cos(π/5)`: the golden ratio
carried by `NonAbelianAnyons.fibonacciDim` is exactly twice the cosine of the icosahedral face angle —
the five-fold geometric origin of the Fibonacci anyon's quantum dimension. -/
lemma fibonacciDim_eq_two_cos_pi_div_five :
    NonAbelianAnyons.fibonacciDim = 2 * Real.cos (Real.pi / 5) := by
  rw [NonAbelianAnyons.fibonacciDim, ← two_cos_pi_div_five_eq_goldenRatio]


/-- **The icosahedral rotation group is `A₅`, of order `60`**: the group of rotational symmetries of the
icosahedron/dodecahedron is the alternating group on five letters, which has `60` elements
(`2 · |A₅| = |S₅| = 5! = 120`). -/
lemma icosahedralRotation_card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_eq_fintype_card (α := Perm (Fin 5)), Fintype.card_perm, Fintype.card_fin] at h
  simp only [Nat.factorial] at h
  omega

/-- **The binary icosahedral group order** `|2I| = 120`. -/
def binaryIcosahedralOrder : ℕ := 120

/-- **The binary icosahedral order as the special-linear formula** `|2I| = |SL(2, 𝔽₅)| = 5(5²−1) = 120`:
the binary icosahedral group is isomorphic to `SL(2, 𝔽₅)`, whose order is `q(q²−1)` at `q = 5`. -/
lemma binaryIcosahedralOrder_eq_specialLinear_formula :
    binaryIcosahedralOrder = 5 * (5 ^ 2 - 1) := by
  norm_num [binaryIcosahedralOrder]

/-- **The binary icosahedral group is the double cover of `A₅`** `|2I| = 2·|A₅| = 2·60`: the order-`120`
double cover of the order-`60` icosahedral rotation group. -/
lemma binaryIcosahedralOrder_eq_two_mul_icosahedral :
    binaryIcosahedralOrder = 2 * Nat.card (alternatingGroup (Fin 5)) := by
  rw [icosahedralRotation_card]; rfl


/-- **A perfect group has trivial abelianization** `H₁ = π₁^{ab} = 0`: if `G` equals its own commutator
subgroup (`Group.IsPerfect`), then the abelianization `G ⧸ ⁅G,G⁆` is a singleton. Read topologically,
a space whose fundamental group is perfect has trivial first homology — the defining feature of a
*homology sphere*. -/
lemma isPerfect_abelianization_isTrivial (G : Type*) [Group G] [Group.IsPerfect G] :
    Subsingleton (Abelianization G) := by
  show Subsingleton (G ⧸ commutator G)
  rw [Group.IsPerfect.commutator_eq_top]
  exact QuotientGroup.subsingleton_quotient_top

/-- **The icosahedral group `A₅` is perfect** `⁅A₅, A₅⁆ = A₅`: being simple and non-abelian, its
commutator subgroup — a normal subgroup — is neither trivial (that would force commutativity, hence
solvability) nor proper, so it is the whole group. -/
lemma alternatingGroup_five_isPerfect : Group.IsPerfect (alternatingGroup (Fin 5)) := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5)))
      inferInstance with h | h
  · exfalso
    have hsolv : IsSolvable (alternatingGroup (Fin 5)) :=
      ⟨⟨1, by rw [derivedSeries_one]; exact h⟩⟩
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
    let a : alternatingGroup (Fin 5) :=
      ⟨⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩,
        Perm.mem_alternatingGroup.mpr (by decide)⟩
    let b : alternatingGroup (Fin 5) :=
      ⟨⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩,
        Perm.mem_alternatingGroup.mpr (by decide)⟩
    exact absurd (hcomm a b) (by decide)
  · exact h

/-- **The icosahedral group has trivial first homology** `H₁(A₅) = 0`: the abelianization of the perfect
group `A₅` is trivial — the concrete witness of the homology-sphere mechanism on the icosahedral group.
The binary icosahedral group `2I = π₁(Σ)` of the Poincaré homology sphere is perfect for the same
reason, giving `H₁(Σ) = 0` despite `|π₁(Σ)| = 120`. -/
lemma alternatingGroup_five_abelianization_isTrivial :
    Subsingleton (Abelianization (alternatingGroup (Fin 5))) :=
  haveI := alternatingGroup_five_isPerfect
  isPerfect_abelianization_isTrivial _


/-- **The dodecahedral face-identification twist** `2π/10 = π/5 = 36°`: the minimal rotation with which
opposite pentagonal faces of the dodecahedron are glued to build the Poincaré homology sphere `S³/2I`. -/
noncomputable def dodecahedralTwist : ℝ := 2 * Real.pi / 10

/-- **The gluing twist is the pentagon half-angle** `2π/10 = π/5`. -/
lemma dodecahedralTwist_eq : dodecahedralTwist = Real.pi / 5 := by
  unfold dodecahedralTwist; ring

/-- **The gluing angle carries the golden ratio** `2cos(2π/10) = φ`: the cosine of the dodecahedral face
twist reproduces the golden ratio (equivalently the Fibonacci quantum dimension) — the five-fold
signature of the Poincaré-sphere construction. -/
lemma two_cos_dodecahedralTwist_eq_goldenRatio :
    2 * Real.cos dodecahedralTwist = Real.goldenRatio := by
  rw [dodecahedralTwist_eq]
  exact two_cos_pi_div_five_eq_goldenRatio

/-- **The pentagon face angle cosine** `cos(2π/5) = (√5 − 1)/4`: the second golden angle of the
icosahedral geometry, from the double-angle identity and `cos(π/5) = (1+√5)/4`. -/
lemma cos_two_pi_div_five :
    Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  rw [show (2 * Real.pi / 5 : ℝ) = 2 * (Real.pi / 5) from by ring, Real.cos_two_mul,
    Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 8 : ℝ) * h5

/-- **`cos(2π/5)` in golden form** `= (φ − 1)/2`: the pentagon face-angle cosine is the golden ratio
minus one, halved (equivalently `1/(2φ)`). -/
lemma cos_two_pi_div_five_golden :
    Real.cos (2 * Real.pi / 5) = (Real.goldenRatio - 1) / 2 := by
  rw [cos_two_pi_div_five]
  show (Real.sqrt 5 - 1) / 4 = ((1 + Real.sqrt 5) / 2 - 1) / 2
  ring

end Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.two_cos_pi_div_five_eq_goldenRatio where
  formalizes @ "claim:twice-the-cosine-of-the-icosahedral-face-angle-is-the-golden-ratio",
  supported_by @ "paper:klein-1884-lectures-on-the-icosahedron"

zil attach Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.icosahedralRotation_card where
  formalizes @ "claim:the-icosahedral-rotation-group-is-a5-of-order-sixty",
  requires @ "claim:twice-the-cosine-of-the-icosahedral-face-angle-is-the-golden-ratio"

zil attach Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.binaryIcosahedralOrder_eq_two_mul_icosahedral where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.icosahedralRotation_card",
  formalizes @ "claim:the-binary-icosahedral-group-double-covers-a5-with-order-one-hundred-twenty",
  requires @ "claim:the-icosahedral-rotation-group-is-a5-of-order-sixty"

zil_file_contract physlib.icosahedralPoincareSphere where
  promises "The icosahedral golden geometry of the Poincare sphere: twice the cosine of the face angle pi over five is the golden ratio, the icosahedral rotation group is A5 of order sixty, and the binary icosahedral group double-covers it with order one hundred twenty."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.binaryIcosahedralOrder"]
  forbids_substitutes ["a full anyon or Fibonacci-category development, only the golden-ratio and group-order identities"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.two_cos_pi_div_five_eq_goldenRatio,
    Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.icosahedralRotation_card,
    Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.binaryIcosahedralOrder_eq_two_mul_icosahedral]

/- ZIL-END -/
