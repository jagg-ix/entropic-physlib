/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralWeylNetSymmetry
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Icosahedral rotations, the golden ratio, and the hyperbolic (Schmidt) continuation

This expands the icosahedral formalization (`IcosahedralWeylNetSymmetry`: `A₅` is the rotation
subgroup of Sorkin's `su(5)` Weyl group `S₅`) with the actual **rotations and operations** of the
icosahedral group, their golden-ratio geometry, and the continuation to the hyperbolic rapidity whose
`coth` is the entanglement **Schmidt number** — the "icosahedral hyperbolic Schmidt" synthesis.

Following McMullen's *Riemann surfaces, dynamics and hyperbolic geometry* (Harvard Math 275): the
regular dodecahedron gives `V − E + F = 20 − 30 + 12 = 2`, and identifying opposite faces yields the
Poincaré homology sphere `S³/2I` (binary icosahedral group `2I`, order `120`, the `ℤ/2` central
extension of `A₅`) and the **Seifert–Weber** hyperbolic manifold `ℍ³/Γ` from a hyperbolic
dodecahedron with dihedral angle `2π/5`, whose vertex link is the icosahedrally-tiled sphere. The
`2π/5` (pentagonal) angle is the golden-ratio angle of the `5`-fold rotation.

* **§A — the rotations (orders 2, 3, 5).** `icosaRot2`, `icosaRot3`, `icosaRot5` — the edge-, face-,
  and vertex-axis rotations, even permutations lying in `A₅` (`icosaRot5_mem`, …) with orders
  `2, 3, 5` (`icosaRot5_orderOf`, …). These are the generators of the `(2,3,5)` von Dyck group `A₅`.
* **§B — the golden ratio underlies the `5`-fold rotation.** `twiceCos_pi_div_five_eq_golden`
  (`2cos(π/5) = φ`), `cos_two_pi_div_five_eq_golden` (`cos(2π/5) = (φ−1)/2`),
  `fiveFold_rotation_trace_golden` (the rotation matrix's trace is `φ − 1 = 1/φ`), reusing
  `goldenRatio_sq` (`φ² = φ + 1`).
* **§C — the hyperbolic continuation.** The `5`-fold rotation is elliptic/orthogonal
  (`fiveFold_orthogonal`, `planeRotation_orthogonal`); its Nagao–Nielsen partner `planeBoost η` is
  the hyperbolic circulator (`boost_trace_two_cosh`), and the Wick contour `θ → iη`
  (`boost_cosh_eq_rotation_wick`) continues one into the other.
* **§D — the Schmidt tie.** `schmidtNumber_eq_boost_coth` — the entanglement Schmidt number
  `K = coth η` is the `cosh/sinh` ratio of the boost that continues the icosahedral rotation; and
  `fiveFold_cycles_su5_weights` — the `5`-fold rotation cyclically permutes the five `su(5)`
  fundamental weights `e_j ↦ e_{j+1}`. So the icosahedral rotation of the `su(5)` weight system
  continues to the hyperbolic rapidity of the Schmidt/entanglement sector.
* **§E — the formal proof.** `schmidtNumber_goldenRapidity` — the golden ratio *is* an
  entanglement Schmidt number `K = coth η_φ = φ` at the golden rapidity `η_φ = (3/2) log φ`; and
  `icosahedral_hyperbolic_schmidt` identifies it with the rotation invariant: `K = trace(5-fold) + 1`.

**Honest layering.** Proven: the orders/membership of the rotations; the golden-ratio identities;
the elliptic/hyperbolic matrices and their Wick relation; `K = coth η`; the `5`-fold weight cycle;
and the identity `K = coth((3/2) log φ) = φ`. Interpretive: the identification of *this* rapidity with
the muon-anomaly Schmidt rapidity, and the "`SU(5)` = icosahedral hyperbolic Schmidt" reading, are the
synthesis the proven pieces support.

## References

* C. McMullen, *Riemann surfaces, dynamics and hyperbolic geometry* (Harvard Math 275, 2024), §1
  (the dodecahedron, Poincaré homology sphere `S³/2I`, Seifert–Weber `ℍ³/Γ`). Icosahedral symmetry:
  the groups `I ≅ A₅` (order `60`) and `I_h ≅ A₅ × ℤ₂` (order `120`). Reuses
  `IcosahedralWeylNetSymmetry`/`SorkinSimplecticNetR4` (`IcosahedralGroup`, `affineWeightBasis`,
  `weyl_permutes_affineWeightBasis`), `LeviCivita.BoostRotationWickContour`/`TetradInvariant`
  (`planeRotation`, `planeBoost`, `boost_cosh_eq_rotation_wick`),
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification` (`schmidtNumber`), Mathlib (`goldenRatio`,
  `cos_pi_div_five`, `alternatingGroup`, `finRotate`).


-/

set_option autoImplicit false

open scoped goldenRatio

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationsHyperbolic

open Equiv Equiv.Perm Matrix
open Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BoostRotationWickContour
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification


/-- **The `5`-fold (vertex-axis) rotation** `icosaRot5` — the cyclic permutation `i ↦ i + 1`. -/
def icosaRot5 : Equiv.Perm (Fin 5) := finRotate 5

/-- **The `3`-fold (face-axis) rotation** `icosaRot3` — the `3`-cycle `(0 1 2)`. -/
def icosaRot3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- **The `2`-fold (edge-axis) rotation** `icosaRot2` — the double transposition `(0 1)(2 3)`. -/
def icosaRot2 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

lemma icosaRot5_mem : icosaRot5 ∈ alternatingGroup (Fin 5) := by
  rw [mem_alternatingGroup]; decide

lemma icosaRot3_mem : icosaRot3 ∈ alternatingGroup (Fin 5) := by
  rw [mem_alternatingGroup]; decide

lemma icosaRot2_mem : icosaRot2 ∈ alternatingGroup (Fin 5) := by
  rw [mem_alternatingGroup]; decide

/-- **[Order `5`]** the vertex-axis rotation is a `5`-fold rotation. -/
lemma icosaRot5_orderOf : orderOf icosaRot5 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- **[Order `3`]** the face-axis rotation is a `3`-fold rotation. -/
lemma icosaRot3_orderOf : orderOf icosaRot3 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- **[Order `2`]** the edge-axis rotation is a `2`-fold rotation. The three orders `{2,3,5}` are the
exponents of the `(2,3,5)` von Dyck (triangle) group, whose orientation-preserving part is `A₅`. -/
lemma icosaRot2_orderOf : orderOf icosaRot2 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- The `5`-fold rotation as an element of the icosahedral group `A₅`. -/
def icosaRot5Elt : IcosahedralGroup := ⟨icosaRot5, icosaRot5_mem⟩

/-- The `5`-fold rotation is the cyclic shift `i ↦ i + 1`. -/
lemma icosaRot5_apply (j : Fin 5) : icosaRot5 j = j + 1 := finRotate_apply j


/-- **`2 cos(π/5) = φ`**: the pentagonal (dihedral) angle is the golden angle. -/
lemma twiceCos_pi_div_five_eq_golden : 2 * Real.cos (Real.pi / 5) = Real.goldenRatio := by
  rw [Real.cos_pi_div_five, Real.goldenRatio]; ring

/-- **`cos(2π/5) = (φ − 1)/2`**: the `5`-fold rotation angle's cosine, from the double-angle formula. -/
lemma cos_two_pi_div_five_eq_golden :
    Real.cos (2 * Real.pi / 5) = (Real.goldenRatio - 1) / 2 := by
  have h : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five, Real.goldenRatio]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)]; ring

/-- **The `5`-fold rotation matrix has trace `φ − 1 = 1/φ`.** `planeRotation θ` has trace `2 cos θ`;
at the icosahedral angle `θ = 2π/5` this is the golden ratio minus one — the rotation is *elliptic*
(`|trace| < 2`), carrying the pentagonal golden-ratio geometry. -/
lemma fiveFold_rotation_trace_golden :
    (planeRotation (2 * Real.pi / 5)).trace = Real.goldenRatio - 1 := by
  have ht : (planeRotation (2 * Real.pi / 5)).trace = 2 * Real.cos (2 * Real.pi / 5) := by
    simp [planeRotation, Matrix.trace_fin_two]; ring
  rw [ht, cos_two_pi_div_five_eq_golden]; ring

/-- The golden ratio is self-similar: `φ² = φ + 1` (restating `goldenRatio_sq`, the defining relation
of the `5`-fold/pentagonal geometry). -/
lemma goldenRatio_self_similar : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq


/-- **The `5`-fold rotation is elliptic (orthogonal)** — an `SO(2)` circulator preserving `x² + y²`
(reusing `planeRotation_orthogonal`). -/
lemma fiveFold_orthogonal :
    (planeRotation (2 * Real.pi / 5))ᵀ * planeRotation (2 * Real.pi / 5) = 1 :=
  planeRotation_orthogonal _

/-- **The boost circulator has trace `2 cosh η`** — the hyperbolic partner of the rotation, with
`|trace| > 2` (non-compact `SO(1,1)`), the continuation of the elliptic `5`-fold rotation. -/
lemma boost_trace_two_cosh (η : ℝ) : (planeBoost η).trace = 2 * Real.cosh η := by
  simp [planeBoost, Matrix.trace_fin_two]; ring

/-- **The Wick contour `θ → iη` continues the rotation into the boost**: the boost's `cosh` is the
rotation's `cos` at imaginary angle (reusing `boost_cosh_eq_rotation_wick`). Applied at the `5`-fold
angle, the elliptic icosahedral rotation becomes the hyperbolic Schmidt boost. -/
lemma fiveFold_wick_to_boost (η : ℝ) :
    Complex.cos (Physlib.QFT.PathIntegral.wickRotateInv η) = (Real.cosh η : ℂ) :=
  boost_cosh_eq_rotation_wick η


/-- **The Schmidt number is the boost's `coth`**: `K = cosh η / sinh η` is the ratio of the diagonal to
the (negated) off-diagonal entry of `planeBoost η` — the hyperbolic circulator continuing the
icosahedral rotation. So the entanglement Schmidt number `K = coth η_eff` of
`SchmidtRapidityHyperbolicUnification` is read off the boost that the `5`-fold rotation continues to. -/
lemma schmidtNumber_eq_boost_coth (η : ℝ) :
    schmidtNumber η = planeBoost η 0 0 / (- planeBoost η 0 1) := by
  unfold schmidtNumber; simp [planeBoost]

/-- **The `5`-fold rotation cyclically permutes the five `su(5)` fundamental weights**: `g · e_j =
e_{σ j}` with `σ = icosaRot5` the cyclic shift, so `e_0 ↦ e_1 ↦ e_2 ↦ e_3 ↦ e_4 ↦ e_0` (reusing
`weyl_permutes_affineWeightBasis`). This is the icosahedral rotation acting on the `SU(5)` weight
system / the vertices of Sorkin's `R⁴` net. -/
lemma fiveFold_cycles_su5_weights (j : Fin 5) :
    (fun i => affineWeightBasis 5 j (icosaRot5.symm i)) = affineWeightBasis 5 (icosaRot5 j) :=
  weyl_permutes_affineWeightBasis icosaRot5 j

/-!

Assembling the chain, the golden ratio of the icosahedral `5`-fold rotation is *itself* an
entanglement Schmidt number, at the **golden rapidity** `η_φ = (3/2) log φ`: since
`e^{2η_φ} = φ³ = 2φ + 1` and `coth η = (e^{2η}+1)/(e^{2η}−1)`, one gets
`coth η_φ = (φ³+1)/(φ³−1) = (2φ+2)/(2φ) = (φ+1)/φ = φ²/φ = φ` (using `φ² = φ + 1`). So `K = φ`. -/

/-- **The golden rapidity** `η_φ = (3/2) log φ` — the rapidity whose entanglement Schmidt number is
the golden ratio. -/
noncomputable def goldenRapidity : ℝ := (3 / 2) * Real.log Real.goldenRatio

/-- **The golden ratio is an entanglement Schmidt number.** `K = coth η_φ = φ` at the golden rapidity:
the golden ratio carried by the icosahedral `5`-fold rotation (`fiveFold_rotation_trace_golden`) is
literally a bipartite Schmidt number of `SchmidtRapidityHyperbolicUnification`. This is the proven
core of the "icosahedral hyperbolic Schmidt" synthesis. -/
lemma schmidtNumber_goldenRapidity : schmidtNumber goldenRapidity = Real.goldenRatio := by
  have hφ : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  set η := goldenRapidity with hη
  set u := Real.exp η with hu
  have hupos : 0 < u := Real.exp_pos η
  have hu2 : u ^ 2 = Real.goldenRatio ^ 3 := by
    rw [hu, sq, ← Real.exp_add]
    have h2 : η + η = Real.log Real.goldenRatio + Real.log Real.goldenRatio
        + Real.log Real.goldenRatio := by rw [hη, goldenRapidity]; ring
    rw [h2, Real.exp_add, Real.exp_add, Real.exp_log hφ]; ring
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by nlinarith [hsq]
  have hu2' : u ^ 2 = 2 * Real.goldenRatio + 1 := by rw [hu2, hcube]
  have hugt1 : 1 < u := by nlinarith [hu2', hφ, hupos]
  have hune : u ≠ 0 := ne_of_gt hupos
  have hi : u⁻¹ < 1 := (inv_lt_one₀ hupos).mpr hugt1
  have hd1 : u - u⁻¹ ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hi hugt1))
  have hd2 : u ^ 2 - 1 ≠ 0 := ne_of_gt (by rw [hu2']; linarith [hφ])
  rw [schmidtNumber, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, ← hu]
  have key : (u + u⁻¹) / 2 / ((u - u⁻¹) / 2) = (u ^ 2 + 1) / (u ^ 2 - 1) := by field_simp
  rw [key, hu2',
    div_eq_iff (ne_of_gt (show (0 : ℝ) < 2 * Real.goldenRatio + 1 - 1 by linarith [hφ]))]
  nlinarith [hsq]

/-- **The icosahedral–hyperbolic–Schmidt identity.** The Schmidt number at the golden rapidity equals
the `5`-fold icosahedral rotation's trace plus one: `K = coth η_φ = (planeRotation(2π/5)).trace + 1`.
The elliptic rotation invariant `trace = φ − 1` (§B) and the hyperbolic Schmidt number `K = φ` (§E)
are the two faces of the same golden ratio — the formal identification of the icosahedral rotation of the
`su(5)` weight system to the hyperbolic entanglement sector. -/
lemma icosahedral_hyperbolic_schmidt :
    schmidtNumber goldenRapidity = (planeRotation (2 * Real.pi / 5)).trace + 1 := by
  rw [schmidtNumber_goldenRapidity, fiveFold_rotation_trace_golden]; ring

end Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationsHyperbolic
