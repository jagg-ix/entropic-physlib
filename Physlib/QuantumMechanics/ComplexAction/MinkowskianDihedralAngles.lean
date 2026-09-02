/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality

/-!
# Angles in the Minkowskian plane and the complexified dihedral angle

The lemmas and equations of Asante–Dittrich–Padua-Argüelles §II.A (angles in the Minkowskian plane)
and §II.B (the complexified dihedral angle), built on the Wick-rotated inner product
`ComplexReggeActionCausality.wickInner`.

* **§A — the signed squared edge lengths** (Eq. 2.2): `s_a = a⋆a`, `s_b = b⋆b`,
  `s_c = a⋆a + b⋆b − 2 a⋆b` — the opposite edge `(a−b)⋆(a−b)` (`wickEdgeSqOpposite_eq`).
* **§B — the dihedral-angle argument** (Eqs. 2.3, 2.5). The numerator `½(s_a+s_b−s_c) = a⋆b`
  (`dihedralNumerator_eq_inner`); the discriminant `¼(s_a²+s_b²+s_c²) − ½(s_a s_b + s_b s_c + s_c s_a)`
  equals both the **Heron form** `(a⋆b)² − s_a s_b` (`dihedralDiscriminant_heron`) and the vector
  discriminant `wickDiscriminant` (`dihedralDiscriminant_eq_wickDiscriminant`) — so the edge-length
  and vector definitions of the angle agree.
* **§C — the complexified dihedral angle** (Eqs. 2.5, 2.10). `dihedralAngle = −i log((num + √disc)/
  (√s_a √s_b))` (parametrized by the branch roots, as the paper's §II.B branch discussion requires);
  the edge-length form `dihedralAngleEdge` equals the vector form
  (`dihedralAngleEdge_eq_dihedralAngle`).
* **§D — Euclidean and Lorentzian angles** (Eq. 2.1). The Euclidean angle `ψ_E = arccos` of the
  normalized inner product, the Lorentzian boost `ψ_L = arccosh`, and the `∓iπ/2` light-ray-crossing
  contribution (`ComplexReggeActionCausality.crossingImaginary`).

**Honest layering.** Proven: the signed-edge-length relation, the numerator/discriminant identities
(the vector ↔ edge-length agreement, the Heron form), and the equality of the two angle forms.
Interpretive: the branch structure of `Complex.log`/`√` (the `θ⁺ = −θ⁻` versions, Lemma II.1's limits)
is carried by the explicit branch roots, not by a full principal-branch continuation.

## References

* S. K. Asante, B. Dittrich, J. Padua-Argüelles, "Complex actions and causality violations",
  arXiv:2112.15387 [`Asante:2021zzh`], §II.A–B, Eqs. (2.1)–(2.5), (2.10). Reuses
  `ComplexReggeActionCausality` (`wickInner`, `wickDiscriminant`).


-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MinkowskianDihedralAngles

open Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality


/-- **The signed squared edge length** `s_a = a ⋆ a` (positive space-like, negative time-like, null
zero) — the Wick-rotated squared norm. -/
noncomputable def wickEdgeSq (φ : ℝ) (a : Fin 2 → ℂ) : ℂ := wickInner φ a a

/-- **The opposite (third) squared edge length** `s_c = (a − b) ⋆ (a − b)` of the triangle spanned by
`a` and `b`. -/
noncomputable def wickEdgeSqOpposite (φ : ℝ) (a b : Fin 2 → ℂ) : ℂ :=
  wickInner φ (fun i => a i - b i) (fun i => a i - b i)

/-- **The signed-edge-length relation** (Eq. 2.2): `s_c = s_a + s_b − 2 a⋆b`. -/
lemma wickEdgeSqOpposite_eq (φ : ℝ) (a b : Fin 2 → ℂ) :
    wickEdgeSqOpposite φ a b = wickEdgeSq φ a + wickEdgeSq φ b - 2 * wickInner φ a b := by
  unfold wickEdgeSqOpposite wickEdgeSq wickInner; simp only []; ring


/-- **The numerator of the dihedral-angle argument** `½(s_a + s_b − s_c)` (Eq. 2.3). -/
noncomputable def dihedralNumerator (sa sb sc : ℂ) : ℂ := (1 / 2) * (sa + sb - sc)

/-- **The discriminant under the square root** `¼(s_a²+s_b²+s_c²) − ½(s_a s_b + s_b s_c + s_c s_a)`
(Eq. 2.3) — the Heron-type area function. -/
noncomputable def dihedralDiscriminant (sa sb sc : ℂ) : ℂ :=
  (1 / 4) * (sa ^ 2 + sb ^ 2 + sc ^ 2) - (1 / 2) * (sa * sb + sb * sc + sc * sa)

/-- **The numerator is the inner product** `½(s_a + s_b − s_c) = a⋆b`. -/
lemma dihedralNumerator_eq_inner (φ : ℝ) (a b : Fin 2 → ℂ) :
    dihedralNumerator (wickEdgeSq φ a) (wickEdgeSq φ b) (wickEdgeSqOpposite φ a b)
      = wickInner φ a b := by
  rw [wickEdgeSqOpposite_eq]; unfold dihedralNumerator wickEdgeSq; ring

/-- **The discriminant in Heron form** `= (a⋆b)² − s_a s_b` when `s_c = s_a + s_b − 2 a⋆b` (Eq. 2.3). -/
lemma dihedralDiscriminant_heron (sa sb sab : ℂ) :
    dihedralDiscriminant sa sb (sa + sb - 2 * sab) = sab ^ 2 - sa * sb := by
  unfold dihedralDiscriminant; ring

/-- **The edge-length discriminant is the vector discriminant** (Eqs. 2.3 ↔ 2.14): the two definitions
of the angle — from edge lengths and from vectors — have the same square-root argument. -/
lemma dihedralDiscriminant_eq_wickDiscriminant (φ : ℝ) (a b : Fin 2 → ℂ) :
    dihedralDiscriminant (wickEdgeSq φ a) (wickEdgeSq φ b) (wickEdgeSqOpposite φ a b)
      = wickDiscriminant φ a b := by
  rw [wickEdgeSqOpposite_eq, dihedralDiscriminant_heron]
  unfold wickDiscriminant wickEdgeSq; ring


/-- **The complexified dihedral angle** `θ = −i log((num + √disc)/(√s_a √s_b))`
(Asante–Dittrich–Padua-Argüelles Eqs. 2.5, 2.10), parametrized by the chosen branch roots `sqrtDisc`,
`sqrtSa`, `sqrtSb` (the branch choice of §II.B). -/
noncomputable def dihedralAngle (num sqrtDisc sqrtSa sqrtSb : ℂ) : ℂ :=
  -Complex.I * Complex.log ((num + sqrtDisc) / (sqrtSa * sqrtSb))

/-- **The edge-length and vector forms of the angle agree** (Eqs. 2.5 ↔ 2.10): built from
`½(s_a+s_b−s_c) = a⋆b` and the shared discriminant, the dihedral angle is the same whether written in
edge lengths or in vector inner products (for any matching branch roots). -/
lemma dihedralAngleEdge_eq_dihedralAngle (φ : ℝ) (a b : Fin 2 → ℂ) (sqrtDisc sqrtSa sqrtSb : ℂ) :
    dihedralAngle
        (dihedralNumerator (wickEdgeSq φ a) (wickEdgeSq φ b) (wickEdgeSqOpposite φ a b))
        sqrtDisc sqrtSa sqrtSb
      = dihedralAngle (wickInner φ a b) sqrtDisc sqrtSa sqrtSb := by
  rw [dihedralNumerator_eq_inner]


/-- **The Euclidean angle** `ψ_E = arccos(â·b̂)` between two real vectors (Eq. 2.1, Euclidean case),
valued in `[0, π]`. -/
noncomputable def euclideanAngle (cosVal : ℝ) : ℝ := Real.arccos cosVal

/-- **The Lorentzian boost angle** `ψ_L = cosh⁻¹(â·b̂) = log(x + √(x²−1))` for two vectors in the same
quadrant (Eq. 2.1, `cosh⁻¹` case), the real rapidity. -/
noncomputable def lorentzianBoostAngle (coshVal : ℝ) : ℝ :=
  Real.log (coshVal + Real.sqrt (coshVal ^ 2 - 1))

/-- **The Euclidean angle lies in `[0, π]`** (Eq. 2.1). -/
lemma euclideanAngle_mem (cosVal : ℝ) : euclideanAngle cosVal ∈ Set.Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg cosVal, Real.arccos_le_pi cosVal⟩

/-- **A light-ray crossing adds `∓iπ/2` to the Lorentzian angle** (Eq. 2.1): the Minkowskian angle of
two vectors in neighbouring quadrants is `sinh⁻¹(â·b̂) ∓ iπ/2`, its imaginary part the crossing
contribution `crossingImaginary = π/2`. -/
lemma lorentzianAngle_crossing_imaginary (sinhVal : ℝ) :
    (((sinhVal : ℂ)) - Complex.I * (crossingImaginary : ℝ)).im = - crossingImaginary := by
  simp

end Physlib.QuantumMechanics.ComplexAction.MinkowskianDihedralAngles
