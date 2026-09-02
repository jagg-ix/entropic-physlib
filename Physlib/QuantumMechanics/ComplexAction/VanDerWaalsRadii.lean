/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Van der Waals radii of elements: the geometric relations

S. S. Batsanov, *Van der Waals Radii of Elements*, Inorg. Mater. 37 (2001) 871, reviews the van der Waals
radius `R` (the periphery of an atom) against the covalent radius `r`. This formalizes the paper's
**derived** geometric and algebraic identities (the fitted electronegativity rule Eq. 10 is a
phenomenological ansatz and is not formalized):

* **§A — the radius ratio from the atomic-shell scaling (Eqs. 7–9).** with the effective-charge radii
  `r = a₀ n²/Z*` and `R = a₀(n+1)²/Z*`, the ratio is `R/r = ((n+1)/n)²`
  (`maxRadius_div_groundStateRadius`).
* **§B — the close-packing radius (Eqs. 11–12).** the overlap fraction `σ = (R²−r²)/(4R²)` and, at the
  maximal coordination `N_c = 12`, the packing sum `S̄ = 12σ = 1` forces `R² = (3/2) r²`
  (`closePacking_radiusSq_iff`), i.e. `R = √(3/2) r` (`closePacking_radius`).
* **§C — the overlap and atomic volumes (Eqs. 2, 13).** the shared lens volume of two atomic spheres
  `V = ⅔π(R−r)²(2R+r)` is the two-sphere lens at centre distance `2r` (`overlapVolume_eq_lens`), and the
  diamond atomic volume `V_a = ⅓π[4R³ − 4(R−r)²(2R+r)]` is the full sphere minus four caps
  (`atomicVolumeDiamond_eq_sphere_sub_caps`).
* **§D — the M–X bond radius (Eq. 5).** `R_M = (R_X² + d² − 2 d r_X)^{1/2}` (`bondRadiusM_sq`).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.VanDerWaalsRadii

open scoped Real


/-- **The covalent (minimal) radius** `r = a₀ n²/Z*` (Eq. 7): the atomic size for principal quantum
number `n` and effective nuclear charge `Z*`, `a₀` the Bohr radius. -/
noncomputable def groundStateRadius (a₀ Zeff n : ℝ) : ℝ := a₀ * n ^ 2 / Zeff

/-- **The van der Waals (maximal) radius** `R = a₀ (n+1)²/Z*` (Eq. 8): the periphery reaches the next
shell `n + 1`. -/
noncomputable def maxRadius (a₀ Zeff n : ℝ) : ℝ := a₀ * (n + 1) ^ 2 / Zeff

/-- **The radius ratio** `R/r = ((n+1)/n)²` (Eq. 9): the van der Waals radius exceeds the covalent radius
by the square of the shell ratio. -/
lemma maxRadius_div_groundStateRadius (a₀ Zeff n : ℝ)
    (ha : a₀ ≠ 0) (hZ : Zeff ≠ 0) (hn : n ≠ 0) :
    maxRadius a₀ Zeff n / groundStateRadius a₀ Zeff n = ((n + 1) / n) ^ 2 := by
  unfold maxRadius groundStateRadius
  field_simp


/-- **The overlap fraction** `σ = (R²−r²)/(4R²)` (Eq. 11): the fraction of a spherical section covered by
close packing at one contact. -/
noncomputable def sigmaOverlap (R r : ℝ) : ℝ := (R ^ 2 - r ^ 2) / (4 * R ^ 2)

/-- **The packing sum at maximal coordination** `S̄ = 12 σ` (Eq. 11 with `N_c = 12`). -/
noncomputable def packingSumFull (R r : ℝ) : ℝ := 12 * sigmaOverlap R r

/-- **Close packing fixes the radius ratio** `S̄ = 1 ↔ R² = (3/2) r²` (Eq. 12): requiring the packing sum
to saturate at `N_c = 12` pins the van der Waals radius to `√(3/2)` times the covalent radius. -/
lemma closePacking_radiusSq_iff (R r : ℝ) (hR : R ≠ 0) :
    packingSumFull R r = 1 ↔ R ^ 2 = 3 / 2 * r ^ 2 := by
  unfold packingSumFull sigmaOverlap
  rw [← mul_div_assoc, div_eq_iff (by positivity : (0 : ℝ) < 4 * R ^ 2).ne']
  constructor <;> intro h <;> nlinarith [h]

/-- **The close-packing radius** `R = √(3/2) r` (Eq. 12) for positive radii. -/
lemma closePacking_radius (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (h : packingSumFull R r = 1) : R = Real.sqrt (3 / 2) * r := by
  have hRsq : R ^ 2 = 3 / 2 * r ^ 2 := (closePacking_radiusSq_iff R r (ne_of_gt hR)).1 h
  rw [← Real.sqrt_sq hR.le, hRsq, Real.sqrt_mul (by norm_num), Real.sqrt_sq hr.le]


/-- **The shared overlap (lens) volume** of two atomic spheres, `V = ⅔π(R−r)²(2R+r)` (Eq. 2): the region
common to two van der Waals spheres of radius `R` whose centres are the bond length `2r` apart. -/
noncomputable def overlapVolume (R r : ℝ) : ℝ := 2 * π / 3 * (R - r) ^ 2 * (2 * R + r)

/-- **Eq. 2 is the two-sphere lens formula at centre distance `2r`**: the intersection volume of two equal
spheres of radius `R` at centre distance `d` is `π/12·(4R+d)(2R−d)²`; setting `d = 2r` gives Eq. 2. -/
lemma overlapVolume_eq_lens (R r : ℝ) :
    overlapVolume R r = π / 12 * (4 * R + 2 * r) * (2 * R - 2 * r) ^ 2 := by
  unfold overlapVolume
  ring

/-- **The atomic volume in the diamond structure** `V_a = ⅓π[4R³ − 4(R−r)²(2R+r)]` (Eq. 13). -/
noncomputable def atomicVolumeDiamond (R r : ℝ) : ℝ :=
  π / 3 * (4 * R ^ 3 - 4 * (R - r) ^ 2 * (2 * R + r))

/-- **The diamond atomic volume is the full sphere minus four caps** (Eq. 13): `V_a = 4/3·πR³ − 4·½V`,
where `V` is the shared overlap volume (Eq. 2) — each of the four tetrahedral bonds removes one cap
(half a lens) from the atomic sphere. -/
lemma atomicVolumeDiamond_eq_sphere_sub_caps (R r : ℝ) :
    atomicVolumeDiamond R r = 4 * π / 3 * R ^ 3 - 4 * (1 / 2 * overlapVolume R r) := by
  unfold atomicVolumeDiamond overlapVolume
  ring


/-- **The van der Waals radius of a metal from an M–X bond** `R_M = (R_X² + d² − 2 d r_X)^{1/2}` (Eq. 5):
from the geometry of the overlapping M and X spheres at internuclear distance `d`, with `r_X` the orbital
radius of `X`. -/
noncomputable def bondRadiusM (RX d rX : ℝ) : ℝ := Real.sqrt (RX ^ 2 + d ^ 2 - 2 * d * rX)

/-- **The squared M–X bond-radius relation** `R_M² = R_X² + d² − 2 d r_X` (Eq. 5), whenever the argument
is nonnegative. -/
lemma bondRadiusM_sq (RX d rX : ℝ) (h : 0 ≤ RX ^ 2 + d ^ 2 - 2 * d * rX) :
    bondRadiusM RX d rX ^ 2 = RX ^ 2 + d ^ 2 - 2 * d * rX := by
  unfold bondRadiusM
  exact Real.sq_sqrt h

end Physlib.QuantumMechanics.ComplexAction.VanDerWaalsRadii

end
