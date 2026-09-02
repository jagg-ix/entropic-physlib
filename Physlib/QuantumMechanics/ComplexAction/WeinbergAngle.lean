/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor

/-!
# The weak mixing (Weinberg) angle `θ_W`

The weak mixing angle rotates the neutral `SU(2)_L × U(1)_Y` gauge fields `(W³, B)` into the physical
photon and `Z`. It is fixed by the two gauge couplings `g` (of `SU(2)_L`) and `g'` (of `U(1)_Y`):
`cos θ_W = g/√(g²+g'²)`, `sin θ_W = g'/√(g²+g'²)`, `tan θ_W = g'/g`.

* **§A — the angle from the couplings.** `cosWeinberg`, `sinWeinberg`, `tanWeinberg`;
  `sinSq_add_cosSq` (`sin²+cos² = 1`), `tan_eq_sin_div_cos`.
* **§B — the electric charge.** `electricCharge` `e = g sin θ_W = g' cos θ_W` (`electricCharge_symm`),
  and the coupling relation `1/e² = 1/g² + 1/g'²` (`inv_electricCharge_sq`).
* **§C — the photon/`Z` mixing.** `neutralMixing` — the orthogonal rotation
  `(A, Z) = R(θ_W)(B, W³)` (`neutralMixing_orthogonal`).
* **§D — the `ρ` parameter.** `rhoParameter`; the tree-level mass relation `m_W = m_Z cos θ_W` gives
  `ρ = 1` (`rho_eq_one`).
* **§E — the `SU(5)` GUT prediction `sin²θ_W = 3/8`.** At the unification scale
  `sin²θ_W = Tr(T₃²)/Tr(Q²)` over a complete representation; on the `SU(5)` `5̄`
  (`weakIsospin3`, reusing `su5AntifundCharge`) this is `(1/2)/(4/3) = 3/8`
  (`su5_sin2Weinberg_eq_three_eighths`) — the celebrated Georgi–Quinn–Weinberg result.

**Honest layering.** Proven: the trigonometric/charge identities from `g, g'`; orthogonality of the
mixing; `ρ = 1` from the mass relation; the `3/8` trace ratio on the `5̄`. Interpretive: the physical
identification (that the measured low-energy `sin²θ_W ≈ 0.23` runs from `3/8` at `M_GUT`) is the
physics the trace identity supports; the renormalization-group running is not formalized here.

## References

* S. Weinberg, "A Model of Leptons", Phys. Rev. Lett. **19**, 1264 (1967); H. Georgi, H. Quinn,
  S. Weinberg, "Hierarchy of Interactions in Unified Gauge Theories", Phys. Rev. Lett. **33**, 451
  (1974) — `sin²θ_W = 3/8` at unification. Reuses `Su5ChargeQuantizationCartanTensor`
  (`su5AntifundCharge`, the `SU(5)` charge/weight structure).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WeinbergAngle

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor


/-- **`cos θ_W = g/√(g²+g'²)`**, from the `SU(2)_L` coupling `g` and `U(1)_Y` coupling `g'`. -/
noncomputable def cosWeinberg (g g' : ℝ) : ℝ := g / Real.sqrt (g ^ 2 + g' ^ 2)

/-- **`sin θ_W = g'/√(g²+g'²)`**. -/
noncomputable def sinWeinberg (g g' : ℝ) : ℝ := g' / Real.sqrt (g ^ 2 + g' ^ 2)

/-- **`tan θ_W = g'/g`** — the ratio of the `U(1)_Y` to `SU(2)_L` couplings. -/
noncomputable def tanWeinberg (g g' : ℝ) : ℝ := g' / g

/-- **`sin²θ_W + cos²θ_W = 1`** (for `(g, g') ≠ 0`). -/
lemma sinSq_add_cosSq (g g' : ℝ) (hS : 0 < g ^ 2 + g' ^ 2) :
    sinWeinberg g g' ^ 2 + cosWeinberg g g' ^ 2 = 1 := by
  have hSne : g ^ 2 + g' ^ 2 ≠ 0 := ne_of_gt hS
  have hSs : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt (le_of_lt hS)
  unfold sinWeinberg cosWeinberg
  rw [div_pow, div_pow, hSs]; field_simp; ring

/-- **`tan θ_W = sin θ_W / cos θ_W`**. -/
lemma tan_eq_sin_div_cos (g g' : ℝ) (hS : 0 < g ^ 2 + g' ^ 2) :
    tanWeinberg g g' = sinWeinberg g g' / cosWeinberg g g' := by
  have hsne : Real.sqrt (g ^ 2 + g' ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hS
  unfold tanWeinberg sinWeinberg cosWeinberg
  rw [div_div_div_cancel_right₀]
  simpa using hsne


/-- **The electric charge `e = g sin θ_W`** — the unbroken `U(1)_em` coupling. -/
noncomputable def electricCharge (g g' : ℝ) : ℝ := g * sinWeinberg g g'

/-- **`e = g sin θ_W = g' cos θ_W`** — the electric charge is symmetric in the two couplings. -/
lemma electricCharge_symm (g g' : ℝ) : electricCharge g g' = g' * cosWeinberg g g' := by
  unfold electricCharge sinWeinberg cosWeinberg; ring

/-- **`1/e² = 1/g² + 1/g'²`** — the electric charge is the "reduced" coupling of `g` and `g'`. -/
lemma inv_electricCharge_sq (g g' : ℝ) (hg : g ≠ 0) (hg' : g' ≠ 0) (hS : 0 < g ^ 2 + g' ^ 2) :
    1 / electricCharge g g' ^ 2 = 1 / g ^ 2 + 1 / g' ^ 2 := by
  have hSs : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt (le_of_lt hS)
  unfold electricCharge sinWeinberg
  rw [mul_pow, div_pow, hSs]; field_simp; ring


/-- **The neutral gauge-boson mixing** `(A, Z) = R(θ_W)(B, W³)`: the photon `A = cos θ_W B +
sin θ_W W³` and `Z = −sin θ_W B + cos θ_W W³` — a rotation of `(B, W³)` by the Weinberg angle. -/
noncomputable def neutralMixing (g g' : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cosWeinberg g g', sinWeinberg g g'; -sinWeinberg g g', cosWeinberg g g']

/-- **The photon/`Z` mixing is orthogonal** (`Rᵀ R = 1`): the physical `(A, Z)` basis is an
orthonormal rotation of the gauge `(B, W³)` basis. -/
lemma neutralMixing_orthogonal (g g' : ℝ) (hS : 0 < g ^ 2 + g' ^ 2) :
    (neutralMixing g g')ᵀ * neutralMixing g g' = 1 := by
  have h := sinSq_add_cosSq g g' hS
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [neutralMixing, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    nlinarith [h]


/-- **The `ρ` parameter** `ρ = m_W² / (m_Z² cos²θ_W)`. -/
noncomputable def rhoParameter (mW mZ cw : ℝ) : ℝ := mW ^ 2 / (mZ ^ 2 * cw ^ 2)

/-- **`ρ = 1` at tree level**: the mass relation `m_W = m_Z cos θ_W` gives `ρ = 1` — the custodial-
symmetry prediction. -/
lemma rho_eq_one (mW mZ cw : ℝ) (hmZ : mZ ≠ 0) (hcw : cw ≠ 0) (h : mW = mZ * cw) :
    rhoParameter mW mZ cw = 1 := by
  unfold rhoParameter; rw [h]; field_simp


/-- **The weak isospin `T₃` on the `SU(5)` `5̄`** `= (d^c, d^c, d^c, e⁻, ν)`: the three colour
antiquarks are `SU(2)` singlets (`T₃ = 0`), the electron `e⁻` (index 3) has `T₃ = −1/2` and the
neutrino `ν` (index 4) has `T₃ = +1/2` (the `L = (ν, e⁻)` doublet). -/
def weakIsospin3 : Fin 5 → ℚ := ![0, 0, 0, -1/2, 1/2]

/-- **The `SU(5)` GUT prediction `sin²θ_W = 3/8`.** At the unification scale
`sin²θ_W = Tr(T₃²)/Tr(Q²)` over any complete representation; on the `5̄` this is
`Tr(T₃²) = 1/2` over `Tr(Q²) = 4/3` (reusing `su5AntifundCharge`), giving `3/8`. -/
lemma su5_sin2Weinberg_eq_three_eighths :
    (∑ i, weakIsospin3 i ^ 2) / (∑ i, su5AntifundCharge i ^ 2) = 3 / 8 := by
  simp [weakIsospin3, su5AntifundCharge, Fin.sum_univ_five]; norm_num

end Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
