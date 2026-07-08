/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

/-!
# Nambu trajectories vs the Nagao–Nielsen contour: contour ↔ strange-attractor deformation

The dissipative Nambu flow (`DissipativeNambuLorenz.DissipativeNambu`) splits the motion into a conservative
rotational part `∇H₁ × ∇H₂` (which keeps `H₁, H₂` constant — the orbit on the surface intersection, §B) and a
dissipative irrotational part `∇D` (which deforms the surfaces, `Ḣⱼ = ∇D·∇Hⱼ`, §C, producing the strange
attractor). This file tracks that trajectory against the **Nagao–Nielsen complex-action contour**
(`nnPathWeight`, `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}`) by accumulating the dissipation as the **imaginary action /
entropy production**.

The dissipation contributes a positive entropy-production rate `|∇D|²` (the `(∇D)²` term of `Ḋ`, Eq. 2.29);
accumulated over trajectory time `t` it is the imaginary action `S_I = |∇D|²·t`, and the Nagao–Nielsen
contour weight along the trajectory is `e^{−S_I/ℏ}`.

* **§A — entropy production from dissipation.** `nambuEntropyProductionRate gD = |∇D|² ≥ 0`
  (`_nonneg`, the second law), `= 0 ⟺ ∇D = 0` (`_eq_zero_iff`, reversible ⟺ conservative Nambu flow), `> 0`
  for `∇D ≠ 0` (`_pos`).
* **§B — the contour weight along the trajectory.** `nambuImaginaryAction gD t = |∇D|²·t`;
  `nambuPathWeight_norm`: the Nagao–Nielsen weight modulus is `e^{−|∇D|² t/ℏ}`.
* **§C — contour vs attractor.** `conservative_contour_undeformed`: at `∇D = 0` the weight is `1` for all
  time — **undeformed contour**, reversible motion confined to the `H₁,H₂` surfaces (no attractor).
  `dissipative_contour_decays`: at `∇D ≠ 0` (and `t, ℏ > 0`) the weight is `< 1` — the **contour deforms**
  (entropic decay) precisely when the *same* `∇D` deforms the surfaces (`dissipativeFlow_H₁_rate`,
  `Ḣⱼ = ∇D·∇Hⱼ`). The Nagao–Nielsen contour deformation *is* the strange-attractor deformation.

So one quantity — the dissipation `∇D` — drives both the imaginary-action / entropic-time accumulation
(contour) and the surface deformation (attractor); they vanish together in the conservative limit.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036 (Eqs. 2.23, 2.28–2.29). N. Nagao, H. B. Nielsen, complex
  action. `Physlib` (`DissipativeNambuLorenz.DissipativeNambu`, `NonHermitianComplexAction.EntropicDampingEquivalence`).

No new axioms.
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.NambuEntropicContour

/-! ## §A — entropy production from the dissipative gradient -/

/-- **The local entropy-production rate** `|∇D|² = ∇D · ∇D` of the dissipative Nambu flow — the positive
`(∇D)²` term of `Ḋ` (Eq. 2.29), the rate at which the dissipation injects imaginary action. -/
def nambuEntropyProductionRate (gD : Fin 3 → ℝ) : ℝ := gD ⬝ᵥ gD

/-- **[Entropy production is nonnegative]** `|∇D|² ≥ 0` — the second law for the Nambu dissipation. -/
theorem nambuEntropyProductionRate_nonneg (gD : Fin 3 → ℝ) :
    0 ≤ nambuEntropyProductionRate gD := by
  simpa [nambuEntropyProductionRate] using dotProduct_star_self_nonneg gD

/-- **[Reversible ⟺ no dissipation]** `|∇D|² = 0 ⟺ ∇D = 0`: the entropy production vanishes exactly when the
flow is the purely conservative (rotational) Nambu flow. -/
theorem nambuEntropyProductionRate_eq_zero_iff (gD : Fin 3 → ℝ) :
    nambuEntropyProductionRate gD = 0 ↔ gD = 0 :=
  dotProduct_self_eq_zero

/-- **[Dissipation ⟹ positive entropy production]** `∇D ≠ 0 ⟹ |∇D|² > 0`. -/
theorem nambuEntropyProductionRate_pos {gD : Fin 3 → ℝ} (h : gD ≠ 0) :
    0 < nambuEntropyProductionRate gD := by
  refine lt_of_le_of_ne (nambuEntropyProductionRate_nonneg gD) ?_
  intro heq
  exact h ((nambuEntropyProductionRate_eq_zero_iff gD).mp heq.symm)

/-! ## §B — the Nagao–Nielsen contour weight along the Nambu trajectory -/

/-- **The accumulated imaginary action** `S_I = |∇D|²·t` along the trajectory over time `t` — the entropy
production of the dissipation integrated along the flow. -/
def nambuImaginaryAction (gD : Fin 3 → ℝ) (t : ℝ) : ℝ := nambuEntropyProductionRate gD * t

/-- **[Contour weight along the trajectory]** `‖nnPathWeight S_R S_I ℏ‖ = e^{−|∇D|² t/ℏ}`: the Nagao–Nielsen
complex-action weight tracked along the dissipative Nambu trajectory. -/
theorem nambuPathWeight_norm (S_R : ℝ) (gD : Fin 3 → ℝ) (ℏ t : ℝ) :
    ‖nnPathWeight S_R (nambuImaginaryAction gD t) ℏ‖
      = Real.exp (-(nambuEntropyProductionRate gD * t) / ℏ) := by
  rw [norm_nnPathWeight, nambuImaginaryAction]
  congr 1
  ring

/-! ## §C — contour deformation ⟺ strange-attractor deformation -/

/-- **[Conservative ⟹ undeformed contour]** at `∇D = 0` the contour weight is `1` for all time — the
reversible Nambu flow, the orbit confined to the `H₁, H₂` surfaces with no attractor and no entropic decay. -/
theorem conservative_contour_undeformed (S_R ℏ t : ℝ) :
    ‖nnPathWeight S_R (nambuImaginaryAction 0 t) ℏ‖ = 1 := by
  rw [nambuPathWeight_norm]
  simp [nambuEntropyProductionRate]

/-- **[Dissipation ⟹ contour decays = attractor deformation]** at `∇D ≠ 0` (and `t, ℏ > 0`) the contour
weight is `< 1`: the Nagao–Nielsen contour deforms (entropic decay) exactly when the same `∇D` deforms the
Nambu surfaces (`dissipativeFlow_H₁_rate`, `Ḣⱼ = ∇D·∇Hⱼ`). The contour deformation *is* the strange-attractor
deformation. -/
theorem dissipative_contour_decays (S_R : ℝ) {gD : Fin 3 → ℝ} {t ℏ : ℝ}
    (hgD : gD ≠ 0) (ht : 0 < t) (hℏ : 0 < ℏ) :
    ‖nnPathWeight S_R (nambuImaginaryAction gD t) ℏ‖ < 1 := by
  rw [nambuPathWeight_norm]
  have hpos : 0 < nambuEntropyProductionRate gD * t / ℏ :=
    div_pos (mul_pos (nambuEntropyProductionRate_pos hgD) ht) hℏ
  rw [neg_div]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-! ## §D — Li Morse-Lyapunov attractor reading -/

/-- The dissipative Nambu entropy-production rate is a valid nonnegative Lyapunov decay rate. -/
theorem nambuEntropyProduction_is_decayRate_nonneg (gD : Fin 3 -> ℝ) :
    0 ≤ nambuEntropyProductionRate gD :=
  nambuEntropyProductionRate_nonneg gD

/-- Nonzero dissipative Nambu gradient gives a strictly positive decay rate. -/
theorem nambuEntropyProduction_is_decayRate_pos {gD : Fin 3 -> ℝ} (hgD : gD ≠ 0) :
    0 < nambuEntropyProductionRate gD :=
  nambuEntropyProductionRate_pos hgD

/-- The existing Nambu contour theorem is exactly a strict Lyapunov/attractor decay statement for the
Nagao-Nielsen complex-action weight. -/
theorem nambu_dissipation_gives_strict_weight_decay
    (S_R : ℝ) {gD : Fin 3 -> ℝ} {t hbar : ℝ}
    (hgD : gD ≠ 0) (ht : 0 < t) (hhbar : 0 < hbar) :
    ‖nnPathWeight S_R (nambuImaginaryAction gD t) hbar‖ < 1 :=
  dissipative_contour_decays S_R hgD ht hhbar

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.NambuEntropicContour

end
