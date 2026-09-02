/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChange

/-!
# Asante–Dittrich–Padua-Argüelles: the complex Regge action and causality violations

Asante, Dittrich and Padua-Argüelles (2021) build the **complex Regge action** for Lorentzian quantum
cosmology from complexified edge lengths, unifying Euclidean and Lorentzian angles by a **Wick
rotation** and analysing causality-violating configurations (trousers/yarmulke) via Picard–Lefschetz.
This module formalizes the algebraic core — the Wick-rotated inner product, the area identity that
resolves the branch cut, the Euclidean↔Lorentzian interpolation — and ties it to the topology-change
strengths of `TwoDimensionalTopologyChange`.

* **§A — the Wick-rotated inner product** (Eq. 2.4): `a ⋆ b = e^{iφ} a₀b₀ + a₁b₁`, with the Wick angle
  `φ`; `wickInner_euclidean` (`φ = 0`: `a₀b₀ + a₁b₁`) and `wickInner_minkowskian`
  (`φ = π`: `−a₀b₀ + a₁b₁`).
* **§B — the area identity** (Eq. 2.14): `(a⋆b)² − (a⋆a)(b⋆b) = −e^{iφ}(a₀b₁ − a₁b₀)²`
  (`wick_area_identity`) — the discriminant under the square root of the dihedral angle (Eq. 2.5) is
  minus `e^{iφ}` times the squared signed area. This resolves the branch cut at `φ = 0`.
* **§C — Euclidean ↔ Lorentzian interpolation.** The discriminant is negative for Euclidean data
  (`wickDiscriminant_euclidean`) and its sign flips to positive Minkowskian
  (`wickDiscriminant_minkowskian`) — the Wick rotation `φ: 0 → π` continuing the (real) Euclidean
  angle to the (boost) Lorentzian one.
* **§D — the light-ray crossings and the topology-change strengths.** Each light-ray crossing adds
  `∓iπ/2` to the Minkowskian angle (Eq. 2.1); the **trousers crotch has four light cones**
  (`trousers_four_lightcones`), giving the imaginary strength `4·(π/2) = 2π` — exactly
  `TwoDimensionalTopologyChange.trousersStrength.im`. So the Louko–Sorkin `2πi` is four
  Asante–Dittrich–Padua-Argüelles light-ray crossings.
* **§E — causal regularity and suppression/enhancement** (Eqs. 2.32, 2.38). `Im(ε_L±) = ±(N_c − 4)π/2`
  (`lorentzianDeficitImaginary`); a configuration is **causally regular iff `N_c = 4`**
  (`causallyRegular_iff`). The amplitude `exp(−A·Im ε_L)` **is** the complex-action entropic weight
  `‖exp(iS/ℏ)‖` (`deficitAmplitude_eq_weight_norm`, unifying with `QFT.Wick.Consistency`): causally
  regular = the reversible pure-phase limit (`causallyRegular_pure_phase`); **suppressed for trousers**
  (`N_c > 4`, `trousers_amplitude_suppressed`) and **enhanced for yarmulke** (`N_c < 4`,
  `yarmulke_amplitude_enhanced`) — the same `complexActionWeight` asymmetry as
  `TwoDimensionalTopologyChange`, now a function of the light-ray-crossing count.

**Honest layering.** Proven: the Wick inner product and its signature limits, the area identity, the
discriminant sign flip, and the crossing-count arithmetic. Interpretive: the full complex dihedral
angle `θ = −i log(…)` and its branch structure (the `θ⁺ = −θ⁻` versions, Picard–Lefschetz contours)
are the analytic content the area identity underlies, not re-derived here.

## References

* S. K. Asante, B. Dittrich, J. Padua-Argüelles, "Complex actions and causality violations",
  arXiv:2112.15387 [`Asante:2021zzh`], Eqs. (2.1), (2.4), (2.5), (2.14). Reuses
  `TwoDimensionalTopologyChange` (`trousersStrength`, the Louko–Sorkin strengths).


-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality

open Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChange
open Physlib.QFT.Wick.Consistency


/-- **The Wick-rotated inner product** `a ⋆ b = e^{iφ} a₀b₀ + a₁b₁` (Asante–Dittrich–Padua-Argüelles
Eq. 2.4), with `φ ∈ (−π, π]` the Wick rotation angle unifying Euclidean and Minkowskian signatures. -/
noncomputable def wickInner (φ : ℝ) (a b : Fin 2 → ℂ) : ℂ :=
  Complex.exp (φ * Complex.I) * a 0 * b 0 + a 1 * b 1

/-- **The Euclidean limit** `φ = 0`: the positive-definite inner product `a₀b₀ + a₁b₁`. -/
lemma wickInner_euclidean (a b : Fin 2 → ℂ) : wickInner 0 a b = a 0 * b 0 + a 1 * b 1 := by
  simp [wickInner]

/-- **The Minkowskian limit** `φ = π`: the Lorentzian inner product `−a₀b₀ + a₁b₁`
(`e^{iπ} = −1`). -/
lemma wickInner_minkowskian (a b : Fin 2 → ℂ) :
    wickInner Real.pi a b = -(a 0 * b 0) + a 1 * b 1 := by
  simp [wickInner, Complex.exp_pi_mul_I]


/-- **The discriminant** `(a⋆b)² − (a⋆a)(b⋆b)` under the square root of the dihedral angle (Eq. 2.5). -/
noncomputable def wickDiscriminant (φ : ℝ) (a b : Fin 2 → ℂ) : ℂ :=
  (wickInner φ a b) ^ 2 - wickInner φ a a * wickInner φ b b

/-- **The area identity** (Asante–Dittrich–Padua-Argüelles Eq. 2.14): the discriminant is
`−e^{iφ}` times the squared signed area `(a₀b₁ − a₁b₀)²` — resolving the branch cut of the square
root at `φ = 0`. -/
lemma wick_area_identity (φ : ℝ) (a b : Fin 2 → ℂ) :
    wickDiscriminant φ a b = - Complex.exp (φ * Complex.I) * (a 0 * b 1 - a 1 * b 0) ^ 2 := by
  unfold wickDiscriminant wickInner; ring


/-- **Euclidean discriminant** `φ = 0`: `−(a₀b₁ − a₁b₀)²`, the negative squared area — the angle is a
real Euclidean angle `cos⁻¹`. -/
lemma wickDiscriminant_euclidean (a b : Fin 2 → ℂ) :
    wickDiscriminant 0 a b = - (a 0 * b 1 - a 1 * b 0) ^ 2 := by
  rw [wick_area_identity]; simp

/-- **Minkowskian discriminant** `φ = π`: `+(a₀b₁ − a₁b₀)²`, the sign flipped positive by the Wick
rotation — the angle is a Lorentzian boost `cosh⁻¹`. The Wick rotation `φ: 0 → π` continues the
Euclidean angle to the Lorentzian one. -/
lemma wickDiscriminant_minkowskian (a b : Fin 2 → ℂ) :
    wickDiscriminant Real.pi a b = (a 0 * b 1 - a 1 * b 0) ^ 2 := by
  rw [wick_area_identity, Complex.exp_pi_mul_I]; ring


/-- **The Minkowskian-angle imaginary contribution per light-ray crossing**: `π/2` (the `∓iπ/2` of
Eq. 2.1, whose sign is the causality-violation convention). -/
noncomputable def crossingImaginary : ℝ := Real.pi / 2

/-- **The accumulated imaginary angle** of `Nc` light-ray crossings: `Nc · π/2` (Eq. 2.11,
`Re θ±(±π) = ∓πNc/2`). -/
noncomputable def accumulatedImaginary (Nc : ℕ) : ℝ := (Nc : ℝ) * crossingImaginary

/-- **The trousers crotch has four light cones**: the accumulated imaginary angle of its four
light-ray crossings is `4·(π/2) = 2π` — exactly the imaginary strength `2π` of the Louko–Sorkin
trousers (`TwoDimensionalTopologyChange.trousersStrength.im`). The `2πi` topology-change strength *is*
four Asante–Dittrich–Padua-Argüelles light-ray crossings. -/
lemma trousers_four_lightcones : accumulatedImaginary 4 = trousersStrength.im := by
  rw [trousersStrength_im]
  unfold accumulatedImaginary crossingImaginary
  push_cast; ring


/-- **The imaginary part of the Lorentzian deficit angle** `Im(ε_L±) = ±(N_c − 4)·π/2` (Eq. 2.32),
`N_c` the number of light-ray crossings in the wedges around a hinge. -/
noncomputable def lorentzianDeficitImaginary (Nc : ℕ) : ℝ := ((Nc : ℝ) - 4) * (Real.pi / 2)

/-- **A configuration is causally regular** (the Lorentzian deficit angle is real) **iff it has exactly
four light-ray crossings** `N_c = 4` — the Asante–Dittrich–Padua-Argüelles causal-regularity condition
(Eq. 2.32). -/
lemma causallyRegular_iff (Nc : ℕ) : lorentzianDeficitImaginary Nc = 0 ↔ Nc = 4 := by
  unfold lorentzianDeficitImaginary
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact_mod_cast (by linarith : (Nc : ℝ) = 4)
    · exact absurd h (by have := Real.pi_pos; positivity)
  · intro h; left; rw [h]; norm_num

/-- **The deficit contribution to the path-integral amplitude** `|exp(i A ε_L)| = exp(−A·Im ε_L)` for a
hinge of area `A` (the entropic modulus of the complex Regge weight). -/
noncomputable def deficitAmplitude (area : ℝ) (Nc : ℕ) : ℝ :=
  Real.exp (- area * lorentzianDeficitImaginary Nc)

/-- **Unification** — the deficit amplitude *is* the complex-action entropic weight: it equals the
modulus `‖exp(iS/ℏ)‖ = exp(−S_I/ℏ)` (`QFT.Wick.Consistency.complexActionWeight`) with imaginary Regge
action `S_I = A · Im ε_L`. So the causality amplitude is not a new object but the same
`complexActionWeight` that carries the whole complex-action arc (`TwoDimensionalTopologyChange`,
`LeviCivita.ComplexReggeAction`). -/
lemma deficitAmplitude_eq_weight_norm (area : ℝ) (Nc : ℕ) :
    deficitAmplitude area Nc = ‖complexActionWeight 0 (area * lorentzianDeficitImaginary Nc) 1‖ := by
  rw [norm_complexActionWeight]; unfold deficitAmplitude; congr 1; ring

/-- **Causal regularity is the reversible (unitary) limit**: `N_c = 4` gives a real deficit angle,
zero imaginary action, and a **pure-phase** amplitude `= 1` — no entropic damping, exactly the
`reggeAction_real_defect_pure_phase` / `norm_complexActionWeight_zero_imag` unitary case of the
complex-action theory. -/
lemma causallyRegular_pure_phase (area : ℝ) (Nc : ℕ) (h : Nc = 4) : deficitAmplitude area Nc = 1 := by
  have h0 : lorentzianDeficitImaginary Nc = 0 := (causallyRegular_iff Nc).mpr h
  rw [deficitAmplitude, h0]; simp

/-- **Trousers-like configurations are suppressed** (Eq. 2.38): more than four light-ray crossings
(`N_c > 4`) give a positive imaginary deficit and an amplitude `< 1` — the topology-changing crotch is
exponentially suppressed, exactly `TwoDimensionalTopologyChange.trousers_suppressed`. -/
lemma trousers_amplitude_suppressed (area : ℝ) (harea : 0 < area) (Nc : ℕ) (h : 4 < Nc) :
    deficitAmplitude area Nc < 1 := by
  rw [deficitAmplitude, Real.exp_lt_one_iff]
  have hNc : (4 : ℝ) < Nc := by exact_mod_cast h
  have hpos : 0 < area * lorentzianDeficitImaginary Nc := by
    unfold lorentzianDeficitImaginary
    exact mul_pos harea (mul_pos (by linarith) (by have := Real.pi_pos; linarith))
  have heq : - area * lorentzianDeficitImaginary Nc
      = -(area * lorentzianDeficitImaginary Nc) := by ring
  rw [heq]; linarith

/-- **Yarmulke-like configurations are enhanced** (Eq. 2.38): fewer than four light-ray crossings
(`N_c < 4`) give a negative imaginary deficit and an amplitude `> 1` — the universe-creating yarmulke
is exponentially enhanced, exactly `TwoDimensionalTopologyChange.yarmulke_enhanced`. -/
lemma yarmulke_amplitude_enhanced (area : ℝ) (harea : 0 < area) (Nc : ℕ) (h : Nc < 4) :
    1 < deficitAmplitude area Nc := by
  rw [deficitAmplitude, Real.one_lt_exp_iff]
  have hNc : (Nc : ℝ) < 4 := by exact_mod_cast h
  have hneg : area * lorentzianDeficitImaginary Nc < 0 := by
    unfold lorentzianDeficitImaginary
    have : ((Nc : ℝ) - 4) * (Real.pi / 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by have := Real.pi_pos; linarith)
    nlinarith
  have heq : - area * lorentzianDeficitImaginary Nc
      = -(area * lorentzianDeficitImaginary Nc) := by ring
  rw [heq]; linarith

end Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality
