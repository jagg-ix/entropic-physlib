/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.Wick.Consistency
public import Physlib.Thermodynamics.SecondLaw.SergiOperatorTimeFree

/-!
# Louko–Sorkin: complex actions in two-dimensional topology change

Louko and Sorkin (1997) analyse `(1+1)`-dimensional topology change through the scalar-curvature action
`½∫R dV` at points of metric degeneration. Any two-dimensional cobordism is built from two elementary
Morse-theory pieces:

* the **yarmulke** — a conical initial/final point, the creation or annihilation of a universe (one
  causal domain of Misner space with a single point adjoined);
* the **trousers** — a **crotch singularity** signalling a change of spatial topology (also the
  fundamental vertex of string theory).

Regularizing the degenerate metric by a small imaginary part (its sign fixed by convergence of a
scalar-field path integral) and removing the regulator, the density `½√(−g)R` becomes a delta-function
of **complex strength**: `β − 2πi` for the yarmulke (`β` the Misner rapidity), and `2πi` for the
trousers. Through the complex-action path weight `exp(iS/ℏ)` (`QFT.Wick.Consistency`), the imaginary
strength gives a real exponential factor: **topology change (trousers) is exponentially suppressed**,
while **universe creation (yarmulke) is exponentially enhanced**.

* **§A — the two elementary cobordisms** (`Cobordism2D`).
* **§B — the complex delta-function strength** (`yarmulkeStrength β = β − 2πi`, `trousersStrength =
  2πi`); real part `= β`/`0`, imaginary part `= −2π`/`+2π`.
* **§C — the path weight** (`cobordismWeight`, reusing `complexActionWeight`): its modulus is
  `exp(−(Im σ)/(κℏ))` (`trousersWeight_norm`, `yarmulkeWeight_norm`).
* **§D — suppression versus enhancement**: `trousers_suppressed` (`< 1`), `yarmulke_enhanced`
  (`> 1`), and the contrast `topologyChange_suppressed_lt_yarmulke_enhanced`.
* **§E — entropic-time reading** (reusing `Thermodynamics.SecondLaw.entropicTimeOf`): the trousers'
  imaginary action is a **forward** entropic time (`trousers_entropicTime_nonneg`, suppression), the
  yarmulke's a **reversed** one (`yarmulke_entropicTime_neg`, enhancement).

The conical singularity here is exactly the support of the curvature in Regge calculus
(`LeviCivita.ComplexReggeAction`; Sorkin's `Sorkin:1975ah`): the delta strength is the (complex)
Regge defect, and the weight `exp(−S_I/ℏ)` is the same entropic modulus.

**Honest layering.** Proven: the complex strengths, the weight modulus, the suppression/enhancement
inequalities, and the entropic-time signs. Interpretive: the Morse-metric derivation of the strengths
`β − 2πi`/`2πi` is Louko–Sorkin's (from the regularized `½√(−g)R`), taken here as the input datum.

## References

* J. Louko, R. D. Sorkin, "Complex actions in two-dimensional topology change", Class. Quantum Grav.
  **14**, 179 (1997) [`Louko:1995jw`]. Reuses `QFT.Wick.Consistency` (`complexActionWeight`,
  `norm_complexActionWeight`) and `Thermodynamics.SecondLaw` (`entropicTimeOf`).


-/

set_option autoImplicit false

open scoped Real
open Physlib.QFT.Wick.Consistency
open Physlib.Thermodynamics.SecondLaw

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChange


/-- **The elementary `(1+1)` cobordisms** (Louko–Sorkin): any two-dimensional cobordism is a
combination of the `yarmulke` (universe creation/annihilation) and the `trousers` (topology change). -/
inductive Cobordism2D
  | yarmulke
  | trousers


/-- **The yarmulke strength** `β − 2πi` — `β` is the rapidity of the associated Misner space. -/
noncomputable def yarmulkeStrength (β : ℝ) : ℂ := (β : ℂ) - ((2 * Real.pi : ℝ) : ℂ) * Complex.I

/-- **The trousers (crotch) strength** `2πi`. -/
noncomputable def trousersStrength : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I

@[simp] lemma yarmulkeStrength_re (β : ℝ) : (yarmulkeStrength β).re = β := by
  simp [yarmulkeStrength]

/-- The yarmulke's imaginary strength is `−2π` (the sign that will *enhance* the amplitude). -/
@[simp] lemma yarmulkeStrength_im (β : ℝ) : (yarmulkeStrength β).im = -(2 * Real.pi) := by
  simp [yarmulkeStrength]

@[simp] lemma trousersStrength_re : trousersStrength.re = 0 := by simp [trousersStrength]

/-- The trousers' imaginary strength is `+2π` (the sign that will *suppress* the amplitude). -/
@[simp] lemma trousersStrength_im : trousersStrength.im = 2 * Real.pi := by simp [trousersStrength]


/-- **The cobordism path weight** `exp(iS/ℏ)` with the complex action `S = σ/κ` — the strength `σ`
divided by the gravitational constant `κ` (reusing `complexActionWeight`). -/
noncomputable def cobordismWeight (strength : ℂ) (κ ℏ : ℝ) : ℂ :=
  complexActionWeight (strength.re / κ) (strength.im / κ) ℏ

/-- **The trousers amplitude modulus** `= exp(−2π/(κℏ))` — a real suppression factor. -/
lemma trousersWeight_norm (κ ℏ : ℝ) :
    ‖cobordismWeight trousersStrength κ ℏ‖ = Real.exp (-(2 * Real.pi / κ / ℏ)) := by
  rw [cobordismWeight, norm_complexActionWeight, trousersStrength_im]

/-- **The yarmulke amplitude modulus** `= exp(+2π/(κℏ))` — a real enhancement factor. -/
lemma yarmulkeWeight_norm (β κ ℏ : ℝ) :
    ‖cobordismWeight (yarmulkeStrength β) κ ℏ‖ = Real.exp (2 * Real.pi / κ / ℏ) := by
  rw [cobordismWeight, norm_complexActionWeight, yarmulkeStrength_im]
  congr 1; ring


/-- **Topology change is exponentially suppressed**: the trousers amplitude has modulus `< 1`. -/
lemma trousers_suppressed (κ ℏ : ℝ) (hκ : 0 < κ) (hℏ : 0 < ℏ) :
    ‖cobordismWeight trousersStrength κ ℏ‖ < 1 := by
  rw [trousersWeight_norm, Real.exp_lt_one_iff]
  have : 0 < 2 * Real.pi / κ / ℏ := by have := Real.pi_pos; positivity
  linarith

/-- **Universe creation is exponentially enhanced**: the yarmulke amplitude has modulus `> 1`. -/
lemma yarmulke_enhanced (β κ ℏ : ℝ) (hκ : 0 < κ) (hℏ : 0 < ℏ) :
    1 < ‖cobordismWeight (yarmulkeStrength β) κ ℏ‖ := by
  rw [yarmulkeWeight_norm, Real.one_lt_exp_iff]
  have := Real.pi_pos; positivity

/-- **The contrast**: the topology-changing trousers amplitude is strictly below the enhanced yarmulke
amplitude — Louko–Sorkin's central dynamical asymmetry. -/
lemma topologyChange_suppressed_lt_yarmulke_enhanced (β κ ℏ : ℝ) (hκ : 0 < κ) (hℏ : 0 < ℏ) :
    ‖cobordismWeight trousersStrength κ ℏ‖ < ‖cobordismWeight (yarmulkeStrength β) κ ℏ‖ :=
  lt_trans (trousers_suppressed κ ℏ hκ hℏ) (yarmulke_enhanced β κ ℏ hκ hℏ)


/-- **The trousers carry a forward entropic time**: their imaginary action `2π/κ ≥ 0` gives a
non-negative `entropicTimeOf`, so the weight `exp(−τ_ent) < 1` — the suppression is a forward arrow
(reusing `entropicTimeOf_nonneg`). -/
lemma trousers_entropicTime_nonneg (κ ℏ : ℝ) (hκ : 0 < κ) (hℏ : 0 < ℏ) :
    0 ≤ entropicTimeOf (trousersStrength.im / κ) ℏ := by
  rw [trousersStrength_im]
  exact entropicTimeOf_nonneg (by have := Real.pi_pos; positivity) hℏ

/-- **The yarmulke carries a reversed entropic time**: its imaginary action `−2π/κ < 0` gives a
negative `entropicTimeOf`, so the weight `exp(−τ_ent) > 1` — the enhancement is a reversed arrow. -/
lemma yarmulke_entropicTime_neg (β κ ℏ : ℝ) (hκ : 0 < κ) (hℏ : 0 < ℏ) :
    entropicTimeOf ((yarmulkeStrength β).im / κ) ℏ < 0 := by
  rw [yarmulkeStrength_im]
  show -(2 * Real.pi) / κ / ℏ < 0
  have := Real.pi_pos
  have h : 0 < 2 * Real.pi / κ / ℏ := by positivity
  rw [neg_div, neg_div]; linarith

end Physlib.QuantumMechanics.ComplexAction.TwoDimensionalTopologyChange
