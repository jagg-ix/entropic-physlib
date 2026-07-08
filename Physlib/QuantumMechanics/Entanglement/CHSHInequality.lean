/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# CHSH inequality and the quantum bound `S = 2√2`

Port of the CHSH content from
`/Users/macbookpro/Downloads/tau/ChatGPT-Minimal Game Universe
Refinement.md` §9000-9050 (Reply 23 of the "Game Universe" model).
The portable substance: the algebraic computation showing the
**quantum singlet-state correlation function** violates the
classical CHSH bound of 2 at specific measurement angles, attaining
the Tsirelson maximum `2·√2`.

## The CHSH expression (Clauser-Horne-Shimony-Holt 1969)

For a two-party Bell experiment with measurement settings `a, a'`
(party A) and `b, b'` (party B), the **CHSH expression** is

  `S(a, a', b, b') := |E(a,b) - E(a,b') + E(a',b) + E(a',b')|`

where `E(x, y) ∈ [-1, +1]` is the *expectation of the product of
the measurement outcomes* (each ±1).

**Classical bound** (any local hidden-variable theory):
`S ≤ 2`.

**Quantum bound (Tsirelson 1980)**: `S ≤ 2·√2 ≈ 2.828`.

For the **quantum correlation function**
`E_quantum(θ_A, θ_B) := cos(θ_A − θ_B)` (or `-cos(θ_A − θ_B)`
depending on sign convention) — the singlet-state expectation for
spin-1/2 measurements along axes at angles `θ_A`, `θ_B` — the
CHSH expression evaluates to **exactly `2·√2`** at the optimal
angle choice `a = 0, a' = π/2, b = π/4, b' = 3π/4`.

This **violates** the classical bound by a factor of `√2`, ruling
out any local hidden-variable model.

## Contents

* `quantumCorrelation θ_A θ_B := cos(θ_A − θ_B)` — the singlet
  spin-correlation function.
* `chshExpression E a a' b b'` — the CHSH expression as an
  absolute value.
* **`chsh_quantum_at_tsirelson_angles`** — at the optimal angles,
  the quantum CHSH expression equals `2·√2`.
* `chsh_quantum_exceeds_classical_bound_2` — `2·√2 > 2`, so the
  quantum value exceeds the classical bound.
* Bounds: `tsirelson_bound : 2 * √2 ≈ 2.828`.

## What this file does NOT ship

* **Proof of the classical bound `S ≤ 2`** under any local
  hidden-variable model.  That requires a measure-theoretic
  framework for ±1-valued random variables and the
  `|±1 + ±1| ≤ 2` algebraic step.  Achievable but ~200 LOC of
  separate scope.  Here we *state* the classical bound as a
  reference and prove only the quantum-side computation.

* **Connection to physical Bell experiments** (POVMs, measurement
  postulate, etc.) — those need physlib's measurement infrastructure
  (`Physlib/QuantumMechanics/QuantumInfo/` etc.).  The present file
  is the *algebraic-numerical* portion of the CHSH theorem.

## References

* Bell 1964 *On the Einstein Podolsky Rosen Paradox*, Physics 1, 195.
* CHSH 1969 *Proposed Experiment to Test Local Hidden-Variable
  Theories*, Phys. Rev. Lett. 23, 880.
* Tsirelson 1980 *Quantum Generalizations of Bell's Inequality*,
  Lett. Math. Phys. 4, 93.
* `Downloads/tau/ChatGPT-Minimal Game Universe Refinement.md`
  Reply 23, §9000-9050 — conceptual source.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Entanglement

open Real

/-! ## §1 — Quantum correlation function -/

/-- **Quantum singlet-state correlation function**:
`E(θ_A, θ_B) := cos(θ_A − θ_B)`.

For two spin-1/2 particles in the singlet state, measured along
axes at angles `θ_A, θ_B`, the expectation of the product of the
±1 outcomes is `cos(θ_A − θ_B)`.  (Convention here: positive
correlation; the singlet convention `-cos(θ_A - θ_B)` differs by a
global sign which cancels in the CHSH `|·|`.) -/
def quantumCorrelation (θ_A θ_B : ℝ) : ℝ := Real.cos (θ_A - θ_B)

/-- The quantum correlation is in `[-1, 1]`. -/
theorem quantumCorrelation_le_one (θ_A θ_B : ℝ) :
    quantumCorrelation θ_A θ_B ≤ 1 := Real.cos_le_one _

theorem neg_one_le_quantumCorrelation (θ_A θ_B : ℝ) :
    -1 ≤ quantumCorrelation θ_A θ_B := Real.neg_one_le_cos _

/-! ## §2 — CHSH expression -/

/-- **CHSH expression**: `|E(a,b) − E(a,b') + E(a',b) + E(a',b')|`
for a two-party Bell experiment with measurement settings `(a, a')`
and `(b, b')`, and correlation function `E`. -/
def chshExpression (E : ℝ → ℝ → ℝ) (a a' b b' : ℝ) : ℝ :=
  |E a b - E a b' + E a' b + E a' b'|

/-! ## §3 — Tsirelson angles and the quantum bound -/

/-- **Optimal Tsirelson angles for CHSH**: `a = 0`, `a' = π/2`,
`b = π/4`, `b' = 3π/4`.  At these angles, the singlet correlation
attains the Tsirelson maximum `2·√2`. -/
def tsirelsonAnglesA : ℝ × ℝ := (0, Real.pi / 2)
def tsirelsonAnglesB : ℝ × ℝ := (Real.pi / 4, 3 * Real.pi / 4)

/-! ## §4 — Closed-form evaluation at Tsirelson angles -/

/-- `cos(0 − π/4) = √2/2`. -/
theorem cos_zero_sub_pi_div_four : Real.cos (0 - Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [zero_sub, Real.cos_neg]
  exact Real.cos_pi_div_four

/-- `cos(0 − 3π/4) = -√2/2`. -/
theorem cos_zero_sub_three_pi_div_four :
    Real.cos (0 - 3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
  have h1 : (0 : ℝ) - 3 * Real.pi / 4 = -(3 * Real.pi / 4) := by ring
  rw [h1, Real.cos_neg]
  have h2 : (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 := by ring
  rw [h2, Real.cos_pi_sub, Real.cos_pi_div_four]
  ring

/-- `cos(π/2 − π/4) = cos(π/4) = √2/2`. -/
theorem cos_pi_div_two_sub_pi_div_four :
    Real.cos (Real.pi / 2 - Real.pi / 4) = Real.sqrt 2 / 2 := by
  have h : (Real.pi / 2 - Real.pi / 4 : ℝ) = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]

/-- `cos(π/2 − 3π/4) = √2/2`. -/
theorem cos_pi_div_two_sub_three_pi_div_four :
    Real.cos (Real.pi / 2 - 3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
  have h1 : (Real.pi / 2 - 3 * Real.pi / 4 : ℝ) = -(Real.pi / 4) := by ring
  rw [h1, Real.cos_neg, Real.cos_pi_div_four]

/-! ## §5 — The Tsirelson-bound theorem (CHSH = 2√2 at the optimal angles) -/

/-- **CHSH expression for the quantum correlation at the
Tsirelson angles equals `2·√2`** — the load-bearing computation.

At `a = 0, a' = π/2, b = π/4, b' = 3π/4`:

```
E(a, b)   = cos(0 − π/4)     = √2/2
E(a, b')  = cos(0 − 3π/4)    = −√2/2
E(a', b)  = cos(π/2 − π/4)   = √2/2
E(a', b') = cos(π/2 − 3π/4)  = √2/2

S = |E(a,b) − E(a,b') + E(a',b) + E(a',b')|
  = |√2/2 − (−√2/2) + √2/2 + √2/2|
  = |4 · (√2/2)|
  = 2·√2 ≈ 2.828
```

This **exceeds the classical bound of 2** by a factor of `√2`.
The singlet correlation `cos(θ_A − θ_B)` is the *quantum-mechanical*
expectation, derived from the spin-1/2 singlet state and the Born
rule.  Tsirelson 1980 proved that `2·√2` is the *maximum possible*
value for any quantum CHSH expression. -/
theorem chsh_quantum_at_tsirelson_angles :
    chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) = 2 * Real.sqrt 2 := by
  unfold chshExpression quantumCorrelation
  rw [cos_zero_sub_pi_div_four, cos_zero_sub_three_pi_div_four,
      cos_pi_div_two_sub_pi_div_four,
      cos_pi_div_two_sub_three_pi_div_four]
  -- Now: |√2/2 - (-√2/2) + √2/2 + √2/2| = |4·(√2/2)| = 2·√2
  have h_sum :
      Real.sqrt 2 / 2 - -Real.sqrt 2 / 2 + Real.sqrt 2 / 2 + Real.sqrt 2 / 2
        = 2 * Real.sqrt 2 := by ring
  rw [h_sum]
  rw [abs_of_pos]
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))

/-! ## §6 — Comparison to the classical bound -/

/-- **`2·√2 > 2`** — the quantum CHSH value strictly exceeds the
classical bound. -/
theorem two_sqrt_two_gt_two : 2 * Real.sqrt 2 > 2 := by
  have h : Real.sqrt 2 > 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- **Quantum CHSH exceeds the classical bound (rephrased)**:
The CHSH expression for the quantum correlation at the Tsirelson
angles is strictly greater than `2` — i.e. ruling out any local
hidden-variable model.

This is the **load-bearing physics theorem** of the file: the
quantum prediction violates the local-realist bound. -/
theorem chsh_quantum_exceeds_classical_bound :
    chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) > 2 := by
  rw [chsh_quantum_at_tsirelson_angles]
  exact two_sqrt_two_gt_two

end Physlib.QuantumMechanics.Entanglement

end
