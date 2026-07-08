/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Entanglement.CHSHInequality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Bell no-signaling marginal

Ports the Bell/no-signaling content from the reference tree's
`Spine/Bridges/BellInequality` and the `NoSpookyAction` re-export it
uses, but keeps the proof local to Physlib's existing CHSH angle
formalization.

The CHSH module already proves that the singlet-style correlation
`quantumCorrelation` reaches the Tsirelson value `2√2` at the standard
angles.  This file adds the companion no-signaling marginal:

* Bob's marginal
  `sin(δ/2)^2 / 2 + cos(δ/2)^2 / 2`
  is always `1/2`;
* therefore Alice's choice of setting cannot change Bob's marginal;
* the Tsirelson violation and the no-signaling statement are available in
  one theorem for downstream bridge modules.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Entanglement

open Real

/-! ## §1 — Bob's marginal in a Bell experiment -/

/-- **Bob's marginal probability** in the two-outcome Bell setup.

The relative angle `δ` changes the split between Bob's two outcomes, but
the sum of the two weighted probabilities is constant. -/
def bobMarginal (δ : ℝ) : ℝ :=
  Real.sin (δ / 2) ^ 2 / 2 + Real.cos (δ / 2) ^ 2 / 2

/-- **No-signaling marginal:** Bob's marginal is always `1/2`. -/
theorem bobMarginal_eq_half (δ : ℝ) : bobMarginal δ = 1 / 2 := by
  unfold bobMarginal
  have htrig : Real.sin (δ / 2) ^ 2 + Real.cos (δ / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (δ / 2)
  nlinarith

/-- **Alice's choice is invisible to Bob:** Bob's marginal is the same for
any two relative-angle choices. -/
theorem alice_invisible_to_bob (δ₁ δ₂ : ℝ) :
    bobMarginal δ₁ = bobMarginal δ₂ := by
  rw [bobMarginal_eq_half δ₁, bobMarginal_eq_half δ₂]

/-! ## §2 — Witness and CHSH assembly -/

/-- A compact witness that two Alice-side choices have the same Bob
marginal. -/
structure BellNoSignalingWitness where
  /-- First relative setting. -/
  leftSetting : ℝ
  /-- Second relative setting. -/
  rightSetting : ℝ
  /-- Bob's marginal at the first setting. -/
  leftMarginal : bobMarginal leftSetting = 1 / 2
  /-- Bob's marginal at the second setting. -/
  rightMarginal : bobMarginal rightSetting = 1 / 2
  /-- The two marginals agree. -/
  sameMarginal : bobMarginal leftSetting = bobMarginal rightSetting

/-- Canonical no-signaling witness for any two choices of Alice's setting. -/
noncomputable def mkBellNoSignalingWitness (δ₁ δ₂ : ℝ) : BellNoSignalingWitness where
  leftSetting := δ₁
  rightSetting := δ₂
  leftMarginal := bobMarginal_eq_half δ₁
  rightMarginal := bobMarginal_eq_half δ₂
  sameMarginal := alice_invisible_to_bob δ₁ δ₂

/-- **Bell violation with no signaling.**

The quantum CHSH value at the Tsirelson angles is `2√2`, it strictly
exceeds the classical bound `2`, and Bob's marginal is independent of
Alice's relative setting. -/
theorem chsh_tsirelson_violation_and_no_signaling :
    chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) = 2 * Real.sqrt 2
      ∧ chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) > 2
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) :=
  ⟨chsh_quantum_at_tsirelson_angles,
    chsh_quantum_exceeds_classical_bound,
    fun δ₁ δ₂ => alice_invisible_to_bob δ₁ δ₂⟩

end Physlib.QuantumMechanics.Entanglement

end
