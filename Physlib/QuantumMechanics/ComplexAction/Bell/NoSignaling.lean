/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Bell.HyperbolicRegime
public import Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces
public import Physlib.QuantumMechanics.Entanglement.BellNoSignaling

/-!
# Bell/CHSH no-signaling bridge

Ports the useful Bell/CHSH bridge layer from the reference tree
(`AdSCFTEntropicEntanglementBridge`, `UnifiedTheoryBellBridge`,
`BellHyperbolicCausalNetworkBridge`, and `SubstrateBellBridge`) into a
Physlib-native form.

The source files contain several assumption-bundle versions of the same
physical point:

* deterministic local hidden variables obey `|S| ≤ 2`;
* quantum CHSH can reach the Tsirelson value `2√2`;
* the violation does not imply faster-than-light signaling, because Bob's
  marginal is invariant under Alice's setting;
* the spacelike/light-cone face and the hyperbolic eccentricity structure
  are the places where this contract is consumed.

This module connects those pieces to existing Physlib theorem names rather
than copying the old placeholder partial-trace contracts.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling

open Physlib.QuantumMechanics.Bell
open Physlib.QuantumMechanics.Entanglement
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces

/-! ## §1 — The spacelike no-signaling witness -/

/-- A CHSH witness on the spacelike/light-cone face that violates the
classical bound, respects Tsirelson, and includes the explicit
no-signaling marginal. -/
structure SpacelikeCHSHNoSignalingWitness where
  /-- The complex light-cone point. -/
  point : ℂ
  /-- The point lies on the spacelike/locality face. -/
  point_spacelike : spacelike point
  /-- The quantum CHSH value represented by this witness. -/
  quantumValue : ℝ
  /-- This witness uses the Tsirelson value. -/
  quantumValue_eq_tsirelson : quantumValue = tsirelsonWitness
  /-- The quantum value violates the classical bound `2`. -/
  violates_classical : 2 < quantumValue
  /-- The quantum value remains within the Tsirelson bound. -/
  respects_tsirelson : quantumValue ≤ tsirelsonWitness
  /-- Bob's marginal is independent of Alice's relative setting. -/
  bob_marginal_no_signaling : ∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂

/-- Canonical spacelike Bell witness built from the existing Physlib
Tsirelson value and no-signaling theorem. -/
noncomputable def canonicalSpacelikeCHSHNoSignalingWitness
    (q : ℂ) (hq : spacelike q) : SpacelikeCHSHNoSignalingWitness where
  point := q
  point_spacelike := hq
  quantumValue := tsirelsonWitness
  quantumValue_eq_tsirelson := rfl
  violates_classical := classical_lt_tsirelson
  respects_tsirelson := le_rfl
  bob_marginal_no_signaling := fun δ₁ δ₂ => alice_invisible_to_bob δ₁ δ₂

/-- The quantum CHSH value at the Tsirelson angles is Physlib's
`tsirelsonWitness`. -/
theorem quantum_chsh_at_angles_eq_tsirelsonWitness :
    chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) = tsirelsonWitness := by
  simpa [tsirelsonWitness] using
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles

/-- **Spacelike CHSH/no-signaling contract.**

On the spacelike face:

* the point is outside the `45°` light cone (`|Re q| < |Im q|`);
* every deterministic local-hidden-variable assignment satisfies
  `|S| ≤ 2`;
* the quantum Tsirelson-angle value is `2√2`;
* `2 < 2√2`;
* Bob's marginal is invariant under Alice's setting. -/
theorem spacelike_chsh_no_signaling_contract
    (q : ℂ) (hq : spacelike q) (x : CHSHAssignment) :
    |q.re| < |q.im|
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) = tsirelsonWitness
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hface := chsh_on_spacelike_face q hq x
  exact
    ⟨hface.1,
      hface.2.1,
      quantum_chsh_at_angles_eq_tsirelsonWitness,
      hface.2.2,
      fun δ₁ δ₂ => alice_invisible_to_bob δ₁ δ₂⟩

/-! ## §2 — Hyperbolic-regime adapter -/

/-- Hyperbolic eccentricity plus a spacelike CHSH/no-signaling witness.

This is the Physlib-native replacement for the reference tree's
hyperbolic Bell bridge: it uses `Bell.HyperbolicRegime` for the
eccentricity classification and the explicit no-signaling witness above
for the Bell side. -/
structure HyperbolicSpacelikeCHSHNoSignalingWitness
    extends SpacelikeCHSHNoSignalingWitness where
  /-- The eccentricity/correlation-length parameter. -/
  eccentricity : ℝ
  /-- The eccentricity is in the hyperbolic Bell regime. -/
  hyperbolic_regime : regimeOfEccentricity eccentricity = BellRegime.hyperbolic
  /-- The hyperbolic entropy-production rate is strictly positive. -/
  entropy_production_positive : 0 < entropyProductionRate eccentricity

/-- Construct the hyperbolic/spacelike witness from `e > 1` and a
spacelike light-cone point. -/
noncomputable def hyperbolicSpacelikeCHSHNoSignalingWitness
    (e : ℝ) (he : 1 < e) (q : ℂ) (hq : spacelike q) :
    HyperbolicSpacelikeCHSHNoSignalingWitness where
  toSpacelikeCHSHNoSignalingWitness := canonicalSpacelikeCHSHNoSignalingWitness q hq
  eccentricity := e
  hyperbolic_regime := (regime_hyperbolic_iff e).mpr he
  entropy_production_positive := entropyProductionRate_pos_of_e_gt_one e he

/-- **Hyperbolic Bell/no-signaling contract.**

Combines the hyperbolic-regime facts from `Bell.HyperbolicRegime` with
the spacelike CHSH/no-signaling contract. -/
theorem hyperbolic_spacelike_chsh_no_signaling_contract
    (e : ℝ) (he : 1 < e) (q : ℂ) (hq : spacelike q) (x : CHSHAssignment) :
    regimeOfEccentricity e = BellRegime.hyperbolic
      ∧ 0 < entropyProductionRate e
      ∧ |q.re| < |q.im|
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hsp := spacelike_chsh_no_signaling_contract q hq x
  exact
    ⟨(regime_hyperbolic_iff e).mpr he,
      entropyProductionRate_pos_of_e_gt_one e he,
      hsp.1,
      hsp.2.1,
      hsp.2.2.2.1,
      hsp.2.2.2.2⟩

end Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling

end
