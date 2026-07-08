/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

/-!
# Bell no-signaling and the Levi-Civita gravitational tensor

Connects the Bell/CHSH no-signaling bridge to the Levi-Civita
gravitational-tensor formalization.

The point of the connection is not to claim that the gravitational tensor
causes the Bell marginal invariance.  The load-bearing statement is a
compatibility contract:

* the spacelike Bell face has deterministic local bound `|S| ≤ 2`,
  Tsirelson value `2√2`, and Bob-marginal no-signaling;
* the Levi-Civita gravitational tensor satisfies the d'Alembert balance
  `T + A = 0` on an Einstein-field-equation solution;
* under the contracted Bianchi hypothesis, the same gravitational tensor
  is divergence-free;
* for the complex Einstein equation, the real sector is exactly the
  Levi-Civita balance while the Bell sector still has no-signaling.

This makes Bell no-signaling available to downstream gravity modules in
the same theorem shape as the existing Levi-Civita tensor facts, without
adding new axioms or new tensor definitions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaTensor

open Physlib.QuantumMechanics.Entanglement
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling
open Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

variable {ι : Type*}

/-! ## §1 — Bell no-signaling with the d'Alembert balance -/

/-- **Bell no-signaling is compatible with the Levi-Civita d'Alembert balance.**

On a spacelike Bell face, the CHSH side supplies the local deterministic
bound, the Tsirelson witness, and Bob-marginal no-signaling.  On the
gravity side, any solution of the Einstein field equation gives
Levi-Civita's gravitational/inertial tensor balance `T + A = 0`. -/
theorem leviCivita_dAlembert_bell_no_signaling
    (q : ℂ) (hq : spacelike q) (x : CHSHAssignment)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hEinstein : einsteinFieldEquation Ric scalarR g T κ) :
    T + gravitationalTensor Ric scalarR g κ = 0
      ∧ |q.re| < |q.im|
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) = tsirelsonWitness
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hBell := spacelike_chsh_no_signaling_contract q hq x
  exact
    ⟨dAlembert_balance Ric scalarR g T κ hκ hEinstein,
      hBell.1,
      hBell.2.1,
      hBell.2.2.1,
      hBell.2.2.2.1,
      hBell.2.2.2.2⟩

/-! ## §2 — Bell no-signaling with Bianchi divergence freedom -/

/-- **Bell no-signaling plus Levi-Civita gravitational divergence freedom.**

The contracted Bianchi identity makes the Levi-Civita gravitational
tensor divergence-free; the Bell side remains spacelike and no-signaling. -/
theorem leviCivita_divergenceFree_bell_no_signaling
    (q : ℂ) (hq : spacelike q) (x : CHSHAssignment)
    (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ) (κ : ℝ)
    (hBianchi : Div (einsteinTensor Ric scalarR g) = 0) :
    Div (gravitationalTensor Ric scalarR g κ) = 0
      ∧ |q.re| < |q.im|
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hBell := spacelike_chsh_no_signaling_contract q hq x
  exact
    ⟨gravitationalTensor_divergence_free Div Ric scalarR g κ hBianchi,
      hBell.1,
      hBell.2.1,
      hBell.2.2.2.1,
      hBell.2.2.2.2⟩

/-! ## §3 — Complex Einstein real sector plus Bell no-signaling -/

/-- **Complex Einstein real sector with Bell no-signaling.**

For the Nagao-Nielsen/complex-action field equation, the real part is
the Levi-Civita d'Alembert balance and the imaginary part is the entropic
curvature equation `Λ = κ • S`.  The Bell side simultaneously provides
the spacelike CHSH no-signaling contract. -/
theorem complexEinstein_realSector_bell_no_signaling
    (q : ℂ) (hq : spacelike q) (x : CHSHAssignment)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hComplex : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    T + gravitationalTensor Ric scalarR g κ = 0
      ∧ Λ = κ • S
      ∧ |q.re| < |q.im|
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) = tsirelsonWitness
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hLC := complexEinstein_real_is_dAlembert Ric scalarR g Λ T S κ hκ hComplex
  have hBell := spacelike_chsh_no_signaling_contract q hq x
  exact
    ⟨hLC.1,
      hLC.2,
      hBell.1,
      hBell.2.1,
      hBell.2.2.1,
      hBell.2.2.2.1,
      hBell.2.2.2.2⟩

end Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaTensor

end
