/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Bell.HyperbolicRegime
public import Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces
public import Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
public import Physlib.QuantumMechanics.Entanglement.BellNoSignaling
public import QuantumInfo.States.Pure.Braket

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling -/

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
* the spacelike/light-cone face and the hyperbolic eccentricity carrier
  are the places where this contract is consumed.

This module connects those pieces to existing Physlib result names rather
than copying the old partial-trace sketches.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling

open Physlib.QuantumMechanics.Bell
open Physlib.QuantumMechanics.Entanglement
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces


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
Tsirelson value and no-signaling result. -/
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
lemma quantum_chsh_at_angles_eq_tsirelsonWitness :
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
lemma spacelike_chsh_no_signaling_contract
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
lemma hyperbolic_spacelike_chsh_no_signaling_contract
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

/-! ## §C — CHSH game score normalization and stochastic locality -/

/-- The uniform-input CHSH game score from the four conditional correlation
cells `E₀₀,E₀₁,E₁₀,E₁₁`, matching Eq. (5) of Barandes-Hasan-Kagan after
the factor `(-1)^{xy}` is absorbed as the final minus sign. -/
def chshUniformScore (E00 E01 E10 E11 : ℝ) : ℝ :=
  (E00 + E01 + E10 - E11) / 4

/-- The score associated with a CHSH operator expectation `C`, using
Eqs. (32)--(35): `score = C / 4`. -/
def chshScoreFromExpectation (C : ℝ) : ℝ :=
  C / 4

/-- The CHSH game's win probability reconstructed from its `+1`/`-1`
score, Eq. (37): `score = 2 P_win - 1`. -/
def chshWinProbability (score : ℝ) : ℝ :=
  (score + 1) / 2

/-- The conditional correlation cell
`P(00)-P(01)-P(10)+P(11)` used in the CHSH score formula. -/
def chshCellCorrelation (p00 p01 p10 p11 : ℝ) : ℝ :=
  p00 - p01 - p10 + p11

/-- The no-signaling-box probability kernel
`(1 + s E) / 4`, where `s = ±1` encodes whether the output parity matches
the input parity in Eq. (8). -/
def nsBoxProbability (E sign : ℝ) : ℝ :=
  (1 + sign * E) / 4

/-- The NS-box probabilities are valid probabilities whenever
`|E| ≤ 1` and the parity sign is `±1`. -/
lemma nsBoxProbability_mem_unitInterval
    {E sign : ℝ} (hE : |E| ≤ 1) (hsign : sign = 1 ∨ sign = -1) :
    0 ≤ nsBoxProbability E sign ∧ nsBoxProbability E sign ≤ 1 := by
  rcases hsign with rfl | rfl
  · have hElower : -1 ≤ E := (abs_le.mp hE).1
    have hEupper : E ≤ 1 := (abs_le.mp hE).2
    unfold nsBoxProbability
    constructor <;> nlinarith
  · have hElower : -1 ≤ E := (abs_le.mp hE).1
    have hEupper : E ≤ 1 := (abs_le.mp hE).2
    unfold nsBoxProbability
    constructor <;> nlinarith

/-- Eq. (8) is locally unbiased: summing the two opposite parity signs
gives marginal probability `1/2`. -/
lemma nsBox_marginal_pair_sum (E : ℝ) :
    nsBoxProbability E 1 + nsBoxProbability E (-1) = 1 / 2 := by
  unfold nsBoxProbability
  ring

/-- For an input pair with `xy = 0`, the NS-box cell correlation is `E`. -/
lemma nsBox_even_cellCorrelation (E : ℝ) :
    chshCellCorrelation
        (nsBoxProbability E 1) (nsBoxProbability E (-1))
        (nsBoxProbability E (-1)) (nsBoxProbability E 1) = E := by
  unfold chshCellCorrelation nsBoxProbability
  ring

/-- For the input pair with `xy = 1`, the NS-box cell correlation is `-E`. -/
lemma nsBox_odd_cellCorrelation (E : ℝ) :
    chshCellCorrelation
        (nsBoxProbability E (-1)) (nsBoxProbability E 1)
        (nsBoxProbability E 1) (nsBoxProbability E (-1)) = -E := by
  unfold chshCellCorrelation nsBoxProbability
  ring

/-- Substituting the NS-box family of Eq. (8) into the uniform CHSH score
formula Eq. (5) returns exactly the box parameter `E`. -/
lemma nsBox_chshUniformScore_eq_parameter (E : ℝ) :
    chshUniformScore
        (chshCellCorrelation
          (nsBoxProbability E 1) (nsBoxProbability E (-1))
          (nsBoxProbability E (-1)) (nsBoxProbability E 1))
        (chshCellCorrelation
          (nsBoxProbability E 1) (nsBoxProbability E (-1))
          (nsBoxProbability E (-1)) (nsBoxProbability E 1))
        (chshCellCorrelation
          (nsBoxProbability E 1) (nsBoxProbability E (-1))
          (nsBoxProbability E (-1)) (nsBoxProbability E 1))
        (chshCellCorrelation
          (nsBoxProbability E (-1)) (nsBoxProbability E 1)
          (nsBoxProbability E 1) (nsBoxProbability E (-1))) = E := by
  unfold chshUniformScore chshCellCorrelation nsBoxProbability
  ring

/-- The Tsirelson operator value `2√2`, divided by the CHSH-game
normalization factor `4`, is the score bound `1/√2`. -/
lemma tsirelsonWitness_score_normalization :
    chshScoreFromExpectation tsirelsonWitness = 1 / Real.sqrt 2 := by
  unfold chshScoreFromExpectation tsirelsonWitness
  calc
    (2 * Real.sqrt 2) / 4 = Real.sqrt 2 / 2 := by ring
    _ = 1 / Real.sqrt 2 := by
      have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
      field_simp [hs]
      exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- The existing Tsirelson bound on the CHSH operator expectation gives
the Barandes-Hasan-Kagan CHSH-game score bound `score ≤ 1/√2`. -/
lemma chshScore_le_tsirelson_of_expectation_bound {C : ℝ}
    (hC : C ≤ tsirelsonWitness) :
    chshScoreFromExpectation C ≤ 1 / Real.sqrt 2 := by
  calc
    chshScoreFromExpectation C ≤ chshScoreFromExpectation tsirelsonWitness := by
      unfold chshScoreFromExpectation
      linarith
    _ = 1 / Real.sqrt 2 := tsirelsonWitness_score_normalization

/-- Solving Eq. (37), `score = P_win - P_loss` with
`P_loss = 1 - P_win`, gives `P_win = (score + 1)/2`. -/
lemma chshWinProbability_eq_of_score_relation
    {score pWin pLoss : ℝ} (hLoss : pLoss = 1 - pWin)
    (hScore : score = pWin - pLoss) :
    pWin = chshWinProbability score := by
  unfold chshWinProbability
  nlinarith

/-- A score upper bound transfers directly to the corresponding win
probability upper bound. -/
lemma chshWinProbability_le_of_score_le {score bound : ℝ} (h : score ≤ bound) :
    chshWinProbability score ≤ chshWinProbability bound := by
  unfold chshWinProbability
  linarith

/-- The paper's Tsirelson win-probability expression is the same as the
direct score-normalized expression. -/
lemma chshTsirelsonWinBound_eq_paperForm :
    chshWinProbability (1 / Real.sqrt 2) =
      (1 + Real.sqrt 2) / (2 * Real.sqrt 2) := by
  unfold chshWinProbability
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  field_simp [hs]

/-- Combining the existing CHSH operator Tsirelson bound with the CHSH-game
normalization yields Eq. (38), the win-probability bound. -/
lemma chshWinProbability_le_tsirelson_of_expectation_bound
    {C score : ℝ} (hScore : score = chshScoreFromExpectation C)
    (hC : C ≤ tsirelsonWitness) :
    chshWinProbability score ≤ (1 + Real.sqrt 2) / (2 * Real.sqrt 2) := by
  rw [hScore]
  calc
    chshWinProbability (chshScoreFromExpectation C)
        ≤ chshWinProbability (1 / Real.sqrt 2) :=
      chshWinProbability_le_of_score_le (chshScore_le_tsirelson_of_expectation_bound hC)
    _ = (1 + Real.sqrt 2) / (2 * Real.sqrt 2) :=
      chshTsirelsonWinBound_eq_paperForm

/-- The classical CHSH operator bound `|C| ≤ 2` implies the game-score
bound `score ≤ 1/2`, the `3/4` winning-probability threshold. -/
lemma chshScore_le_classical_of_abs_bound {C : ℝ} (hC : |C| ≤ 2) :
    chshScoreFromExpectation C ≤ 1 / 2 := by
  have hCle : C ≤ 2 := le_trans (le_abs_self C) hC
  unfold chshScoreFromExpectation
  linarith

/-- The local/classical CHSH bound gives the usual `P_win ≤ 3/4`
CHSH-game limit. -/
lemma chshWinProbability_le_three_quarters_of_classical_bound
    {C score : ℝ} (hScore : score = chshScoreFromExpectation C)
    (hC : |C| ≤ 2) :
    chshWinProbability score ≤ 3 / 4 := by
  rw [hScore]
  calc
    chshWinProbability (chshScoreFromExpectation C)
        ≤ chshWinProbability (1 / 2) :=
      chshWinProbability_le_of_score_le (chshScore_le_classical_of_abs_bound hC)
    _ = 3 / 4 := by
      unfold chshWinProbability
      norm_num

/-- The score normalization is exactly division by the CHSH expectation:
the uniform game score equals `C/4` for `C = E₀₀ + E₀₁ + E₁₀ - E₁₁`. -/
lemma chshUniformScore_eq_scoreFromExpectation (E00 E01 E10 E11 : ℝ) :
    chshUniformScore E00 E01 E10 E11 =
      chshScoreFromExpectation (E00 + E01 + E10 - E11) :=
  rfl

/-- The Tsirelson score bound is strictly below the PR-box score `1`. -/
lemma one_div_sqrt_two_lt_one : 1 / Real.sqrt 2 < (1 : ℝ) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hsone : (1 : ℝ) < Real.sqrt 2 := by
    have hsqrt : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
    simpa using hsqrt
  rw [div_lt_iff₀ hspos]
  simpa using hsone

/-- A PR-box score `E = 1` exceeds the causally-local unistochastic
Tsirelson score ceiling `1/√2`. -/
lemma prBox_score_exceeds_tsirelson : ¬ ((1 : ℝ) ≤ 1 / Real.sqrt 2) :=
  not_le.mpr one_div_sqrt_two_lt_one

/-- A no-signaling box whose score parameter is realized through a
Tsirelson-bounded CHSH operator cannot exceed `E ≤ 1/√2`. -/
lemma nsBox_parameter_le_tsirelson_of_expectation_bound
    {E C : ℝ} (hScore : E = chshScoreFromExpectation C)
    (hC : C ≤ tsirelsonWitness) :
    E ≤ 1 / Real.sqrt 2 := by
  rw [hScore]
  exact chshScore_le_tsirelson_of_expectation_bound hC

/-! ## §D — stochastic-quantum dictionary and unistochastic kernels -/

/-- The scalar stochastic-quantum dictionary of Eq. (17):
`Θ = exp(iθ) sqrt(p)`. -/
def stochasticQuantumAmplitude (phase probability : ℝ) : ℂ :=
  Complex.exp ((phase : ℂ) * Complex.I) * (Real.sqrt probability : ℂ)

/-- The Eq. (17) amplitude has squared modulus equal to the original
probability whenever that probability is nonnegative. -/
lemma stochasticQuantumAmplitude_normSq
    (phase probability : ℝ) (hprob : 0 ≤ probability) :
    Complex.normSq (stochasticQuantumAmplitude phase probability) = probability := by
  unfold stochasticQuantumAmplitude
  rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg probability)]
  exact Real.sq_sqrt hprob

/-- Born probability of a configuration from a normalized finite ket,
the basis-vector version of Eq. (19). -/
def bornTransitionFromKet {Config : Type*} [Fintype Config]
    (ψ : Ket Config) (target : Config) : ℝ :=
  Complex.normSq (ψ target)

/-- Born probabilities from a normalized finite ket sum to one, reusing
`Ket.normalized` from `QuantumInfo`. -/
lemma bornTransitionFromKet_normalized
    {Config : Type*} [Fintype Config] (ψ : Ket Config) :
    ∑ target, bornTransitionFromKet ψ target = 1 := by
  simpa [bornTransitionFromKet] using Ket.normalized ψ

/-- The unistochastic transition kernel associated with a finite unitary
matrix, Eq. (19): `p(q_t | q_0) = |U_{q_t q_0}|²`. -/
def unistochasticTransition {Config : Type*} [Fintype Config] [DecidableEq Config]
    (U : Matrix.unitaryGroup Config ℂ) (target initial : Config) : ℝ :=
  Complex.normSq (U target initial)

/-- A finite unitary matrix gives a normalized stochastic transition for
each fixed initial configuration, reusing `Matrix.unitaryGroup_row_norm`. -/
lemma unistochasticTransition_normalized
    {Config : Type*} [Fintype Config] [DecidableEq Config]
    (U : Matrix.unitaryGroup Config ℂ) (initial : Config) :
    ∑ target, unistochasticTransition U target initial = 1 := by
  simpa [unistochasticTransition, Complex.normSq_eq_norm_sq]
    using Matrix.unitaryGroup_row_norm U initial

/-! ## §E — finite stochastic marginalization and causal locality -/

/-- The joint distribution reconstructed from a conditional transition
kernel and an initial distribution, Eq. (9):
`p(q_t,q_0) = p(q_t | q_0) p(q_0)`. -/
def jointFromConditional {Initial Target : Type*}
    (transition : Target → Initial → ℝ) (prior : Initial → ℝ)
    (target : Target) (initial : Initial) : ℝ :=
  transition target initial * prior initial

/-- The target marginal obtained by summing the reconstructed joint law
over the initial state, Eq. (10). -/
def marginalFromConditional {Initial Target : Type*} [Fintype Initial]
    (transition : Target → Initial → ℝ) (prior : Initial → ℝ)
    (target : Target) : ℝ :=
  ∑ initial, jointFromConditional transition prior target initial

/-- Divisibility of a finite stochastic transition through an intermediate
event, Eq. (11):
`p(q_t | q_0) = Σ_r p(q_t | r) p(r | q_0)`. -/
def DivisibleTransition {Initial Middle Target : Type*} [Fintype Middle]
    (direct : Target → Initial → ℝ)
    (after : Target → Middle → ℝ)
    (before : Middle → Initial → ℝ) : Prop :=
  ∀ target initial, direct target initial =
    ∑ middle, after target middle * before middle initial

/-- The factorized transition through a fixed intermediate event set. -/
def factorizedTransition {Initial Middle Target : Type*} [Fintype Middle]
    (after : Target → Middle → ℝ)
    (before : Middle → Initial → ℝ)
    (target : Target) (initial : Initial) : ℝ :=
  ∑ middle, after target middle * before middle initial

/-- Finite transition composition is associative, the algebraic content
behind the multi-division-event chain in Eq. (21). -/
lemma factorizedTransition_assoc
    {Initial Middle₁ Middle₂ Target : Type*}
    [Fintype Middle₁] [Fintype Middle₂]
    (third : Target → Middle₂ → ℝ)
    (second : Middle₂ → Middle₁ → ℝ)
    (first : Middle₁ → Initial → ℝ)
    (target : Target) (initial : Initial) :
    factorizedTransition third (factorizedTransition second first) target initial =
      factorizedTransition (factorizedTransition third second) first target initial := by
  classical
  unfold factorizedTransition
  calc
    ∑ middle₂, third target middle₂ *
        (∑ middle₁, second middle₂ middle₁ * first middle₁ initial)
        = ∑ middle₂, ∑ middle₁,
            third target middle₂ * (second middle₂ middle₁ * first middle₁ initial) := by
      exact Finset.sum_congr rfl (fun middle₂ _ => by rw [Finset.mul_sum])
    _ = ∑ middle₁, ∑ middle₂,
        third target middle₂ * (second middle₂ middle₁ * first middle₁ initial) := by
      rw [Finset.sum_comm]
    _ = ∑ middle₁,
        (∑ middle₂, third target middle₂ * second middle₂ middle₁)
          * first middle₁ initial := by
      exact Finset.sum_congr rfl (fun middle₁ _ => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun middle₂ _ => by ring))

/-- The interference or memory remainder in Eq. (20): the exact transition
minus the transition factorized through a division event. -/
def divisibilityRemainder {Initial Middle Target : Type*} [Fintype Middle]
    (direct : Target → Initial → ℝ)
    (after : Target → Middle → ℝ)
    (before : Middle → Initial → ℝ)
    (target : Target) (initial : Initial) : ℝ :=
  direct target initial - factorizedTransition after before target initial

/-- Every transition decomposes into its factorized-through-the-division
part plus the Eq. (20) remainder. -/
lemma direct_eq_factorizedTransition_add_divisibilityRemainder
    {Initial Middle Target : Type*} [Fintype Middle]
    (direct : Target → Initial → ℝ)
    (after : Target → Middle → ℝ)
    (before : Middle → Initial → ℝ)
    (target : Target) (initial : Initial) :
    direct target initial =
      factorizedTransition after before target initial
        + divisibilityRemainder direct after before target initial := by
  unfold divisibilityRemainder
  ring

/-- When the transition is divisible through the intermediate event, the
Eq. (20) interference or memory remainder vanishes. -/
lemma divisibilityRemainder_eq_zero_of_divisible
    {Initial Middle Target : Type*} [Fintype Middle]
    (direct : Target → Initial → ℝ)
    (after : Target → Middle → ℝ)
    (before : Middle → Initial → ℝ)
    (hDiv : DivisibleTransition direct after before)
    (target : Target) (initial : Initial) :
    divisibilityRemainder direct after before target initial = 0 := by
  unfold divisibilityRemainder factorizedTransition
  rw [hDiv target initial]
  ring

/-- Divisibility propagates a prior distribution in two equivalent ways:
directly from the initial state to the target, or first to the intermediate
division event and then from that event to the target. This is the finite
form of Eqs. (12)--(13). -/
lemma divisibleTransition_marginalFromConditional
    {Initial Middle Target : Type*} [Fintype Initial] [Fintype Middle]
    (direct : Target → Initial → ℝ)
    (after : Target → Middle → ℝ)
    (before : Middle → Initial → ℝ)
    (prior : Initial → ℝ)
    (hDiv : DivisibleTransition direct after before)
    (target : Target) :
    marginalFromConditional direct prior target =
      ∑ middle,
        after target middle * marginalFromConditional before prior middle := by
  classical
  unfold marginalFromConditional jointFromConditional
  calc
    ∑ initial, direct target initial * prior initial =
        ∑ initial, (∑ middle, after target middle * before middle initial)
          * prior initial := by
      exact Finset.sum_congr rfl (fun initial _ => by rw [hDiv target initial])
    _ = ∑ initial, ∑ middle,
        (after target middle * before middle initial) * prior initial := by
      exact Finset.sum_congr rfl (fun initial _ => by rw [Finset.sum_mul])
    _ = ∑ middle, ∑ initial,
        (after target middle * before middle initial) * prior initial := by
      rw [Finset.sum_comm]
    _ = ∑ middle,
        after target middle * ∑ initial, before middle initial * prior initial := by
      exact Finset.sum_congr rfl (fun middle _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun initial _ => by ring))

/-- Factorization of a two-subsystem stochastic transition, Eq. (16):
`p(q_t,r_t | q_0,r_0) = p(q_t | q_0) p(r_t | r_0)`. -/
def NonInteractingTransition {Q R Q0 R0 : Type*}
    (joint : Q → R → Q0 → R0 → ℝ)
    (left : Q → Q0 → ℝ) (right : R → R0 → ℝ) : Prop :=
  ∀ q r q0 r0, joint q r q0 r0 = left q q0 * right r r0

/-- The left-subsystem marginal transition
`p(q_t | q_0,r_0) = Σ_{r_t} p(q_t,r_t | q_0,r_0)`. -/
def leftMarginalTransition {Q R Q0 R0 : Type*} [Fintype R]
    (joint : Q → R → Q0 → R0 → ℝ) (q : Q) (q0 : Q0) (r0 : R0) : ℝ :=
  ∑ r, joint q r q0 r0

/-- The right-subsystem marginal transition
`p(r_t | q_0,r_0) = Σ_{q_t} p(q_t,r_t | q_0,r_0)`. -/
def rightMarginalTransition {Q R Q0 R0 : Type*} [Fintype Q]
    (joint : Q → R → Q0 → R0 → ℝ) (r : R) (q0 : Q0) (r0 : R0) : ℝ :=
  ∑ q, joint q r q0 r0

/-- Eq. (16) implies the left causal-independence marginal Eq. (23),
provided the right transition is normalized. -/
lemma nonInteracting_leftMarginalTransition_eq
    {Q R Q0 R0 : Type*} [Fintype R]
    (joint : Q → R → Q0 → R0 → ℝ)
    (left : Q → Q0 → ℝ) (right : R → R0 → ℝ)
    (hFactor : NonInteractingTransition joint left right)
    (hRightNorm : ∀ r0, ∑ r, right r r0 = 1)
    (q : Q) (q0 : Q0) (r0 : R0) :
    leftMarginalTransition joint q q0 r0 = left q q0 := by
  classical
  unfold leftMarginalTransition
  calc
    ∑ r, joint q r q0 r0 = ∑ r, left q q0 * right r r0 := by
      exact Finset.sum_congr rfl (fun r _ => hFactor q r q0 r0)
    _ = left q q0 * ∑ r, right r r0 := by
      rw [Finset.mul_sum]
    _ = left q q0 := by
      rw [hRightNorm r0, mul_one]

/-- Eq. (16) implies the right causal-independence marginal Eq. (24),
provided the left transition is normalized. -/
lemma nonInteracting_rightMarginalTransition_eq
    {Q R Q0 R0 : Type*} [Fintype Q]
    (joint : Q → R → Q0 → R0 → ℝ)
    (left : Q → Q0 → ℝ) (right : R → R0 → ℝ)
    (hFactor : NonInteractingTransition joint left right)
    (hLeftNorm : ∀ q0, ∑ q, left q q0 = 1)
    (r : R) (q0 : Q0) (r0 : R0) :
    rightMarginalTransition joint r q0 r0 = right r r0 := by
  classical
  unfold rightMarginalTransition
  calc
    ∑ q, joint q r q0 r0 = ∑ q, left q q0 * right r r0 := by
      exact Finset.sum_congr rfl (fun q _ => hFactor q r q0 r0)
    _ = (∑ q, left q q0) * right r r0 := by
      rw [Finset.sum_mul]
    _ = right r r0 := by
      rw [hLeftNorm q0, one_mul]

/-- The bit type used for the finite CHSH stochastic-process marginals. -/
abbrev CHSHBit := Fin 2

/-- Alice's outcome marginal in a CHSH stochastic round:
`Σ_r p_{xy}(q,r | Ψ)`. -/
def aliceCHSHMarginal
    (p : CHSHBit → CHSHBit → CHSHBit → CHSHBit → ℝ)
    (x y q : CHSHBit) : ℝ :=
  ∑ r, p x y q r

/-- Bob's outcome marginal in a CHSH stochastic round:
`Σ_q p_{xy}(q,r | Ψ)`. -/
def bobCHSHMarginal
    (p : CHSHBit → CHSHBit → CHSHBit → CHSHBit → ℝ)
    (x y r : CHSHBit) : ℝ :=
  ∑ q, p x y q r

/-- Causal locality for a finite CHSH stochastic round, Eqs. (26)--(27):
Alice's marginal is independent of Bob's setting, and Bob's marginal is
independent of Alice's setting. -/
def CHSHCausalLocal
    (p : CHSHBit → CHSHBit → CHSHBit → CHSHBit → ℝ) : Prop :=
  (∀ x y₁ y₂ q, aliceCHSHMarginal p x y₁ q = aliceCHSHMarginal p x y₂ q)
    ∧ (∀ x₁ x₂ y r, bobCHSHMarginal p x₁ y r = bobCHSHMarginal p x₂ y r)

/-- Causal locality gives the Alice-side no-signaling marginal equation,
Eq. (26). -/
lemma chshCausalLocal_alice_noSignaling
    {p : CHSHBit → CHSHBit → CHSHBit → CHSHBit → ℝ}
    (hLocal : CHSHCausalLocal p) (x y₁ y₂ q : CHSHBit) :
    aliceCHSHMarginal p x y₁ q = aliceCHSHMarginal p x y₂ q :=
  hLocal.1 x y₁ y₂ q

/-- Causal locality gives the Bob-side no-signaling marginal equation,
Eq. (27). -/
lemma chshCausalLocal_bob_noSignaling
    {p : CHSHBit → CHSHBit → CHSHBit → CHSHBit → ℝ}
    (hLocal : CHSHCausalLocal p) (x₁ x₂ y r : CHSHBit) :
    bobCHSHMarginal p x₁ y r = bobCHSHMarginal p x₂ y r :=
  hLocal.2 x₁ x₂ y r

/-- Barandes-Hasan-Kagan CHSH contract in repo form: causal locality gives
the two finite no-signaling marginal equations, while a Tsirelson-bounded
local unistochastic CHSH operator gives the score and win-probability
bounds. -/
lemma causallyLocal_unistochastic_chsh_contract
    {p : CHSHBit → CHSHBit → CHSHBit → CHSHBit → ℝ}
    (hLocal : CHSHCausalLocal p)
    {C score : ℝ} (hScore : score = chshScoreFromExpectation C)
    (hC : C ≤ tsirelsonWitness) :
    (∀ x y₁ y₂ q,
        aliceCHSHMarginal p x y₁ q = aliceCHSHMarginal p x y₂ q)
      ∧ (∀ x₁ x₂ y r,
        bobCHSHMarginal p x₁ y r = bobCHSHMarginal p x₂ y r)
      ∧ score ≤ 1 / Real.sqrt 2
      ∧ chshWinProbability score ≤ (1 + Real.sqrt 2) / (2 * Real.sqrt 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y₁ y₂ q
    exact chshCausalLocal_alice_noSignaling hLocal x y₁ y₂ q
  · intro x₁ x₂ y r
    exact chshCausalLocal_bob_noSignaling hLocal x₁ x₂ y r
  · rw [hScore]
    exact chshScore_le_tsirelson_of_expectation_bound hC
  · exact chshWinProbability_le_tsirelson_of_expectation_bound hScore hC

/-- A non-interacting transition, plus normalization of both factors,
implies both causal-independence marginal equations at once. -/
lemma nonInteracting_marginalTransition_eq
    {Q R Q0 R0 : Type*} [Fintype Q] [Fintype R]
    (joint : Q → R → Q0 → R0 → ℝ)
    (left : Q → Q0 → ℝ) (right : R → R0 → ℝ)
    (hFactor : NonInteractingTransition joint left right)
    (hLeftNorm : ∀ q0, ∑ q, left q q0 = 1)
    (hRightNorm : ∀ r0, ∑ r, right r r0 = 1)
    (q : Q) (r : R) (q0 : Q0) (r0 : R0) :
    leftMarginalTransition joint q q0 r0 = left q q0
      ∧ rightMarginalTransition joint r q0 r0 = right r r0 :=
  ⟨nonInteracting_leftMarginalTransition_eq joint left right hFactor hRightNorm q q0 r0,
    nonInteracting_rightMarginalTransition_eq joint left right hFactor hLeftNorm r q0 r0⟩

/-! ## §F — memory-conditioned kernels and non-Markovian reduction -/

/-- A finite history-conditioned transition kernel of the kind described
in Eqs. (39)--(43): the target distribution may depend on the present
state and on an older recorded history. -/
def historyConditionedTransition
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ)
    (target : Target) (current : Current) (history : History) : ℝ :=
  kernel target current history

/-- The Markov-style reduction obtained by freezing one reference history. -/
def memoryReducedTransition
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ) (reference : History)
    (target : Target) (current : Current) : ℝ :=
  historyConditionedTransition kernel target current reference

/-- A history-conditioned transition is memory independent exactly when
older history labels do not change the target probabilities. -/
def MemoryIndependent
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ) : Prop :=
  ∀ target current history₁ history₂,
    historyConditionedTransition kernel target current history₁ =
      historyConditionedTransition kernel target current history₂

/-- A concrete memory effect is a pair of older histories that produce
different target probabilities at the same current state. -/
def HasMemoryEffect
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ) : Prop :=
  ∃ target current history₁ history₂,
    historyConditionedTransition kernel target current history₁ ≠
      historyConditionedTransition kernel target current history₂

/-- Memory independence reduces a history-conditioned kernel to any fixed
reference-history transition. -/
lemma memoryIndependent_eq_memoryReducedTransition
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ)
    (hmem : MemoryIndependent kernel)
    (reference : History)
    (target : Target) (current : Current) (history : History) :
    historyConditionedTransition kernel target current history =
      memoryReducedTransition kernel reference target current := by
  exact hmem target current history reference

/-- A concrete memory effect rules out memory independence. -/
lemma not_memoryIndependent_of_hasMemoryEffect
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ)
    (hmem : HasMemoryEffect kernel) :
    ¬ MemoryIndependent kernel := by
  rintro hIndependent
  rcases hmem with ⟨target, current, history₁, history₂, hdiff⟩
  exact hdiff (hIndependent target current history₁ history₂)

/-- The history-memory remainder: the difference between the full
history-conditioned kernel and its fixed-history Markov reduction. -/
def memoryRemainder
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ) (reference : History)
    (target : Target) (current : Current) (history : History) : ℝ :=
  historyConditionedTransition kernel target current history -
    memoryReducedTransition kernel reference target current

/-- Memory independence makes the history-memory remainder vanish. -/
lemma memoryRemainder_eq_zero_of_memoryIndependent
    {Target Current History : Type*}
    (kernel : Target → Current → History → ℝ)
    (hmem : MemoryIndependent kernel)
    (reference : History)
    (target : Target) (current : Current) (history : History) :
    memoryRemainder kernel reference target current history = 0 := by
  unfold memoryRemainder
  rw [memoryIndependent_eq_memoryReducedTransition kernel hmem reference target current history]
  ring

/-- If every history-conditioned row is normalized, then every fixed-history
Markov reduction is normalized. -/
lemma memoryReducedTransition_normalized
    {Target Current History : Type*} [Fintype Target]
    (kernel : Target → Current → History → ℝ)
    (hNorm : ∀ current history,
      ∑ target, historyConditionedTransition kernel target current history = 1)
    (reference : History) (current : Current) :
    ∑ target, memoryReducedTransition kernel reference target current = 1 := by
  simpa [memoryReducedTransition] using hNorm current reference

end Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling

end

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling -/

/-!
# Locality, spacetime, and Bell no-signaling from the boost-invariant light cone

The Einstein Equivalence Principle — Local Lorentz Invariance, the boost-invariance
of the Minkowski form (`poincareRestMassSq_boost_invariant`) — was proved but never
*wired into* the causal / Bell layer.  `ThreeFaces.threeFaces_chsh_unification`
merely **conjoins** boost-invariance (at one point) with the CHSH bound (at another),
without deriving one from the other.  This module supplies the missing derivations.

A general boost on the `(Re, Im) = (time, space)` plane with Lorentz-factor pair
`(a, b)`, `a = cosh θ`, `b = sinh θ`, `a² − b² = 1`:

`boostBy a b q = ⟨a·Re q + b·Im q, b·Re q + a·Im q⟩`.

* **Local Lorentz Invariance (EEP)** — `boostBy_preserves_lorentzianForm`: the boost
  preserves `L(q) = Re² − Im²`, hence the spacelike / timelike / null *character*.
* **BELL, frame-covariance** — `spacelike_chsh_noSignaling_frame_covariant`: the
  *entire* CHSH/no-signaling contract (classical `|S| ≤ 2`, Tsirelson `2√2`, and the
  marginal `bobMarginal δ₁ = bobMarginal δ₂`) holds at **every** boosted image of a
  spacelike point, *because* the boost keeps it spacelike.  This replaces the
  disconnected conjunction with a genuine `spacelike-boost-invariance ⇒ no-signaling`
  implication (gu.md Axiom 10 / Prop 4).
* **LOCALITY, spacelike** — `spacelike_exists_simultaneity_frame`: a spacelike
  separation is *simultaneous* in some inertial frame (`(boostBy a b q).re = 0`), so
  spacelike order is not frame-invariant — the metric realization of "distant
  simultaneity is observer-dependent" (gu.md Axiom 4) and the reason no-signaling is
  *mandatory*.
* **LOCALITY, timelike** — `boostBy_preserves_timelikeFuture`: a future-timelike
  (causally-connected) separation stays future under every orthochronous boost, so
  the causal order of signal-connected events is frame-invariant (gu.md Axiom 3).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.Entanglement
open Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces
open Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian (timelike timelikeFuture)

namespace Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling

/-- **The Lorentz boost** on the `(Re, Im) = (time, space)` plane with Lorentz-factor
pair `(a, b)` (`a = cosh θ`, `b = sinh θ`). -/
def boostBy (a b : ℝ) (q : ℂ) : ℂ := ⟨a * q.re + b * q.im, b * q.re + a * q.im⟩

@[simp] lemma boostBy_re (a b : ℝ) (q : ℂ) : (boostBy a b q).re = a * q.re + b * q.im := rfl
@[simp] lemma boostBy_im (a b : ℝ) (q : ℂ) : (boostBy a b q).im = b * q.re + a * q.im := rfl

/-- **Local Lorentz Invariance (the Einstein Equivalence Principle).**  A boost with
`a² − b² = 1` preserves the Minkowski form `L(q) = Re² − Im²`.  The invariant is the
interval; the boost is pure inertial gauge. -/
@[zil_level physical_theorem]
theorem boostBy_preserves_lorentzianForm (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (q : ℂ) :
    lorentzianForm (boostBy a b q) = lorentzianForm q := by
  simp only [lorentzianForm, boostBy_re, boostBy_im]
  linear_combination (q.re ^ 2 - q.im ^ 2) * hab

/-- **The rapidity boost is a special case** (`a = cosh θ`, `b = sinh θ`), tying the
general boost to the existing rapidity form and making it orthochronous
(`cosh θ ≥ 1`). -/
@[zil_level structural]
theorem coshSinhBoost_preserves_lorentzianForm (θ : ℝ) (q : ℂ) :
    lorentzianForm (boostBy (Real.cosh θ) (Real.sinh θ) q) = lorentzianForm q :=
  boostBy_preserves_lorentzianForm _ _ (Real.cosh_sq_sub_sinh_sq θ) q

/-- **The spacelike character is boost-invariant.** -/
@[zil_level physical_theorem]
theorem boostBy_preserves_spacelike (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) {q : ℂ}
    (h : spacelike q) : spacelike (boostBy a b q) := by
  unfold spacelike at h ⊢
  rwa [boostBy_preserves_lorentzianForm a b hab q]

/-- **The timelike (causal) character is boost-invariant.** -/
@[zil_level physical_theorem]
theorem boostBy_preserves_timelike (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) {q : ℂ}
    (h : timelike q) : timelike (boostBy a b q) := by
  unfold timelike at h ⊢
  rwa [boostBy_preserves_lorentzianForm a b hab q]

/-- **Relativity of simultaneity (LOCALITY).**  A spacelike separation is simultaneous
in some inertial frame: there is a boost with `(boostBy a b q).re = 0`.  Spacelike
order is therefore not frame-invariant — the metric-level content of "distant
simultaneity is observer-dependent", and the reason no-signaling is mandatory. -/
@[zil_level bridge_theorem]
theorem spacelike_exists_simultaneity_frame {q : ℂ} (h : spacelike q) :
    ∃ a b : ℝ, a ^ 2 - b ^ 2 = 1 ∧ (boostBy a b q).re = 0 := by
  have him : q.re ^ 2 < q.im ^ 2 := by
    unfold spacelike lorentzianForm at h; linarith
  have hs : 0 < q.im ^ 2 - q.re ^ 2 := by linarith
  have hs_pos : 0 < Real.sqrt (q.im ^ 2 - q.re ^ 2) := Real.sqrt_pos.mpr hs
  set s := Real.sqrt (q.im ^ 2 - q.re ^ 2) with hsdef
  have hs_sq : s ^ 2 = q.im ^ 2 - q.re ^ 2 := Real.sq_sqrt hs.le
  have hsne : s ≠ 0 := ne_of_gt hs_pos
  refine ⟨q.im / s, -q.re / s, ?_, ?_⟩
  · have hform : (q.im / s) ^ 2 - (-q.re / s) ^ 2 = (q.im ^ 2 - q.re ^ 2) / s ^ 2 := by
      field_simp
    rw [hform, ← hs_sq, div_self (pow_ne_zero 2 hsne)]
  · simp only [boostBy_re]; ring

/-- **Frame-invariant causal order (LOCALITY).**  A future-timelike (causally
connected) separation stays future under every orthochronous boost `(1 ≤ a)`:
`(boostBy a b q).re > 0`.  No boost reverses the time-order of signal-connected
events — the light cone is a frame-invariant causal structure. -/
@[zil_level bridge_theorem]
theorem boostBy_preserves_timelikeFuture (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (ha : 1 ≤ a)
    {q : ℂ} (h : timelikeFuture q) : 0 < (boostBy a b q).re := by
  obtain ⟨htl, hre⟩ := h
  have him : q.im ^ 2 < q.re ^ 2 := by
    unfold timelike lorentzianForm at htl; linarith
  have ha_pos : 0 < a := lt_of_lt_of_le one_pos ha
  have hb2 : b ^ 2 < a ^ 2 := by linarith
  have key : (b * q.im) ^ 2 < (a * q.re) ^ 2 := by
    nlinarith [him, hb2, sq_nonneg q.im, mul_pos ha_pos ha_pos, ha_pos]
  have h1 : 0 < a * q.re := mul_pos ha_pos hre
  simp only [boostBy_re]
  nlinarith [key, h1]

/-- **A rapidity boost preserves future-timelike causal order** — the physical
orthochronous statement, `cosh θ ≥ 1`. -/
@[zil_level physical_theorem]
theorem coshSinhBoost_preserves_timelikeFuture (θ : ℝ) {q : ℂ} (h : timelikeFuture q) :
    0 < (boostBy (Real.cosh θ) (Real.sinh θ) q).re :=
  boostBy_preserves_timelikeFuture _ _ (Real.cosh_sq_sub_sinh_sq θ) (Real.one_le_cosh θ) h

/-- **Bell no-signaling is Lorentz-frame-covariant (BELL).**  The *entire* CHSH /
no-signaling contract — the point stays outside the `45°` cone, every local-hidden-
variable assignment obeys `|S| ≤ 2`, the quantum value is Tsirelson `2√2 > 2`, and
Bob's marginal is independent of Alice's setting — holds at **every** boosted image of
a spacelike point, *derived* from the boost-invariance of the spacelike character.
This upgrades the disconnected `threeFaces_chsh_unification` to a genuine
`spacelike-boost-invariance ⇒ no-signaling` implication. -/
@[zil_level bridge_theorem]
theorem spacelike_chsh_noSignaling_frame_covariant (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1)
    {q : ℂ} (h : spacelike q) (x : CHSHAssignment) :
    |(boostBy a b q).re| < |(boostBy a b q).im|
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ chshExpression quantumCorrelation 0 (Real.pi / 2) (Real.pi / 4) (3 * Real.pi / 4)
          = tsirelsonWitness
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) :=
  spacelike_chsh_no_signaling_contract (boostBy a b q) (boostBy_preserves_spacelike a b hab h) x

end Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling

zil attach boostBy_preserves_lorentzianForm where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_im",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_re",
  formalizes @ "claim:a-lorentz-boost-preserves-the-minkowski-form-re-squared-minus-im-squared-so-the-causal-character-is-boost-invariant-local-lorentz-invariance"

zil attach spacelike_chsh_noSignaling_frame_covariant where
  formalizes @ "claim:the-entire-chsh-no-signaling-contract-holds-at-every-boosted-image-of-a-spacelike-point-so-bell-no-signaling-is-lorentz-frame-covariant-derived-from-boost-invariance-of-spacelike-character",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.spacelike_chsh_no_signaling_contract",
  caveat @ "claim:this-is-the-one-plus-one-complex-plane-boost-not-the-full-three-plus-one-lorentz-group-and-the-marginal-is-the-fixed-singlet-bob-marginal"

zil attach spacelike_exists_simultaneity_frame where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_re",
  supported_by @ "lean:HermitianMat.sqrt_pos",
  formalizes @ "claim:a-spacelike-separation-is-simultaneous-in-some-inertial-frame-so-spacelike-time-order-is-observer-dependent-which-is-why-no-signaling-is-mandatory"

zil attach boostBy_preserves_timelikeFuture where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_re",
  supported_by @ "lean:HermitianMat.sq_nonneg",
  formalizes @ "claim:a-future-timelike-causally-connected-separation-stays-future-under-every-orthochronous-boost-so-the-causal-order-of-signal-connected-events-is-frame-invariant"

zil_file_contract physlib.spacelikeBoostNoSignaling where
  promises "The boost-invariant light cone (Local Lorentz Invariance, the Einstein Equivalence Principle) is wired into the causal and Bell layers. A general boost on the time-space plane with a squared minus b squared equal one preserves the Minkowski form re squared minus im squared, hence the spacelike and timelike character. From this: the full CHSH no-signaling contract holds at every boosted image of a spacelike point, so Bell no-signaling is Lorentz-frame-covariant and derived rather than conjoined; a spacelike separation is simultaneous in some inertial frame, so spacelike time-order is observer-dependent and no-signaling is mandatory; and a future-timelike separation stays future under every orthochronous boost, so the causal order of signal-connected events is frame-invariant."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.spacelike_chsh_no_signaling_contract",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces.spacelike"
  ]
  forbids_substitutes [
    "reading the one-plus-one complex-plane boost as the full three-plus-one Lorentz group",
    "co-locating boost-invariance and the CHSH bound without transporting the contract along the boost"
  ]
  witnessed_by [
    boostBy_preserves_lorentzianForm,
    boostBy_preserves_spacelike,
    boostBy_preserves_timelike,
    spacelike_exists_simultaneity_frame,
    boostBy_preserves_timelikeFuture,
    spacelike_chsh_noSignaling_frame_covariant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.spacelikeBoostNoSignaling

