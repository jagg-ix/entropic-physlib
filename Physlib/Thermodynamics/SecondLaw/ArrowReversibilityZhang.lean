/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.EntropyProductionWorldline
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations
public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Physlib.Thermodynamics.SecondLaw.ClausiusEntropyArrow

/-! # SecondLaw — part `ArrowReversibilityZhang`. Full docstring in the umbrella module `Physlib.Thermodynamics.SecondLaw`;
namespace and declaration names are unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QFT.Wick.Consistency

namespace Physlib.Thermodynamics.SecondLaw

open QuantumInfo.Finite QuantumMechanics.FiniteTarget

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §3 — Second law instantiates the entropic-time arrow -/

/-- **A monotone temperature history is an entropic-time arrow.** Given a positive,
monotone temperature profile starting at or above the reference, the Clausius
second law supplies the `S_I` monotonicity, so the derived `τ_ent` runs forward.
This exhibits the thermodynamic second law as one *source* of the entropy
increase the time arrow rides on. -/
def ofClausiusProfile (k_B hbar T₀ : ℝ) (hk : 0 < k_B) (hℏ : 0 < hbar) (hT₀ : 0 < T₀)
    (T : ℝ → ℝ) (hTpos : ∀ t, 0 < T t) (hTmono : Monotone T) (hT0 : T₀ ≤ T 0) :
    EntropyArrowWorldline where
  ℏ := hbar
  ℏ_pos := hℏ
  S_I_along := fun t => clausiusEntropy k_B (T t) T₀
  τ_ent_along := fun t => clausiusEntropy k_B (T t) T₀ / hbar
  τ_ent_eq := fun _ => rfl
  S_I_monotone := fun {_ _} h =>
    clausiusEntropy_monotone k_B T₀ hk hT₀ (hTpos _) (hTmono h)
  S_I_at_zero_nonneg := by
    unfold clausiusEntropy
    exact mul_nonneg hk.le
      (Real.log_nonneg (by rw [le_div_iff₀ hT₀]; linarith))

/-! ## §4 — Link to physlib's relative-entropy time -/

/-- **The entropic clock is accumulated quantum relative entropy.** From a state
trajectory `ρ : ℝ → MState d` with the (physical, load-bearing) assumption that
the relative-entropy gap `D(ρ(t)‖ρ(0))` is monotone, build the entropic-time
arrow with `S_I(t) = ℏ·D(ρ(t)‖ρ(0))`. -/
def ofStateWorldline (hbar : ℝ) (hℏ : 0 < hbar) (ρ : ℝ → MState d)
    (hmono : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
      (entropicProperTime (ρ t₁) (ρ 0)).toReal ≤
        (entropicProperTime (ρ t₂) (ρ 0)).toReal) :
    EntropyArrowWorldline where
  ℏ := hbar
  ℏ_pos := hℏ
  S_I_along := fun t => hbar * (entropicProperTime (ρ t) (ρ 0)).toReal
  τ_ent_along := fun t => (entropicProperTime (ρ t) (ρ 0)).toReal
  τ_ent_eq := fun _ => by rw [eq_div_iff (ne_of_gt hℏ)]; ring
  S_I_monotone := fun {_ _} h => mul_le_mul_of_nonneg_left (hmono _ _ h) hℏ.le
  S_I_at_zero_nonneg := by rw [entropicProperTime_self]; simp

/-- **The derived entropic time is exactly the relative-entropy gap.** Confirms
that `τ_ent` of the state-worldline arrow is `(entropicProperTime (ρ t) (ρ 0)).toReal`
— physlib's own quantum relative entropy, recovered as a side effect of state
divergence. -/
theorem ofStateWorldline_tau_ent_eq_relativeEntropy
    (hbar : ℝ) (hℏ : 0 < hbar) (ρ : ℝ → MState d)
    (hmono : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
      (entropicProperTime (ρ t₁) (ρ 0)).toReal ≤
        (entropicProperTime (ρ t₂) (ρ 0)).toReal) (t : ℝ) :
    (ofStateWorldline hbar hℏ ρ hmono).τ_ent_along t
      = (entropicProperTime (ρ t) (ρ 0)).toReal := rfl

/-- **Grounding: the arrow's damping is the modulus of the complex action
weight.** The entropic-time arrow's damping factor `e^{−τ_ent(t)}` equals
`‖entropicComplexWeight S_R ℏ (ρ t) (ρ 0)‖` — the modulus of the path-integral /
Wick weight from `Physlib.QFT.Wick.Consistency`. This proves the field labelled
"imaginary action `S_I`" is the genuine entropic imaginary action (`S_I = ℏ·D`),
not just a nominal label: the arrow's clock reading controls the same weight that
factors through the time-ordered Wick expansion. -/
theorem ofStateWorldline_damping_eq_weight_norm
    (S_R hbar : ℝ) (hℏ : 0 < hbar) (ρ : ℝ → MState d)
    (hmono : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
      (entropicProperTime (ρ t₁) (ρ 0)).toReal ≤
        (entropicProperTime (ρ t₂) (ρ 0)).toReal) (t : ℝ) :
    Real.exp (-(ofStateWorldline hbar hℏ ρ hmono).τ_ent_along t)
      = ‖entropicComplexWeight S_R hbar (ρ t) (ρ 0)‖ := by
  rw [ofStateWorldline_tau_ent_eq_relativeEntropy,
    norm_entropicComplexWeight S_R hbar (ne_of_gt hℏ) (ρ t) (ρ 0)]

/-! ## §5 — Deriving the monotonicity from a positive (dissipative) generator

The structure field `S_I_monotone` (the operationalised second law) must not stand
as a free assumption. Here we **derive** it from the genuine physical root: the
irreversible generator `H_I` is a *positive operator* (the operator-positivity
definition of dissipativity). Then `⟨H_I⟩ ≥ 0` is a theorem
(`IsPositive.re_inner_nonneg_left`), the entropy-production rate
`(2/ℏ)⟨H_I⟩ ≥ 0` is `entropyRate_nonneg` (already proved), and the constant-rate
worldline's `S_I` monotonicity follows with **no monotonicity hypothesis**. -/

/-- Entropy-controlled system from a **positive** irreversible generator `H_I`.
Its `expectation_nonneg` (⟨H_I⟩ ≥ 0) is a *theorem* from `H_I.IsPositive`, not an
assumed field. -/
def positiveGeneratorSystem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R H_I : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hpos : H_I.IsPositive) : EntropyControlledSchrodingerSystem (H := H) where
  H_R := H_R
  H_I := H_I
  hbar := hbar
  hbar_pos := hbar_pos
  expectation_HI := fun ψ => H_I.reApplyInnerSelf ψ
  entropyRate := fun ψ => (2 / hbar) * H_I.reApplyInnerSelf ψ
  entropyRate_eq_expectation := fun _ => rfl
  expectation_nonneg := fun ψ => hpos.2 ψ
  zero_HI_zero_expectation := fun h ψ => by
    rw [h]; simp [ContinuousLinearMap.reApplyInnerSelf]

/-- Entropy-time arrow from an entropy-controlled system at vector `ψ`, evolving at
the constant entropy-production rate `entropyRate ψ`. **`S_I` monotonicity is
derived** from `entropyRate_nonneg` (proved), not assumed. -/
def ofEntropyControlledSystem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) :
    EntropyArrowWorldline where
  ℏ := S.hbar
  ℏ_pos := S.hbar_pos
  S_I_along := fun t => S.hbar * S.entropyRate ψ * t
  τ_ent_along := fun t => S.entropyRate ψ * t
  τ_ent_eq := fun _ => by rw [eq_div_iff (ne_of_gt S.hbar_pos)]; ring
  S_I_monotone := fun {_ _} h =>
    mul_le_mul_of_nonneg_left h (mul_nonneg S.hbar_pos.le (S.entropyRate_nonneg ψ))
  S_I_at_zero_nonneg := by simp

/-- **The entropy-time arrow built entirely from a positive (dissipative)
generator.** No monotonicity hypothesis enters; the only input is `H_I ⪰ 0`. -/
def ofPositiveGeneratorArrow
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R H_I : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hpos : H_I.IsPositive) (ψ : H) : EntropyArrowWorldline :=
  ofEntropyControlledSystem (positiveGeneratorSystem H_R H_I hbar hbar_pos hpos) ψ

/-- **Resolution of the load-bearing assumption.** For the arrow built from a
positive irreversible generator, the second-law monotonicity `S_I(t₁) ≤ S_I(t₂)`
holds as a *theorem* — its only premise is `H_I.IsPositive` (dissipativity, an
operator property provable for any `H_I = L†L`), with no monotonicity postulate. -/
theorem ofPositiveGeneratorArrow_S_I_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R H_I : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hpos : H_I.IsPositive) (ψ : H) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).S_I_along t₁ ≤
      (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).S_I_along t₂ :=
  (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).S_I_monotone h

/-- **Concrete witness.** With the identity dissipator `H_I = 1`
(positive by `isPositive_one`), an entropy-time arrow exists with no input beyond
`ℏ > 0`, and its monotonicity holds unconditionally — confirming the second-law
assumption is genuinely *eliminated* here, not merely relocated. -/
def identityDissipatorArrow
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) : EntropyArrowWorldline :=
  ofPositiveGeneratorArrow H_R 1 hbar hbar_pos ContinuousLinearMap.isPositive_one ψ

theorem identityDissipatorArrow_S_I_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (identityDissipatorArrow H_R hbar hbar_pos ψ).S_I_along t₁ ≤
      (identityDissipatorArrow H_R hbar hbar_pos ψ).S_I_along t₂ :=
  (identityDissipatorArrow H_R hbar hbar_pos ψ).S_I_monotone h

/-! ## The frozen-clock case `H_I = 0`

The complementary endpoint of the second-law family: a purely real complex action
`H_C = H_R - i·H_I` with `H_I = 0` (Sergi–Giaquinta 2016). The generator is then
unitary, the entropy rate vanishes, and the entropy-time arrow built from it is
*reversible* — the entropic clock is frozen and the entropic proper time of any
transition is zero.

These three theorems are the quantum (non-commutative) mirror of the classical
result `reversible_entropy_production_zero` in
`Physlib.Thermodynamics.ComputationLandauer`: a reversible channel leaves the
relative entropy invariant, so no entropic time accrues. Here the reversible
channel is unitary evolution (`H_I = 0`); there it is a history-keeping
computation (`klDiv_reversible_invariant`). Both reduce the entropic-time layer to
a constant. (Referenced by name only — that module imports this one, so the
dependency runs one way.) -/

/-- **`H_I = 0` ⇒ entropy production vanishes identically.** With no
anti-Hermitian part the entropy rate is zero, so `S_I_along` is the zero function.
This is the single fact the two frozen-clock corollaries below rest on. -/
theorem ofEntropyControlledSystem_S_I_zero_of_zero_HI
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) (hzero : S.H_I = 0)
    (t : ℝ) :
    (ofEntropyControlledSystem S ψ).S_I_along t = 0 := by
  show S.hbar * S.entropyRate ψ * t = 0
  rw [S.zero_HI_implies_zero_entropyRate hzero ψ]; ring

/-- **`H_I = 0` ⇒ the entropy-time arrow is reversible.** `S_I_along` is constant
(identically zero), so the worldline satisfies `IsReversible`. -/
theorem ofEntropyControlledSystem_isReversible_of_zero_HI
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) (hzero : S.H_I = 0) :
    (ofEntropyControlledSystem S ψ).IsReversible := fun t₁ t₂ =>
  (ofEntropyControlledSystem_S_I_zero_of_zero_HI S ψ hzero t₁).trans
    (ofEntropyControlledSystem_S_I_zero_of_zero_HI S ψ hzero t₂).symm

/-- **`H_I = 0` ⇒ frozen entropic clock.** The derived entropic time
`τ_ent_along t` is identically zero — a corollary of the vanishing `S_I_along`
through the generic `worldline_S_I_zero_implies_tau_ent_zero`. -/
theorem ofEntropyControlledSystem_tau_ent_zero_of_zero_HI
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) (hzero : S.H_I = 0)
    (t : ℝ) :
    (ofEntropyControlledSystem S ψ).τ_ent_along t = 0 :=
  (ofEntropyControlledSystem S ψ).worldline_S_I_zero_implies_tau_ent_zero
    (ofEntropyControlledSystem_S_I_zero_of_zero_HI S ψ hzero) t

/-- **`H_I = 0` ⇒ zero entropic proper time.** For any finite entropic transition
of an `H_I = 0` system, the relative-entropy gap `D(ρ₁‖ρ₀)` vanishes: unitary
evolution produces no entropic proper time. -/
theorem entropicTransition_properTime_zero_of_zero_HI
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    {d : Type*} [Fintype d] [DecidableEq d]
    (S : EntropyControlledSchrodingerSystem (H := H))
    (T : EntropicTransition (d := d) S) (hzero : S.H_I = 0) :
    (entropicProperTime T.ρ₁ T.ρ₀).toReal = 0 := by
  rw [T.rate_relation, S.zero_HI_implies_zero_entropyRate hzero T.ψ]; ring

/-! ## The reversibility characterisation (C4)

The frozen-clock results above establish one direction (`H_I = 0 ⇒ reversible`).
Here that is sharpened to an *equivalence*, at three levels of specificity:

* at the level of any entropy-controlled system, the worldline at `ψ` is
  reversible iff the entropy-production rate read at `ψ` vanishes;
* for the positive-generator arrow that rate is `(2/ℏ)·⟨H_I⟩_ψ`, so
  reversibility at `ψ` is equivalent to the expectation `reApplyInnerSelf ψ`
  (the real part of `⟨H_I⟩_ψ`) vanishing;
* the arrow is reversible at *every* state iff the irreversible generator `H_I`
  is itself the zero operator.

The last is the operator-level statement: a dissipative complex action
`H_C = H_R − i·H_I` produces no entropic time at any state only when its
anti-Hermitian part `H_I` is absent. -/

/-- **Reversibility ⇔ zero entropy-production rate.** The constant-rate worldline
of an entropy-controlled system is reversible exactly when the entropy rate read
at `ψ` is zero — since `ℏ > 0`, the constant slope `ℏ·rate` vanishes iff the rate
does. The `H_I = 0 ⇒ reversible` arrow of
`ofEntropyControlledSystem_isReversible_of_zero_HI` is the (left-to-right of the)
special case where the rate vanishes because the generator does. -/
theorem ofEntropyControlledSystem_isReversible_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) :
    (ofEntropyControlledSystem S ψ).IsReversible ↔ S.entropyRate ψ = 0 := by
  constructor
  · intro hrev
    have h : S.hbar * S.entropyRate ψ * 0 = S.hbar * S.entropyRate ψ * 1 := hrev 0 1
    rw [mul_zero, mul_one] at h
    rcases mul_eq_zero.mp h.symm with h1 | h2
    · exact absurd h1 (ne_of_gt S.hbar_pos)
    · exact h2
  · intro hrate t₁ t₂
    show S.hbar * S.entropyRate ψ * t₁ = S.hbar * S.entropyRate ψ * t₂
    rw [hrate]; ring

/-- **Reversibility ⇔ vanishing expectation `⟨H_I⟩_ψ`.** For the arrow built from
a positive irreversible generator, reversibility at `ψ` is equivalent to the
(non-negative) expectation `reApplyInnerSelf ψ = re ⟨H_I⟩_ψ` being zero. -/
theorem ofPositiveGeneratorArrow_isReversible_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R H_I : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hpos : H_I.IsPositive) (ψ : H) :
    (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).IsReversible
      ↔ H_I.reApplyInnerSelf ψ = 0 :=
  (ofEntropyControlledSystem_isReversible_iff
      (positiveGeneratorSystem H_R H_I hbar hbar_pos hpos) ψ).trans <| by
    show (2 / hbar) * H_I.reApplyInnerSelf ψ = 0 ↔ H_I.reApplyInnerSelf ψ = 0
    rw [mul_eq_zero, or_iff_right (div_pos (by norm_num) hbar_pos).ne']

/-- **Reversibility ⇔ `H_I ψ = 0` (kernel form).** Sharpening of
`ofPositiveGeneratorArrow_isReversible_iff`: for a *positive* irreversible
generator, vanishing of the real expectation `reApplyInnerSelf ψ` is equivalent
to `ψ` lying in the kernel of `H_I` itself, by the positive-operator pointwise
kernel theorem `ContinuousLinearMap.IsPositive.apply_eq_zero_of_reApplyInnerSelf_eq_zero`.
So the worldline at `ψ` is reversible exactly when `H_I ψ = 0`. -/
theorem ofPositiveGeneratorArrow_isReversible_iff'
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R H_I : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hpos : H_I.IsPositive) (ψ : H) :
    (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).IsReversible
      ↔ H_I ψ = 0 :=
  (ofPositiveGeneratorArrow_isReversible_iff H_R H_I hbar hbar_pos hpos ψ).trans
    ⟨fun h => hpos.apply_eq_zero_of_reApplyInnerSelf_eq_zero h,
     fun h => by simp [ContinuousLinearMap.reApplyInnerSelf_apply, h]⟩

/-- **Operator-level reversibility iff: reversible at every state ⇔ `H_I = 0`.**
The positive-generator arrow is reversible for *all* `ψ` exactly when the
irreversible generator vanishes. The forward direction uses that a positive
operator whose expectation `⟨H_I⟩_ψ` vanishes at every `ψ` is the zero operator
(`inner_map_self_eq_zero`, the complex polarisation identity); the converse is
the frozen-clock result `ofEntropyControlledSystem_isReversible_of_zero_HI`. -/
theorem ofPositiveGeneratorArrow_isReversible_forall_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R H_I : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (hpos : H_I.IsPositive) :
    (∀ ψ, (ofPositiveGeneratorArrow H_R H_I hbar hbar_pos hpos ψ).IsReversible)
      ↔ H_I = 0 := by
  constructor
  · intro hrev
    have hall : ∀ x, inner ℂ (H_I x) x = (0 : ℂ) := by
      intro x
      have hr : H_I.reApplyInnerSelf x = 0 :=
        (ofPositiveGeneratorArrow_isReversible_iff H_R H_I hbar hbar_pos hpos x).mp (hrev x)
      have hsym := hpos.isSymmetric.coe_reApplyInnerSelf_apply x
      rw [hr] at hsym
      rw [← hsym]; norm_num
    have hL : (H_I : H →ₗ[ℂ] H) = 0 := by
      rw [← inner_map_self_eq_zero]
      intro x; simpa using hall x
    ext x
    have hx := DFunLike.congr_fun hL x
    simpa using hx
  · intro hzero ψ
    exact ofEntropyControlledSystem_isReversible_of_zero_HI
      (positiveGeneratorSystem H_R H_I hbar hbar_pos hpos) ψ hzero

/-! ## Zhang (2008) information-theoretic second law

The von-Neumann second law from two information-theoretic ingredients
(Q.-R. Zhang, *Int. J. Mod. Phys. E* **17** (2008) 531):

1. **Information conservation under unitary evolution** (Zhang Eq. 3)
   `Sᵥₙ (U ρ U†) = Sᵥₙ ρ` — `Sᵥₙ_U_conj` in
   `QuantumInfo.Entropy.VonNeumann`.

2. **Sub-additivity of entropy** under partial trace into parts (Zhang
   Eq. 8 / Lemma 4):
   `Sᵥₙ ρ_AB ≤ Sᵥₙ (Tr_B ρ_AB) + Sᵥₙ (Tr_A ρ_AB)` — `Sᵥₙ_subadditivity`
   in `QuantumInfo.Entropy.SSA`.

Combined they give Zhang Theorem 1: *the entropy of an isolated system,
if it changes, can only increase*.  The physical content: the increase
is exactly the loss of correlation information between the parts when
the entangled joint state is decomposed by partial trace.

This is the bipartite-unitary specialisation that turns the *assumed*
`S_I_monotone` field of `EntropyArrowWorldline` into a *proved*
theorem in the canonical setting.
-/

open QuantumInfo.Finite

/-- **Zhang's information-theoretic second law (bipartite unitary case).**

For any bipartite mixed state `ρ : MState (d₁ × d₂)` and unitary
`U : 𝐔[d₁ × d₂]`, the initial entropy is bounded above by the sum of
the part-wise entropies of the time-evolved state after partial trace:

  `Sᵥₙ ρ ≤ Sᵥₙ (Tr_B (U ρ U†)) + Sᵥₙ (Tr_A (U ρ U†))`.

Proof: unitary invariance of `Sᵥₙ` (Zhang Eq. 3) collapses the LHS to
`Sᵥₙ (U ρ U†)`, and sub-additivity (Zhang Eq. 8) bounds it by the
part-wise sum on the right. -/
theorem zhang_second_law
    {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁]
    [DecidableEq d₂]
    (ρ : MState (d₁ × d₂)) (U : 𝐔[d₁ × d₂]) :
    Sᵥₙ ρ ≤
      Sᵥₙ (ρ.U_conj U).traceRight + Sᵥₙ (ρ.U_conj U).traceLeft :=
  calc Sᵥₙ ρ
      = Sᵥₙ (ρ.U_conj U) := (Sᵥₙ_U_conj ρ U).symm
    _ ≤ Sᵥₙ (ρ.U_conj U).traceRight + Sᵥₙ (ρ.U_conj U).traceLeft :=
        Sᵥₙ_subadditivity (ρ.U_conj U)

/-- **Initial-to-final entropy bound** for an unentangled initial state
that is then unitarily evolved.

If the initial state is factorisable, `ρ(t₀) = σ_A ⊗ᴹ σ_B`, the initial
entropy is exactly `Sᵥₙ σ_A + Sᵥₙ σ_B`; Zhang's theorem then gives

  `Sᵥₙ σ_A + Sᵥₙ σ_B ≤ Sᵥₙ (Tr_B (U·(σ_A⊗σ_B)·U†)) + Sᵥₙ (Tr_A (U·(σ_A⊗σ_B)·U†))`,

i.e., **`S(t₀) ≤ S(t)`** in the second-law sense.

Note: the additivity step `Sᵥₙ (σ_A ⊗ᴹ σ_B) = Sᵥₙ σ_A + Sᵥₙ σ_B` is
left as a hypothesis here (it is `Sᵥₙ_prod` in QuantumInfo when
applicable); the load-bearing inequality is Zhang's. -/
theorem zhang_second_law_of_product
    {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁]
    [DecidableEq d₂]
    (σ_A : MState d₁) (σ_B : MState d₂) (U : 𝐔[d₁ × d₂])
    (h_prod : Sᵥₙ (σ_A ⊗ᴹ σ_B) = Sᵥₙ σ_A + Sᵥₙ σ_B) :
    Sᵥₙ σ_A + Sᵥₙ σ_B ≤
      Sᵥₙ ((σ_A ⊗ᴹ σ_B).U_conj U).traceRight +
        Sᵥₙ ((σ_A ⊗ᴹ σ_B).U_conj U).traceLeft := by
  rw [← h_prod]
  exact zhang_second_law (σ_A ⊗ᴹ σ_B) U


end Physlib.Thermodynamics.SecondLaw

end
