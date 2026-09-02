/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.LeviCivita
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
meta import Zil

/-!
# Covariant Compton phase along a curved worldline

This module upgrades the flat straight-worldline Compton clock to a genuine
pseudo-Riemannian manifold. Let `γ` be an integral curve, `U` its four-velocity,
and `P` its four-momentum. The dimensionless covariant phase is

`Phi[a,b] = integral_a^b g(P,U) / hbar d tau`.

The proof has three non-algebraic links:

1. Levi--Civita metric compatibility and parallel transport make the local
   directional derivative of `g(P,U)` vanish;
2. the manifold chain rule turns that local statement into a zero ordinary
   Frechet derivative along `γ`;
3. the mean-value theorem promotes the zero derivative to global constancy,
   after which the interval integral evaluates exactly.

For a proper-time geodesic, `P = m U` and `g(U,U) = c^2` at one reference
point give `Phi[a,b] = m c^2 (b-a) / hbar`, exactly the existing Compton phase.
Consequently a proper-time interval `hbar/(m c^2)` advances the covariant phase
by one radian even on a curved spacetime.

The regularity hypothesis on the scalar pairing is explicit because the current
`PseudoRiemannianMetric` API exposes metric smoothness in charts rather than a
ready-made smooth-contraction lemma. The result concerns a freely falling
Levi--Civita geodesic; accelerated motion with forces needs the corresponding
forced transport equation. It neither quantizes the metric nor constructs a
graviton.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle Set FiberBundle
open scoped Manifold ContDiff Interval
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.CurvedWorldlinePhase

universe v w

variable {n : WithTop ℕ∞}
variable {E : Type v} {H M : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H E]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I 2 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-! ## A. Covariant phase functional -/

/-- The dimensionless covariant phase accumulated between worldline parameters
`a` and `b`: the interval integral of the momentum--velocity pairing divided
by `ℏ`. For a proper-time parametrized massive geodesic this is `S/ℏ`. -/
noncomputable def curvedWorldlinePhase
    (g : PseudoRiemannianMetric E H M n I)
    (P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (ℏ a b : ℝ) : ℝ :=
  ∫ t in a..b, g.val (γ t) (P (γ t)) (U (γ t)) / ℏ

/-! ## B. Levi--Civita conservation along the worldline -/

set_option backward.isDefEq.respectTransparency false in
/-- Levi--Civita parallel transport makes the ordinary Frechet derivative of
the momentum--velocity pairing vanish along an integral curve. This is the
manifold-chain-rule bridge from local metric compatibility to a one-dimensional
worldline conservation law. -/
@[zil_level physical_theorem]
lemma leviCivita_worldlinePairing_fderiv_eq_zero
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (X P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hX : MDiff (T% X)) (hP : MDiff (T% P)) (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦ g.val x (P x) (U x)))
    (hγ : IsMIntegralCurve γ X)
    (hparallelP : ∀ x, cov P x (X x) = 0)
    (hparallelU : ∀ x, cov U x (X x) = 0) (t : ℝ) :
    fderiv ℝ (fun s ↦ g.val (γ s) (P (γ s)) (U (γ s))) t = 0 := by
  let pairing : M → ℝ := fun x ↦ g.val x (P x) (U x)
  have hγt : MDiffAt γ t := (hγ t).mdifferentiableAt
  have hcomp := mfderiv_comp_apply t (hpair (γ t)) hγt
    ((1 : ℝ) : TangentSpace (modelWithCornersSelf ℝ ℝ) t)
  have hvelocity :
      mfderiv (modelWithCornersSelf ℝ ℝ) I γ t
        ((1 : ℝ) : TangentSpace (modelWithCornersSelf ℝ ℝ) t) = X (γ t) := by
    rw [(hγ t).mfderiv]
    change (1 : ℝ) • X (γ t) = X (γ t)
    exact one_smul ℝ (X (γ t))
  have hlocal :=
    PseudoRiemannianMetric.leviCivita_pairing_mfderiv_eq_zero_of_parallel
      I g cov hcov X P U (γ t) (hX (γ t)) (hP (γ t)) (hU (γ t))
        (hparallelP (γ t)) (hparallelU (γ t))
  rw [← mfderiv_eq_fderiv]
  apply ContinuousLinearMap.ext_ring
  change mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      (pairing ∘ γ) t
        ((1 : ℝ) : TangentSpace (modelWithCornersSelf ℝ ℝ) t) = 0
  rw [hcomp, hvelocity]
  exact hlocal

set_option backward.isDefEq.respectTransparency false in
/-- The momentum--velocity pairing is globally constant along a connected
worldline when both fields are Levi--Civita parallel in its tangent direction. -/
@[zil_level physical_theorem]
lemma leviCivita_worldlinePairing_eq
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (X P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hX : MDiff (T% X)) (hP : MDiff (T% P)) (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦ g.val x (P x) (U x)))
    (hγ : IsMIntegralCurve γ X)
    (hparallelP : ∀ x, cov P x (X x) = 0)
    (hparallelU : ∀ x, cov U x (X x) = 0) (s t : ℝ) :
    g.val (γ s) (P (γ s)) (U (γ s)) =
      g.val (γ t) (P (γ t)) (U (γ t)) := by
  let pairing : M → ℝ := fun x ↦ g.val x (P x) (U x)
  have hdiff : Differentiable ℝ (pairing ∘ γ) := fun r ↦
    ((hpair (γ r)).comp r (hγ r).mdifferentiableAt).differentiableAt
  exact is_const_of_fderiv_eq_zero hdiff
    (fun r ↦ leviCivita_worldlinePairing_fderiv_eq_zero I g cov hcov X P U γ
      hX hP hU hpair hγ hparallelP hparallelU r) s t

set_option backward.isDefEq.respectTransparency false in
/-- Integrating the Levi--Civita-conserved momentum--velocity pairing gives
its value at the initial endpoint times the oriented parameter duration. -/
@[zil_level physical_theorem]
lemma curvedWorldlinePhase_eq_pairing_mul_duration
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (X P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hX : MDiff (T% X)) (hP : MDiff (T% P)) (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦ g.val x (P x) (U x)))
    (hγ : IsMIntegralCurve γ X)
    (hparallelP : ∀ x, cov P x (X x) = 0)
    (hparallelU : ∀ x, cov U x (X x) = 0) (ℏ a b : ℝ) :
    curvedWorldlinePhase I g P U γ ℏ a b =
      (g.val (γ a) (P (γ a)) (U (γ a)) / ℏ) * (b - a) := by
  unfold curvedWorldlinePhase
  have hconst : ∀ t : ℝ,
      g.val (γ t) (P (γ t)) (U (γ t)) =
        g.val (γ a) (P (γ a)) (U (γ a)) := fun t ↦
    leviCivita_worldlinePairing_eq I g cov hcov X P U γ hX hP hU hpair hγ
      hparallelP hparallelU t a
  simp_rw [hconst]
  rw [intervalIntegral.integral_const]
  ring

/-! ## C. Proper-time Compton phase -/

set_option backward.isDefEq.respectTransparency false in
/-- **Curved-worldline Compton phase theorem.** On a proper-time geodesic,
Levi--Civita transport, one-point momentum calibration `P = m U`, and timelike
normalization `g(U,U) = c^2` force the complete covariant phase integral to be
the standard Compton phase `m c^2 (b-a) / ℏ`. -/
@[zil_level bridge_theorem]
theorem curvedWorldlinePhase_eq_comptonPhase
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hP : MDiff (T% P)) (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦ g.val x (P x) (U x)))
    (hγ : IsMIntegralCurve γ U)
    (hparallelP : ∀ x, cov P x (U x) = 0)
    (hgeodesic : ∀ x, cov U x (U x) = 0)
    (m c ℏ a b : ℝ) (hmomentum : P (γ a) = m • U (γ a))
    (hproper : g.val (γ a) (U (γ a)) (U (γ a)) = c ^ 2) :
    curvedWorldlinePhase I g P U γ ℏ a b = comptonPhase m c ℏ (b - a) := by
  rw [curvedWorldlinePhase_eq_pairing_mul_duration I g cov hcov U P U γ
    hU hP hU hpair hγ hparallelP hgeodesic]
  have hrest : g.val (γ a) (P (γ a)) (U (γ a)) = m * c ^ 2 := by
    simp [hmomentum, hproper]
  rw [hrest]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A reduced Compton proper-time interval `ℏ/(m c^2)` advances the covariant
phase by exactly one radian on any geodesic satisfying the theorem's transport
and normalization conditions. -/
@[zil_level bridge_theorem]
lemma curvedWorldlinePhase_comptonTick_eq_one
    (g : PseudoRiemannianMetric E H M n I)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : PseudoRiemannianMetric.IsLeviCivitaConnection I g cov)
    (P U : ∀ x : M, TangentSpace I x) (γ : ℝ → M)
    (hP : MDiff (T% P)) (hU : MDiff (T% U))
    (hpair : MDiff (fun x ↦ g.val x (P x) (U x)))
    (hγ : IsMIntegralCurve γ U)
    (hparallelP : ∀ x, cov P x (U x) = 0)
    (hgeodesic : ∀ x, cov U x (U x) = 0)
    (m c ℏ a : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0)
    (hmomentum : P (γ a) = m • U (γ a))
    (hproper : g.val (γ a) (U (γ a)) (U (γ a)) = c ^ 2) :
    curvedWorldlinePhase I g P U γ ℏ a (a + ℏ / (m * c ^ 2)) = 1 := by
  rw [curvedWorldlinePhase_eq_comptonPhase I g cov hcov P U γ hP hU hpair hγ
    hparallelP hgeodesic m c ℏ a (a + ℏ / (m * c ^ 2)) hmomentum hproper]
  unfold comptonPhase comptonFrequency
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.CurvedWorldlinePhase

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.CurvedWorldlinePhase

zil attach leviCivita_worldlinePairing_fderiv_eq_zero where
  formalizes @ "claim:levi-civita-metric-compatibility-and-parallel-transport-\
make-the-frechet-derivative-of-the-momentum-velocity-pairing-vanish-along-a-\
curved-integral-worldline",
  epistemic_status @ "analytic-theorem",
  supported_by @ "lean:PseudoRiemannianMetric.\
leviCivita_pairing_mfderiv_eq_zero_of_parallel",
  supported_by @ "lean:mfderiv_comp_apply"

zil attach leviCivita_worldlinePairing_eq where
  formalizes @ "claim:the-momentum-velocity-pairing-is-globally-constant-along-\
a-connected-worldline-when-both-fields-are-levi-civita-parallel",
  epistemic_status @ "analytic-theorem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
CurvedWorldlinePhase.leviCivita_worldlinePairing_fderiv_eq_zero",
  supported_by @ "lean:is_const_of_fderiv_eq_zero"

zil attach curvedWorldlinePhase_eq_pairing_mul_duration where
  formalizes @ "claim:the-curved-worldline-covariant-phase-integral-of-a-\
levi-civita-conserved-momentum-velocity-pairing-is-the-initial-pairing-over-\
hbar-times-the-oriented-worldline-parameter-duration",
  epistemic_status @ "analytic-theorem",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
CurvedWorldlinePhase.leviCivita_worldlinePairing_eq"

zil attach curvedWorldlinePhase_eq_comptonPhase where
  formalizes @ "claim:on-a-proper-time-geodesic-with-parallel-momentum-p-equals-\
m-u-and-g-u-u-equals-c-squared-at-one-reference-point-the-full-curved-\
worldline-covariant-phase-is-the-compton-phase-m-c-squared-delta-tau-over-hbar",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
CurvedWorldlinePhase.curvedWorldlinePhase_eq_pairing_mul_duration",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonClockMalamentProperTime.comptonPhase"

zil attach curvedWorldlinePhase_comptonTick_eq_one where
  formalizes @ "claim:a-reduced-compton-proper-time-interval-advances-the-\
levi-civita-covariant-phase-by-exactly-one-radian-on-a-curved-geodesic",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
CurvedWorldlinePhase.curvedWorldlinePhase_eq_comptonPhase"

zil_file_contract physlib.curvedWorldlinePhase where
  promises "The curved-worldline completion of the Compton phase. On a genuine \
pseudo-Riemannian manifold, the manifold chain rule converts the local \
Levi-Civita metric-compatibility identity for two parallel fields into a zero \
ordinary Frechet derivative of their pairing along an integral curve. The \
mean-value theorem promotes this to global conservation, and an actual oriented \
interval integral evaluates the covariant phase. For a proper-time geodesic \
whose momentum equals mass times four-velocity and whose four-velocity has \
metric norm c squared at one reference point, the full phase is exactly the \
Compton phase m c squared Delta tau over hbar, and one reduced Compton interval \
advances it by one radian."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:PseudoRiemannianMetric.IsLeviCivitaConnection",
    "lean:IsMIntegralCurve",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.\
ComptonClockMalamentProperTime.comptonPhase"
  ]
  forbids_substitutes [
    "treating the straight Minkowski worldline calculation as a curved-manifold proof",
    "dropping the geodesic or parallel-transport hypotheses for an accelerated forced trajectory",
    "reading the covariant particle phase as a quantization of the gravitational \
field or a graviton construction",
    "hiding the scalar-pairing regularity needed by the manifold chain rule"
  ]
  witnessed_by [
    leviCivita_worldlinePairing_fderiv_eq_zero,
    leviCivita_worldlinePairing_eq,
    curvedWorldlinePhase_eq_pairing_mul_duration,
    curvedWorldlinePhase_eq_comptonPhase,
    curvedWorldlinePhase_comptonTick_eq_one
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.curvedWorldlinePhase
