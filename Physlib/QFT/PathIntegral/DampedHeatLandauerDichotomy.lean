/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.EuclideanPropagator
public import Physlib.QFT.PathIntegral.DampedHeatSemigroup
public import Physlib.Thermodynamics.ComputationLandauer
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
meta import Zil

/-!
# The damped-heat reversibility dichotomy and its Landauer count

The entropically damped heat propagator `p(t) = exp(-(m² + λ)t)` (`EuclideanPropagator`) and the
thermodynamics of computation (`Thermodynamics.ComputationLandauer`) formalize the *same*
reversible/irreversible dichotomy in two categories. There, a computation step is reversible exactly when its
`eval` is injective (KL divergence preserved — Bennett) and irreversible when it erases (a coarse-graining with
`τ_ent ≥ 0` and Landauer cost per bit). Here the same split appears at the semigroup level:

* **§A — the dichotomy for one mode.** `dampedHeat_isometry_iff`: the damped-heat evolution preserves every
  amplitude, `|p(t)·x| = |x|`, **iff** the total rate vanishes, `m² + λ = 0` — the reversible/Bennett face.
  `dampedHeat_strict_contraction`: for a positive rate every positive-time orbit strictly contracts — the
  erasure face. `dampedHeat_bit_erasure_time`: the evolution halves the register in time `ln 2/(m² + λ)` —
  **one bit erased per `ln 2/a`**, the same `ln 2` that prices a bit in `landauerCount`/`landauerCost`.
* **§B — the Landauer count of a damped cascade.** Flagging each stage of a cascade of damped modes by its
  rate (`dampedStepFlag`: rate `0` ↦ `reversibleStep`, positive rate ↦ `irreversibleStep`) and reusing
  `ComputationLandauer.landauerCount`, the cascade propagator `∏ᵢ exp(-aᵢt) = exp(-(∑ᵢ aᵢ)t)`
  (`dampedCascade_prod_eq_exp_sum`) is the identity **iff** the Landauer count vanishes
  (`dampedCascade_isometric_iff_landauerCount_zero`): *a damped-heat cascade dissipates nothing exactly when
  its Landauer count is zero.*
* **§C — the two-sided (Tomita–Takesaki) face.** Modular dynamics is a one-parameter group of isometries on
  all of `ℝ` (Inoue, LNM 1699 §4.4–4.5; Bisognano–Wichmann's boost group; physlib's
  `modularGroupOfState_group_law`, `kmsQIF`, `KayWaldHawkingKMSHorizon`). The damped mode has the group law
  for free (`dampedHeat_group_hom`) but its backward flow expands (`dampedHeat_backward_expands`);
  `dampedHeat_two_sided_isometry_iff`: it is a two-sided isometric flow **iff** `m² + λ = 0` — a strictly
  damped mode can never be modular.
* **§E — the ZIL file contract.** `physlib.dampedHeatLandauerDichotomy` (level `bridge_theorem`, status
  `satisfied`), with theorem intents pinning what each witness statement must mention, and forbidden
  substitutes recording the honest ceiling.

**Scope (ZIL caveats).** These are modewise scalar statements — no full function-space heat/Navier–Stokes
semigroup is claimed. The Landauer flag is assigned *by rate*, mirroring `ComputationLandauer`'s per-step
declaration (there justified by the undecidability of halting); it is not derived from a Gödel code. And all
entropy accounting here lives in the finite/trace-available setting: the continuum Landauer bound
`ΔQ ≥ β⁻¹ΔS_rel` would require Araki relative entropy, KMS/modular references, and the split property (type
III local algebras have no trace), none of which is asserted.

## References

* R. Landauer, IBM J. Res. Dev. 5 (1961) 183; C. H. Bennett, IBM J. Res. Dev. 17 (1973) 525. Carriers:
  `QFT.PathIntegral.EuclideanPropagator` (`damped_heat_propagator`),
  `Thermodynamics.ComputationLandauer` (`Reversibility`, `landauerCount`).
-/

set_option autoImplicit false

open Physlib.Thermodynamics.ComputationLandauer Physlib.Thermodynamics.Landauer

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

/-! ## A. The reversibility dichotomy for one damped mode -/

/-- **[Exact exponential amplitude decay]** `|p(t)·x| = exp(-(m² + λ)t)·|x|` — the norm of every scalar
orbit of the damped-heat propagator. -/
lemma dampedHeat_abs_apply (t m_sq lam x : ℝ) :
    |damped_heat_propagator t m_sq lam * x| = Real.exp (-(m_sq + lam) * t) * |x| := by
  unfold damped_heat_propagator
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **[The continuous-time arrow]** for a non-negative total rate, the damped-heat amplitude is
`Antitone` in time: `t₁ ≤ t₂ ⟹ |p(t₂)·x| ≤ |p(t₁)·x|` — amplitude (information) never returns.
The continuous face of the discrete second law (`processDissipation_take_monotone`, the H-theorem
summed over a process): there, cumulative dissipation never rewinds; here, the semigroup orbit
never regrows. -/
theorem dampedHeat_abs_antitone (m_sq lam x : ℝ) (hrate : 0 ≤ m_sq + lam) :
    Antitone (fun t => |damped_heat_propagator t m_sq lam * x|) := by
  intro t₁ t₂ h12
  simp only [dampedHeat_abs_apply]
  have hexp : Real.exp (-(m_sq + lam) * t₂) ≤ Real.exp (-(m_sq + lam) * t₁) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right hexp (abs_nonneg x)

/-- **[Reversible ⟺ zero rate] the damped-heat evolution is an isometry iff `m² + λ = 0`.** The semigroup
face of the Bennett/Landauer dichotomy of `ComputationLandauer`: amplitude is preserved for all times and all
registers exactly when nothing is damped — the analogue of an injective (information-preserving) computation
step, which preserves KL divergence and produces no entropy. -/
@[zil_claim physlib.dampedHeat.isometryIffZeroRate,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.nonnegativeRates,
  zil_export]
theorem dampedHeat_isometry_iff (m_sq lam : ℝ) (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    (∀ t, 0 ≤ t → ∀ x : ℝ, |damped_heat_propagator t m_sq lam * x| = |x|)
      ↔ m_sq + lam = 0 := by
  constructor
  · intro h
    have h1 := h 1 zero_le_one 1
    rw [dampedHeat_abs_apply, abs_one] at h1
    have h2 : Real.exp (-(m_sq + lam) * 1) = 1 := by linarith
    have h3 : Real.exp (-(m_sq + lam) * 1) = Real.exp 0 := by rw [Real.exp_zero]; exact h2
    have h4 := Real.exp_eq_exp.mp h3
    linarith
  · intro ha t ht x
    rw [dampedHeat_abs_apply, ha]
    simp

/-- **[Irreversible ⟺ strict contraction] a positive rate strictly contracts every nonzero register at every
positive time.** The erasure face of the dichotomy: with `m² + λ > 0` information about the initial amplitude
is being lost at every instant — the semigroup analogue of a non-injective (erasing) computation step. -/
@[zil_claim physlib.dampedHeat.strictContraction,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.positiveDecayRate,
  zil_export]
theorem dampedHeat_strict_contraction (m_sq lam t x : ℝ)
    (ha : 0 < m_sq + lam) (ht : 0 < t) (hx : x ≠ 0) :
    |damped_heat_propagator t m_sq lam * x| < |x| := by
  rw [dampedHeat_abs_apply]
  have hexp : Real.exp (-(m_sq + lam) * t) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    nlinarith
  have hxpos : 0 < |x| := abs_pos.mpr hx
  nlinarith [Real.exp_pos (-(m_sq + lam) * t)]

/-- **[One bit per `ln 2/a`] the damped-heat evolution halves the register at time `ln 2/(m² + λ)`.** The
decay rate is a Landauer erasure rate: each interval of length `ln 2/(m² + λ)` erases one bit of amplitude —
the same `ln 2` that prices one erased bit in `landauerCost` (and one factor-2 dilation in the scale metric). -/
@[zil_claim physlib.dampedHeat.bitErasureTime,
  zil_concept physics.landauerErasure, zil_requires assumptions.positiveDecayRate,
  zil_export]
theorem dampedHeat_bit_erasure_time (m_sq lam x : ℝ) (ha : 0 < m_sq + lam) :
    damped_heat_propagator (Real.log 2 / (m_sq + lam)) m_sq lam * x = x / 2 := by
  unfold damped_heat_propagator
  rw [show -(m_sq + lam) * (Real.log 2 / (m_sq + lam)) = -Real.log 2 from by field_simp,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

/-! ## B. The Landauer count of a damped cascade -/

/-- **The Landauer flag of a damped stage**: rate `0` is a `reversibleStep`, a nonzero rate an
`irreversibleStep` (`ComputationLandauer.Reversibility`). Assigned *by rate* — mirroring
`ComputationLandauer`'s per-step declaration, not derived from a Gödel code. -/
def dampedStepFlag (rate : ℝ) : Reversibility :=
  if rate = 0 then reversibleStep else irreversibleStep

@[simp] lemma dampedStepFlag_zero : dampedStepFlag 0 = reversibleStep := if_pos rfl

lemma dampedStepFlag_ne_zero {rate : ℝ} (h : rate ≠ 0) :
    dampedStepFlag rate = irreversibleStep := if_neg h

/-- **[Zero Landauer count ⟺ all rates vanish].** The `landauerCount` of a rate-flagged damped cascade is
zero exactly when every stage has zero decay rate. -/
theorem dampedCascade_landauerCount_eq_zero_iff (rates : List ℝ) :
    landauerCount (rates.map dampedStepFlag) = 0 ↔ ∀ a ∈ rates, a = 0 := by
  unfold landauerCount
  rw [List.count_eq_zero]
  constructor
  · intro h a ha
    by_contra hne
    exact h (List.mem_map.mpr ⟨a, ha, dampedStepFlag_ne_zero hne⟩)
  · intro h hmem
    obtain ⟨a, ha, hflag⟩ := List.mem_map.mp hmem
    rw [h a ha, dampedStepFlag_zero] at hflag
    simp [reversibleStep, irreversibleStep] at hflag

/-- **[The cascade propagator is the exponential of the total rate]**
`∏ᵢ exp(-aᵢ t) = exp(-(∑ᵢ aᵢ)t)` — damped stages compose by adding their decay rates. -/
lemma dampedCascade_prod_eq_exp_sum (rates : List ℝ) (t : ℝ) :
    (rates.map (fun a => Real.exp (-a * t))).prod = Real.exp (-rates.sum * t) := by
  induction rates with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.sum_cons, ← Real.exp_add]
    congr 1
    ring

/-- A list of non-negative reals sums to zero iff every entry is zero. -/
lemma list_sum_eq_zero_iff {rates : List ℝ} (hnn : ∀ a ∈ rates, 0 ≤ a) :
    rates.sum = 0 ↔ ∀ a ∈ rates, a = 0 := by
  induction rates with
  | nil => simp
  | cons a l ih =>
    have hha : 0 ≤ a := hnn a List.mem_cons_self
    have hhl : ∀ b ∈ l, 0 ≤ b := fun b hb => hnn b (List.mem_cons_of_mem a hb)
    have hsl : 0 ≤ l.sum := List.sum_nonneg hhl
    rw [List.sum_cons]
    constructor
    · intro h
      have haz : a = 0 := by linarith
      have hlz : l.sum = 0 := by linarith
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hbl
      · exact haz
      · exact ((ih hhl).mp hlz) b hbl
    · intro h
      rw [h a List.mem_cons_self, zero_add]
      exact (ih hhl).mpr fun b hb => h b (List.mem_cons_of_mem a hb)

/-- **[A damped cascade dissipates nothing ⟺ its Landauer count is zero].** For non-negative stage rates and
any positive time, the cascade propagator `∏ᵢ exp(-aᵢt)` equals `1` (the evolution is the identity — nothing
erased) **iff** the `landauerCount` of the rate-flagged cascade vanishes. The two formalizations of
irreversibility — strict contraction of the damped semigroup and the erasure count of
`ComputationLandauer` — agree exactly. -/
@[zil_claim physlib.dampedHeat.cascadeLandauerCountDichotomy,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.nonnegativeRates,
  zil_export]
theorem dampedCascade_isometric_iff_landauerCount_zero (rates : List ℝ) (t : ℝ)
    (hnn : ∀ a ∈ rates, 0 ≤ a) (ht : 0 < t) :
    (rates.map (fun a => Real.exp (-a * t))).prod = 1
      ↔ landauerCount (rates.map dampedStepFlag) = 0 := by
  rw [dampedCascade_prod_eq_exp_sum, dampedCascade_landauerCount_eq_zero_iff,
    ← Real.exp_zero, Real.exp_eq_exp, ← list_sum_eq_zero_iff hnn]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact neg_eq_zero.mp h0
    · exact absurd h0 ht.ne'
  · intro h
    rw [h, neg_zero, zero_mul]

#zil_validate_embedded dampedHeat_isometry_iff where
  no_sorry, claim_linked, requirement_linked

#zil_validate_embedded dampedCascade_isometric_iff_landauerCount_zero where
  no_sorry, claim_linked, requirement_linked

/-! ## C. The two-sided isometry dichotomy — the Tomita–Takesaki face

Tomita–Takesaki modular dynamics is a one-parameter *group* of isometries defined for **all** real times:
`Ω^{it} 𝔐 Ω^{−it} = 𝔐, ∀ t ∈ ℝ` (A. Inoue, *Tomita–Takesaki theory in algebras of unbounded operators*,
LNM 1699, §4.4 — KMS quasi-weights for the BCS model), and in the Bisognano–Wichmann standard system of the
Wightman wedge the modular operator is the analytic continuation of the *unitary boost group* `{V(t)}_{t∈ℝ}`
(§4.5, Thm. 4.5.2). physlib's own finite-dimensional carrier `modularGroupOfState` likewise satisfies its
group law for all `s, t : ℝ` (`QuantumInertialFrameModularFromState.modularGroupOfState_group_law`), with the
KMS side in `QuantumInertialFrameKMS.kmsQIF` and `EntropicTime.KayWaldHawkingKMSHorizon`.

The damped mode satisfies the *group law* at all real times for free — what fails is the isometry of the
backward flow: running a strictly damped mode backwards **expands**. Hence only the rate-zero (reversible)
mode is eligible to be a modular flow; a strictly damped mode is semigroup-only. This is the arrow of time of
the dichotomy, in Tomita–Takesaki form. -/

/-- **[The group law is free] `p(s+t) = p(s)·p(t)` for all real times** — the damped propagator is a group
homomorphism on all of `ℝ`; the two-sided structure fails only at the level of isometry. -/
lemma dampedHeat_group_hom (m_sq lam s t : ℝ) :
    damped_heat_propagator (s + t) m_sq lam
      = damped_heat_propagator s m_sq lam * damped_heat_propagator t m_sq lam := by
  unfold damped_heat_propagator
  rw [← Real.exp_add]
  congr 1
  ring

/-- **[The backward flow of a damped mode expands] `1 < p(-t)` for positive rate and time.** Running a
strictly damped mode backwards is unbounded — the semigroup-only arrow of time. -/
lemma dampedHeat_backward_expands (m_sq lam t : ℝ) (ha : 0 < m_sq + lam) (ht : 0 < t) :
    1 < damped_heat_propagator (-t) m_sq lam := by
  unfold damped_heat_propagator
  rw [← Real.exp_zero, Real.exp_lt_exp]
  nlinarith

/-- **[Modular eligibility ⟺ zero rate] the damped mode is a two-sided isometric flow iff `m² + λ = 0`.**
Modular (Tomita–Takesaki/Bisognano–Wichmann) dynamics has unit modulus at *every* real time; the damped scalar
mode achieves this exactly when its rate vanishes — no sign hypotheses needed. A strictly damped mode can never
be a modular flow: irreversibility is precisely the loss of the two-sided isometric structure. -/
@[zil_claim physlib.dampedHeat.twoSidedIsometryIffZeroRate,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.modewiseScalarCarrier,
  zil_export]
theorem dampedHeat_two_sided_isometry_iff (m_sq lam : ℝ) :
    (∀ t : ℝ, |damped_heat_propagator t m_sq lam| = 1) ↔ m_sq + lam = 0 := by
  constructor
  · intro h
    have h1 := h 1
    unfold damped_heat_propagator at h1
    rw [abs_of_pos (Real.exp_pos _)] at h1
    have h3 : Real.exp (-(m_sq + lam) * 1) = Real.exp 0 := by rw [Real.exp_zero]; exact h1
    have h4 := Real.exp_eq_exp.mp h3
    linarith
  · intro ha t
    unfold damped_heat_propagator
    rw [ha]
    simp

/-! ## D. The dichotomy on the `C₀` contraction-semigroup carrier

`DampedHeatSemigroup` packages the scalar flow as a genuine `RealC0ContractionSemigroup` — operators
`dampedHeatOperator`, generator `dampedHeatGenerator = -(m² + λ)·id`, and the Hille–Yosida resolvent equal to
the Euclidean propagator. The dichotomy lifts verbatim to that carrier: the semigroup is isometric **iff** the
rate vanishes **iff** its infinitesimal generator is zero — reversibility read at the orbit level and at the
infinitesimal level agree. -/

/-- **[Operator-level orbit decay]** `‖T(t)x‖ = e^{−(m²+λ)t}·‖x‖` for the `C₀`-semigroup operators of
`DampedHeatSemigroup`. -/
lemma dampedHeatOperator_norm_apply (m_sq lam t x : ℝ) :
    ‖dampedHeatOperator m_sq lam t x‖ = Real.exp (-(m_sq + lam) * t) * ‖x‖ := by
  rw [dampedHeatOperator_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  exact dampedHeat_abs_apply t m_sq lam x

/-- **[The `C₀` semigroup is isometric ⟺ zero rate]** the carrier-level form of the dichotomy: the
`RealC0ContractionSemigroup` of `DampedHeatSemigroup` preserves every norm at every non-negative time exactly
when `m² + λ = 0` — discharged by the scalar dichotomy `dampedHeat_isometry_iff`. -/
@[zil_claim physlib.dampedHeat.semigroupIsometryIffZeroRate,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.nonnegativeRates,
  zil_export]
theorem dampedHeatSemigroup_isometry_iff (m_sq lam : ℝ) (hm : 0 ≤ m_sq) (hl : 0 ≤ lam) :
    (∀ t, 0 ≤ t → ∀ x : ℝ,
        ‖(dampedHeatC0ContractionSemigroup m_sq lam hm hl).operator t x‖ = ‖x‖)
      ↔ m_sq + lam = 0 := by
  have hop : ∀ t x, (dampedHeatC0ContractionSemigroup m_sq lam hm hl).operator t x
      = damped_heat_propagator t m_sq lam * x := fun t x => rfl
  constructor
  · intro h
    refine (dampedHeat_isometry_iff m_sq lam hm hl).mp fun t ht x => ?_
    have hx := h t ht x
    rwa [hop, Real.norm_eq_abs, Real.norm_eq_abs] at hx
  · intro ha t ht x
    rw [hop, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (dampedHeat_isometry_iff m_sq lam hm hl).mpr ha t ht x

/-- **[The generator vanishes ⟺ zero rate]** reversibility at the infinitesimal level: the bounded generator
`dampedHeatGenerator = -(m² + λ)·id` of the damped-heat `C₀` semigroup is the zero operator exactly when the
rate vanishes — the derivative form of the isometry dichotomy. -/
@[zil_claim physlib.dampedHeat.generatorZeroIffZeroRate,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.modewiseScalarCarrier,
  zil_export]
theorem dampedHeatGenerator_eq_zero_iff (m_sq lam : ℝ) :
    dampedHeatGenerator m_sq lam = 0 ↔ m_sq + lam = 0 := by
  constructor
  · intro h
    have h1 : dampedHeatGenerator m_sq lam 1 = 0 := by rw [h]; rfl
    rw [dampedHeatGenerator_apply, mul_one, neg_eq_zero] at h1
    exact h1
  · intro ha
    apply ContinuousLinearMap.ext
    intro x
    rw [dampedHeatGenerator_apply, ha]
    simp

zil_theorem_intent dampedHeatSemigroup_isometry_iff where
  at_level bridge_theorem
  must_mention [dampedHeatC0ContractionSemigroup, damped_heat_propagator]

zil_theorem_intent dampedHeatGenerator_eq_zero_iff where
  at_level bridge_theorem
  must_mention [dampedHeatGenerator]

zil attach dampedHeatSemigroup_isometry_iff where
  formalizes @ "claim:damped-semigroup-isometry-iff-zero-rate",
  requires @ "claim:damped-heat-isometry-iff-zero-rate",
  supported_by @ "definition:damped-heat-c0-contraction-semigroup",
  caveat @ "claim:modewise-scalar-not-full-pde-semigroup"

zil attach dampedHeatGenerator_eq_zero_iff where
  formalizes @ "claim:damped-generator-zero-iff-zero-rate",
  supported_by @ "definition:damped-heat-generator",
  caveat @ "claim:modewise-scalar-not-full-pde-semigroup"

/-! ## E. Native ZIL claim graph -/

zil attach dampedHeat_isometry_iff where
  formalizes @ "claim:damped-heat-isometry-iff-zero-rate",
  supported_by @ "definition:damped-heat-propagator",
  supported_by @ "paper:bennett-1973",
  caveat @ "claim:modewise-scalar-not-full-pde-semigroup"

zil attach dampedHeat_strict_contraction where
  supported_by @ "lean:Physlib.QFT.PathIntegral.dampedHeat_abs_apply",
  supported_by @ "lean:HermitianMat.exp_pos",
  formalizes @ "claim:damped-heat-strict-contraction",
  requires @ "assumption:positive-decay-rate",
  caveat @ "claim:modewise-scalar-not-full-pde-semigroup"

zil attach dampedHeat_bit_erasure_time where
  formalizes @ "claim:damped-heat-bit-erasure-time",
  requires @ "assumption:positive-decay-rate",
  supported_by @ "paper:landauer-1961",
  caveat @ "claim:amplitude-halving-not-thermodynamic-heat-bound"

zil attach dampedCascade_isometric_iff_landauerCount_zero where
  formalizes @ "claim:damped-cascade-landauer-count-dichotomy",
  requires @ "assumption:nonnegative-rates",
  supported_by @ "definition:landauer-count",
  supported_by @ "paper:bennett-1973",
  caveat @ "claim:rate-flag-not-derived-from-code",
  caveat @ "claim:finite-trace-setting-not-araki-continuum"

zil_rule dampedHeatClaimRequirement:
  ?claim # requires_claim @ ?requirement IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # requires @ ?requirement

zil_rule dampedHeatClaimEvidence:
  ?claim # supported_by @ ?source IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # supported_by @ ?source

zil_rule dampedHeatClaimCaveat:
  ?claim # has_caveat @ ?caveat IF
  ?declaration # formalizes @ ?claim AND
  ?declaration # caveat @ ?caveat

zil attach dampedHeat_two_sided_isometry_iff where
  formalizes @ "claim:damped-heat-two-sided-isometry-iff-zero-rate",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "paper:bisognano-wichmann-1975",
  caveat @ "claim:scalar-shadow-not-operator-modular-theory"

zil attach dampedHeat_backward_expands where
  formalizes @ "claim:damped-backward-flow-expands",
  requires @ "assumption:positive-decay-rate",
  caveat @ "claim:scalar-shadow-not-operator-modular-theory"

/-! ## E. The file contract and formalization lint -/

zil_theorem_intent dampedHeat_isometry_iff where
  at_level bridge_theorem
  must_mention [damped_heat_propagator]

zil_theorem_intent dampedHeat_strict_contraction where
  at_level bridge_theorem
  must_mention [damped_heat_propagator]

zil_theorem_intent dampedHeat_bit_erasure_time where
  at_level bridge_theorem
  must_mention [damped_heat_propagator, Real.log]

zil_theorem_intent dampedCascade_isometric_iff_landauerCount_zero where
  at_level bridge_theorem
  must_mention [Physlib.Thermodynamics.Landauer.landauerCount, dampedStepFlag, Real.exp]

zil_theorem_intent dampedHeat_two_sided_isometry_iff where
  at_level bridge_theorem
  must_mention [damped_heat_propagator]

zil_file_contract physlib.dampedHeatLandauerDichotomy where
  promises "The entropically damped heat propagator realizes the reversible/irreversible dichotomy of the thermodynamics of computation: it is an isometry (for non-negative or all real times) exactly at zero rate, strictly contracts at positive rate, erases one bit of amplitude per ln 2 over the rate, and a damped cascade is the identity exactly when its Landauer count vanishes."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QFT.PathIntegral.damped_heat_propagator",
    "lean:Physlib.Thermodynamics.Landauer.landauerCount",
    "lean:Physlib.Thermodynamics.Landauer.irreversibleStep",
    "lean:Physlib.QFT.PathIntegral.dampedStepFlag"]
  forbids_substitutes ["a full function-space heat or Navier-Stokes PDE semigroup claim",
    "a continuum Landauer bound stated without Araki relative entropy and KMS references",
    "a reversibility flag derived from a Godel code rather than declared by rate",
    "a dynamical identification of damping with a Tomita-Takesaki modular flow"]
  witnessed_by [dampedHeat_isometry_iff, dampedHeat_strict_contraction,
    dampedHeat_bit_erasure_time, dampedCascade_isometric_iff_landauerCount_zero,
    dampedHeat_two_sided_isometry_iff]

#zil_formalization_lint physlib.dampedHeatLandauerDichotomy

end Physlib.QFT.PathIntegral

end
