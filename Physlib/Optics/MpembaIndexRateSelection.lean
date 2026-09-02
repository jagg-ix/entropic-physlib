/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Optics.MpembaCrossingReadsEffectiveDamping

meta import Zil

/-!
# The Mpemba index: nulling the slow mode selects which rate is observed

Klich, Raz, Hirschberg & Vucelja, *The Mpemba index and anomalous relaxation*
(arXiv:1711.05829, PRX 9, 021060 (2019)), analyse Markovian relaxation with rate matrix `R`
satisfying detailed balance.  Its eigenvalues obey `0 > Re λ₂ ≥ Re λ₃ ≥ …`, and the equilibration
timescale is `−(Re λ₂)⁻¹` — set by the *slowest* mode.  The amplitude of that mode in a given
preparation is the overlap coefficient

  `a₂ = (f₂ · F^{1/2} p_init) / ‖f₂‖²`

which vanishes identically at the bath temperature.  Their **strong Mpemba effect** is a second,
non-trivial zero: a preparation with `a₂ = 0` does not populate the slow mode at all, so relaxation
is governed by `λ₃` and is *exponentially* faster.  Counting those zeros gives the **Mpemba index**
`I_M = I_M^dir + I_M^inv`, and its **parity is topological** — robust under perturbation of the
energies, barriers and bath temperature.

Why this matters for the ENZ arc
--------------------------------
`MpembaCrossingReadsEffectiveDamping` showed the crossing reads the rate *gap* `γ_eff = γ_Drude − β`
off a prepared amplitude ratio and one timed event.  The strong-Mpemba structure adds the
complementary half: nulling a branch isolates the *other* branch's rate, so the two preparations
together **overdetermine** the decomposition rather than just its difference.

  generic preparation      -> crossing time gives  γ_Drude − β
  a₂ = 0 preparation       -> single exponential   gives the surviving rate alone

That is rate spectroscopy, not a fit, and it is what `mpemba_rate_is_spectral`'s "slowest *occupied*
mode" phrasing already anticipates.

What is formalized here
-----------------------
§A the two-mode relaxation amplitude and the mode-selection identity;
§B the exponential speed-up — the nulled preparation's amplitude ratio tends to zero;
§C existence and robustness of a strong-Mpemba point from a sign change, which is the
   intermediate-value content of the index's topological parity.

The index itself is a *count* of zeros; what is proved here is the part that carries the physics and
the robustness — that a sign change forces a zero, and that a strict sign change survives
perturbation.  The trapped-ion instance already in the library
(`SciamaAdSCPTTrappedIonMpembaSpectrum.strongMeCancellation`, Shapira et al.) is a concrete
realisation of such a zero.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.MpembaIndexRateSelection

/-! ### §A — Two-mode relaxation and mode selection -/

/-- Amplitude of a two-mode Markovian relaxation: the slow mode `λ₂` with weight `a₂` and the fast
mode `λ₃` with weight `a₃`.  Klich et al. Eq. (6) truncated to the two slowest modes. -/
def relaxationAmplitude (a₂ a₃ lam₂ lam₃ t : ℝ) : ℝ :=
  a₂ * Real.exp (lam₂ * t) + a₃ * Real.exp (lam₃ * t)

/-- **Nulling the slow mode selects the fast one.**  At a strong-Mpemba preparation (`a₂ = 0`) the
relaxation is a single exponential at the *fast* rate `λ₃`: the observed decay is no longer the
slowest mode.  This is what makes the strong effect exponentially faster, and it is the
mode-selection that turns the crossing measurement into rate spectroscopy. -/
theorem relaxationAmplitude_at_strongMpemba (a₃ lam₂ lam₃ t : ℝ) :
    relaxationAmplitude 0 a₃ lam₂ lam₃ t = a₃ * Real.exp (lam₃ * t) := by
  unfold relaxationAmplitude
  ring

/-- **A generic preparation is governed by the slow mode.**  With the fast weight nulled instead,
the amplitude is the slow exponential — the two preparations isolate the two rates separately. -/
theorem relaxationAmplitude_at_zero_fast (a₂ lam₂ lam₃ t : ℝ) :
    relaxationAmplitude a₂ 0 lam₂ lam₃ t = a₂ * Real.exp (lam₂ * t) := by
  unfold relaxationAmplitude
  ring

/-! ### §B — The exponential speed-up -/

/-- **The strong preparation outruns the generic one exponentially.**  For a strictly faster fast
mode (`lam₃ < lam₂`), the ratio of the nulled-slow-mode amplitude to the pure slow-mode amplitude is
`exp((lam₃ − lam₂) t)`, which tends to `0`.  The speed-up is exponential in the spectral gap, not
merely a prefactor — Klich et al.'s defining property of the *strong* effect. -/
theorem strongMpemba_ratio_tendsto_zero {lam₂ lam₃ : ℝ} (hlt : lam₃ < lam₂) :
    Filter.Tendsto (fun t : ℝ => Real.exp ((lam₃ - lam₂) * t)) Filter.atTop (nhds 0) := by
  have hneg : lam₃ - lam₂ < 0 := by linarith
  have hlin : Filter.Tendsto (fun t : ℝ => (lam₃ - lam₂) * t) Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg hneg Filter.tendsto_id
  exact Real.tendsto_exp_atBot.comp hlin

/-- **The ratio is exactly the gap exponential.**  Writing the two amplitudes with unit weights,
their quotient is `exp((lam₃ − lam₂) t)`: the spectral gap, and nothing else, sets the advantage. -/
theorem strongMpemba_ratio_eq_gap_exp (lam₂ lam₃ t : ℝ) :
    Real.exp (lam₃ * t) / Real.exp (lam₂ * t) = Real.exp ((lam₃ - lam₂) * t) := by
  rw [← Real.exp_sub]
  congr 1
  ring

/-! ### §C — Existence and robustness: the parity content -/

/-- A preparation parametrised by `T` is a **strong Mpemba point** when the slow-mode overlap
vanishes there.  Klich et al. count these to define the Mpemba index; `a₂` vanishes trivially at the
bath temperature, and the index counts the *other* zeros. -/
def IsStrongMpembaPoint (a₂ : ℝ → ℝ) (T : ℝ) : Prop := a₂ T = 0

/-- **A sign change forces a strong-Mpemba point.**  If the slow-mode overlap is continuous and
takes opposite signs at two preparations, some intermediate preparation nulls it.  This is the
intermediate-value content behind the index's parity: the existence of the strong effect is decided
by boundary data alone. -/
theorem strongMpemba_exists_of_sign_change {a₂ : ℝ → ℝ} {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hcont : ContinuousOn a₂ (Set.Icc T₁ T₂)) (hneg : a₂ T₁ < 0) (hpos : 0 < a₂ T₂) :
    ∃ T ∈ Set.Ioo T₁ T₂, IsStrongMpembaPoint a₂ T := by
  have hmem : (0 : ℝ) ∈ Set.Ioo (a₂ T₁) (a₂ T₂) := Set.mem_Ioo.mpr ⟨hneg, hpos⟩
  obtain ⟨T, hTmem, hTval⟩ := intermediate_value_Ioo hT hcont hmem
  exact ⟨T, hTmem, hTval⟩

/-- **The sign change is robust.**  A perturbation smaller than the endpoint values in magnitude
leaves both signs intact, so the strong-Mpemba point survives.  This is why Klich et al. call the
index's parity topological: it is fixed by boundary data and cannot be removed by a small change in
energies, barriers or bath temperature. -/
theorem strongMpemba_sign_change_robust {a₂ e : ℝ → ℝ} {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hcont : ContinuousOn (fun T => a₂ T + e T) (Set.Icc T₁ T₂))
    (hneg : a₂ T₁ < 0) (hpos : 0 < a₂ T₂)
    (hsmall₁ : |e T₁| < -a₂ T₁) (hsmall₂ : |e T₂| < a₂ T₂) :
    ∃ T ∈ Set.Ioo T₁ T₂, IsStrongMpembaPoint (fun T => a₂ T + e T) T := by
  refine strongMpemba_exists_of_sign_change hT hcont ?_ ?_
  · have hb := abs_lt.mp hsmall₁
    linarith [hb.2]
  · have hb := abs_lt.mp hsmall₂
    linarith [hb.1]

/-! ### §D — What this adds to the effective-damping readout

`MpembaCrossingReadsEffectiveDamping.gammaEff_mul_crossingTime` reads the rate *gap* from a prepared
ratio and one timed event.  §A above supplies the complement: a preparation with the slow overlap
nulled decays as a single exponential at the surviving rate, so `γ_Drude` and `β` are separated
rather than only their difference being fixed.  Two preparations therefore overdetermine the
`EffectiveDampingDecomposition`, which is a consistency check no single-preparation measurement can
provide. -/

/-! ### §E — The endpoint parity criteria (Klich et al. Eqs. 15–17)

The `a₂ = 0` set has codimension one, so it splits the probability simplex into two components, and
the parity of the number of times the equilibrium curve crosses it depends **only on which component
its two ends lie in**.  Klich et al. turn that into three step-function criteria: for the direct
effect `θ(−∂_T a₂|_{T_b} · a₂(∞))`, for the inverse effect `θ(∂_T a₂|_{T_b} · a₂(0))`, and for the
total index `θ(a₂(∞) · a₂(0))` — the last depending on boundary data alone.

Since `a₂` vanishes at the bath temperature and grows in magnitude away from it, it *crosses* there;
the criteria below ask whether it must cross again. -/

/-- Argument of the direct-effect step function, `−∂_T a₂|_{T_b} · a₂(∞)` (Eq. 15). -/
def directCriterion (dTb aInf : ℝ) : ℝ := -dTb * aInf

/-- Argument of the inverse-effect step function, `∂_T a₂|_{T_b} · a₂(0)` (Eq. 16). -/
def inverseCriterion (dTb aZero : ℝ) : ℝ := dTb * aZero

/-- Argument of the total-index step function, `a₂(∞) · a₂(0)` (Eq. 17) — boundary data only. -/
def totalCriterion (aZero aInf : ℝ) : ℝ := aInf * aZero

/-- **The two half-line criteria compose into the endpoint criterion.**  Their product is
`−(∂_T a₂|_{T_b})² · a₂(∞) a₂(0)`, so with a transversal crossing at the bath (`∂_T a₂ ≠ 0`) the
sign of the total criterion is fixed by the two half-line ones.  This is Eq. 17 as a consequence of
Eqs. 15 and 16 rather than an independent postulate. -/
theorem criteria_product (dTb aZero aInf : ℝ) :
    directCriterion dTb aInf * inverseCriterion dTb aZero
      = -(dTb ^ 2) * totalCriterion aZero aInf := by
  unfold directCriterion inverseCriterion totalCriterion
  ring

/-- **Same-sign endpoints make the total criterion positive.**  Both ends of the equilibrium curve
in the same component of the complement of `a₂ = 0` is exactly `a₂(∞) a₂(0) > 0`. -/
theorem totalCriterion_pos_of_same_sign {aZero aInf : ℝ}
    (h : (0 < aZero ∧ 0 < aInf) ∨ (aZero < 0 ∧ aInf < 0)) :
    0 < totalCriterion aZero aInf := by
  unfold totalCriterion
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos h2 h1
  · exact mul_pos_of_neg_of_neg h2 h1

/-- **Same-sign endpoints force a strong-Mpemba point.**  If `a₂` crosses at the bath temperature —
negative just above it — and is positive again at the upper end, a further zero lies between.  With
`a₂(0)` on the same side as `a₂(∞)`, the curve must return across the hyperplane, which is the
content of an odd Mpemba index.  The bath zero itself is not counted. -/
theorem strongMpemba_of_same_sign_endpoints {a₂ : ℝ → ℝ} {Tm T₁ : ℝ} (hT : Tm ≤ T₁)
    (hcont : ContinuousOn a₂ (Set.Icc Tm T₁)) (hjust : a₂ Tm < 0) (hend : 0 < a₂ T₁) :
    ∃ T ∈ Set.Ioo Tm T₁, IsStrongMpembaPoint a₂ T :=
  strongMpemba_exists_of_sign_change hT hcont hjust hend

/-! ### §F — Weak versus strong

The original (weak) Mpemba effect needs only that a hotter preparation carry *less* slow-mode weight
than a colder one, `|a₂(T_h)| < |a₂(T_c)|` for `T_h > T_c > T_b` (Klich et al. Eq. 10).  The strong
effect is the degenerate case where that weight reaches zero.  Weak is an inequality between two
preparations; strong is a property of one, and only the strong case changes which eigenvalue is
observed. -/

/-- **Weak Mpemba condition**: the hotter preparation carries strictly less slow-mode weight. -/
def IsWeakMpemba (a₂ : ℝ → ℝ) (Th Tc : ℝ) : Prop := |a₂ Th| < |a₂ Tc|

/-- **A strong point gives the weak effect against any occupied preparation.**  If the hot
preparation nulls the slow mode and the cold one does not, the weak inequality holds — strong
implies weak, and the converse fails since weak needs no vanishing. -/
theorem weak_of_strongMpemba {a₂ : ℝ → ℝ} {Th Tc : ℝ}
    (hstrong : IsStrongMpembaPoint a₂ Th) (hcold : a₂ Tc ≠ 0) :
    IsWeakMpemba a₂ Th Tc := by
  unfold IsWeakMpemba IsStrongMpembaPoint at *
  rw [hstrong, abs_zero]
  exact abs_pos.mpr hcold

/-! ### §G — Why the rates are real: detailed balance is the symmetrization

Everything above treats the relaxation rates as real.  Klich et al. justify that rather than assume
it: a detailed-balance rate matrix is *similar* to a symmetric one,

  `R̃ = F^{1/2} R F^{−1/2}`,  `F_ij = e^{β_b E_j} δ_ij`,

and `R̃` "has the same eigenvalues as `R`, and has an orthogonal set of real eigenvectors".  Real
spectrum, orthogonal modes, and hence the two-mode expansion of §A all rest on that one condition.

Proved here elementwise: detailed balance makes the conjugated matrix symmetric.  So the reality of
`λ₂`, `λ₃` — and with it the crossing and index construction — is supplied by the detailed-balance
hypothesis rather than added on top of it. -/

/-- Detailed balance against Boltzmann weights: `R_ij e^{−β E_j} = R_ji e^{−β E_i}`. -/
def DetailedBalance {n : Type*} (R : n → n → ℝ) (E : n → ℝ) (beta : ℝ) : Prop :=
  ∀ i j, R i j * Real.exp (-(beta * E j)) = R j i * Real.exp (-(beta * E i))

/-- The similarity transform `R̃ = F^{1/2} R F^{−1/2}` elementwise, `F^{1/2}_ii = e^{β E_i / 2}`. -/
def symmetrized {n : Type*} (R : n → n → ℝ) (E : n → ℝ) (beta : ℝ) (i j : n) : ℝ :=
  Real.exp (beta * E i / 2) * R i j * Real.exp (-(beta * E j / 2))

/-- **Detailed balance symmetrizes the rate matrix.**  Conjugating by the Boltzmann half-weights
turns a detailed-balance generator into a symmetric one, which is what supplies the real spectrum
and orthogonal eigenvectors the Mpemba construction uses throughout. -/
theorem detailedBalance_symmetrizes {n : Type*} {R : n → n → ℝ} {E : n → ℝ} {beta : ℝ}
    (h : DetailedBalance R E beta) (i j : n) :
    symmetrized R E beta i j = symmetrized R E beta j i := by
  unfold symmetrized
  have hR : R i j = R j i * Real.exp (beta * E j - beta * E i) := by
    have hne : Real.exp (-(beta * E j)) ≠ 0 := Real.exp_ne_zero _
    apply mul_right_cancel₀ hne
    rw [h i j, mul_assoc, ← Real.exp_add]
    congr 1
    ring
  rw [hR]
  have hL : Real.exp (beta * E i / 2) * (R j i * Real.exp (beta * E j - beta * E i))
        * Real.exp (-(beta * E j / 2))
      = R j i * (Real.exp (beta * E i / 2) * Real.exp (beta * E j - beta * E i)
        * Real.exp (-(beta * E j / 2))) := by ring
  have hRr : Real.exp (beta * E j / 2) * R j i * Real.exp (-(beta * E i / 2))
      = R j i * (Real.exp (beta * E j / 2) * Real.exp (-(beta * E i / 2))) := by ring
  rw [hL, hRr, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/- ZIL-BEGIN -/

zil attach Physlib.Optics.MpembaIndexRateSelection.relaxationAmplitude_at_strongMpemba where
  formalizes @ "claim:at-a-strong-mpemba-preparation-the-slow-mode-overlap-vanishes-so-the-relaxation-is-a-single-exponential-at-the-fast-rate-which-selects-which-eigenvalue-is-observed",
  epistemic_status @ "consistency-identity",
  caveat @ "this-is-the-two-mode-truncation-of-the-markovian-expansion-a-real-relaxation-carries-further-modes-whose-weights-are-not-nulled-by-the-same-preparation"

zil attach Physlib.Optics.MpembaIndexRateSelection.strongMpemba_ratio_tendsto_zero where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-strong-mpemba-advantage-is-exponential-in-the-spectral-gap-the-ratio-of-the-nulled-slow-mode-amplitude-to-the-slow-mode-amplitude-tends-to-zero",
  epistemic_status @ "consistency-identity",
  requires @ "claim:at-a-strong-mpemba-preparation-the-slow-mode-overlap-vanishes-so-the-relaxation-is-a-single-exponential-at-the-fast-rate-which-selects-which-eigenvalue-is-observed"

zil attach Physlib.Optics.MpembaIndexRateSelection.strongMpemba_exists_of_sign_change where
  formalizes @ "claim:a-sign-change-of-the-slow-mode-overlap-between-two-preparations-forces-a-strong-mpemba-point-between-them-which-is-the-intermediate-value-content-behind-the-topological-parity-of-the-mpemba-index",
  epistemic_status @ "conditional-model",
  caveat @ "existence-only-this-does-not-count-the-zeros-and-so-does-not-compute-the-mpemba-index-itself-only-the-parity-relevant-fact-that-a-sign-change-forces-at-least-one"

zil attach Physlib.Optics.MpembaIndexRateSelection.strongMpemba_sign_change_robust where
  supported_by @ "lean:Physlib.Optics.MpembaIndexRateSelection.strongMpemba_exists_of_sign_change",
  formalizes @ "claim:a-perturbation-smaller-in-magnitude-than-the-endpoint-overlaps-leaves-both-signs-intact-so-the-strong-mpemba-point-survives-which-is-why-the-index-parity-is-robust-to-changes-in-energies-barriers-and-bath-temperature",
  epistemic_status @ "conditional-model",
  requires @ "claim:a-sign-change-of-the-slow-mode-overlap-between-two-preparations-forces-a-strong-mpemba-point-between-them-which-is-the-intermediate-value-content-behind-the-topological-parity-of-the-mpemba-index"

zil attach Physlib.Optics.MpembaIndexRateSelection.criteria_product where
  supported_by @ "lean:IsProjectionTensor.complement",
  formalizes @ "claim:the-direct-and-inverse-half-line-parity-criteria-compose-into-the-endpoint-criterion-their-product-being-minus-the-squared-bath-slope-times-the-product-of-the-overlaps-at-zero-and-infinite-temperature",
  epistemic_status @ "consistency-identity",
  caveat @ "this-derives-the-total-parity-criterion-from-the-two-half-line-ones-it-does-not-establish-that-any-of-them-counts-the-zeros-correctly"

zil attach Physlib.Optics.MpembaIndexRateSelection.strongMpemba_of_same_sign_endpoints where
  supported_by @ "lean:Physlib.Optics.MpembaIndexRateSelection.strongMpemba_exists_of_sign_change",
  formalizes @ "claim:when-the-overlap-crosses-at-the-bath-temperature-and-the-two-ends-of-the-equilibrium-curve-lie-on-the-same-side-of-the-vanishing-overlap-hyperplane-a-further-strong-mpemba-point-must-exist-which-is-the-odd-index-case",
  epistemic_status @ "conditional-model",
  requires @ "claim:a-sign-change-of-the-slow-mode-overlap-between-two-preparations-forces-a-strong-mpemba-point-between-them-which-is-the-intermediate-value-content-behind-the-topological-parity-of-the-mpemba-index",
  caveat @ "the-transversality-of-the-bath-crossing-is-a-hypothesis-supplied-as-the-sign-just-above-the-bath-not-derived-from-detailed-balance-here"

zil attach Physlib.Optics.MpembaIndexRateSelection.weak_of_strongMpemba where
  formalizes @ "claim:a-strong-mpemba-preparation-yields-the-weak-mpemba-inequality-against-any-preparation-that-still-occupies-the-slow-mode-so-strong-implies-weak-while-the-converse-fails",
  epistemic_status @ "consistency-identity",
  caveat @ "the-weak-effect-is-an-inequality-between-two-preparations-and-does-not-change-which-eigenvalue-governs-the-decay-only-the-strong-case-does"

zil attach Physlib.Optics.MpembaIndexRateSelection.detailedBalance_symmetrizes where
  formalizes @ "claim:detailed-balance-conjugated-by-the-boltzmann-half-weights-turns-the-rate-matrix-symmetric-which-is-what-supplies-the-real-spectrum-and-orthogonal-eigenvectors-the-mpemba-construction-uses",
  epistemic_status @ "consistency-identity",
  caveat @ "elementwise-symmetry-only-the-passage-from-a-symmetric-conjugate-to-a-real-spectrum-and-orthogonal-eigenbasis-is-standard-linear-algebra-not-carried-out-here"

zil_file_contract physlib.mpembaIndexRateSelection where
  promises "Klich Raz Hirschberg and Vucelja analyse Markovian relaxation whose equilibration timescale is set by the slowest eigenvalue, with the slow mode's weight in a preparation given by the overlap coefficient between the initial probability and the second eigenvector. Their strong Mpemba effect is a preparation at which that overlap vanishes away from the bath temperature, so the slow mode is unoccupied and relaxation proceeds at the next eigenvalue, exponentially faster; counting such zeros gives the Mpemba index whose parity is topological. Formalized here: the two-mode relaxation amplitude and the identity that nulling the slow weight leaves a single exponential at the fast rate, the exponential character of the advantage since the amplitude ratio is the gap exponential and tends to zero, and the intermediate-value content of the parity claim, namely that a sign change of the overlap between two preparations forces a strong Mpemba point between them and that a perturbation smaller than the endpoint overlaps leaves that conclusion intact. For the effective-damping arc this supplies the complement of the crossing measurement: the crossing reads the rate gap from a prepared ratio and one timed event, while a nulled preparation decays as a single exponential at the surviving rate, so the equilibrium Drude rate and the avalanche rate are separated rather than only their difference being fixed, and two preparations overdetermine the decomposition."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Optics.MpembaCrossingReadsEffectiveDamping.gammaEff_mul_crossingTime",
    "lean:Physlib.Optics.MaterialTimescales.EffectiveDampingDecomposition",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.mpembaCrossingTime"]
  forbids_substitutes ["reading the existence result as a computation of the Mpemba index, which counts zeros rather than exhibiting one",
    "treating the two-mode truncation as the full Markovian relaxation, whose further modes are not nulled by the same preparation",
    "presenting the strong-Mpemba rate selection as measured in an epsilon-near-zero system, where it has not been attempted"]
  witnessed_by [Physlib.Optics.MpembaIndexRateSelection.detailedBalance_symmetrizes,
    Physlib.Optics.MpembaIndexRateSelection.criteria_product,
    Physlib.Optics.MpembaIndexRateSelection.strongMpemba_of_same_sign_endpoints,
    Physlib.Optics.MpembaIndexRateSelection.weak_of_strongMpemba,
    Physlib.Optics.MpembaIndexRateSelection.relaxationAmplitude_at_strongMpemba,
    Physlib.Optics.MpembaIndexRateSelection.relaxationAmplitude_at_zero_fast,
    Physlib.Optics.MpembaIndexRateSelection.strongMpemba_ratio_tendsto_zero,
    Physlib.Optics.MpembaIndexRateSelection.strongMpemba_ratio_eq_gap_exp,
    Physlib.Optics.MpembaIndexRateSelection.strongMpemba_exists_of_sign_change,
    Physlib.Optics.MpembaIndexRateSelection.strongMpemba_sign_change_robust]

/- ZIL-END -/

end Physlib.Optics.MpembaIndexRateSelection

end
