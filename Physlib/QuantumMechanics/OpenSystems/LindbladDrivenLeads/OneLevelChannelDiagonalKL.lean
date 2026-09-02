/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelEntropicArrow
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelProduction
public import Physlib.Thermodynamics.SecondLaw.BipartiteEntropyProduction
public import QuantumInfo.Channels.Pinching
meta import Zil

/-!
# The diagonal-KL bridge: the one-level entropic clock is the Bernoulli relative entropy

`OneLevelChannelEntropicArrow` proved the entropic proper time `entropicProperTime (Φⁿ ρ₀) σ_f`
antitone along the channel orbit, but left the identification of its value with the classical
Bernoulli `binaryKL` — the diagonal restriction — as an open follow-up. This file closes it.

For a diagonal occupation state `diag(1 - N, N)` (`occState N`) and the stationary reference
`diag(1 - f, f)`, the quantum (Umegaki) relative entropy coincides with the classical
Kullback–Leibler divergence of the occupation distributions:

  `entropicProperTime (occState N) σ_f = D_bin(N ‖ f) = binaryKL N f`.

This is the commuting-state reduction: it uses the repository's quantum-to-classical reduction
`SecondLaw.qRelativeEnt_ofClassical_eq_Hₛ_rel` (both states diagonal in the same basis, so their
quantum relative entropy is the classical KL of their eigenvalue distributions), the strict
positivity of the reference distribution (giving the required kernel inclusion), and
`Real.log_div` to match `Hₛ_rel` against `binaryKL`.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Physlib.Thermodynamics.QuantumRelativeEntropyArrow
open QuantumInfo.Finite
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality

/-- The Bernoulli occupation distribution `(1 - N, N)` on a qubit. -/
def occDist (N : ℝ) (h0 : 0 ≤ N) (h1 : N ≤ 1) : ProbDistribution Qubit :=
  ProbDistribution.mk' ![1 - N, N]
    (by intro i; fin_cases i
        · simpa using sub_nonneg.mpr h1
        · simpa using h0)
    (by simp [Fin.sum_univ_two])

/-- The diagonal occupation state `diag(1 - N, N)`. -/
def occState (N : ℝ) (h0 : 0 ≤ N) (h1 : N ≤ 1) : MState Qubit :=
  MState.ofClassical (occDist N h0 h1)

@[simp] theorem occDist_apply (N : ℝ) (h0 : 0 ≤ N) (h1 : N ≤ 1) (i : Qubit) :
    ((occDist N h0 h1 i : ℝ)) = ![1 - N, N] i := by
  simp [occDist, ProbDistribution.mk']

@[simp] theorem stationaryDist_apply (d : OneLevelChannelData) (i : Qubit) :
    ((d.stationaryDist i : ℝ)) = ![1 - d.occupation, d.occupation] i := by
  simp [OneLevelChannelData.stationaryDist, ProbDistribution.mk']

/-- A strictly-positive classical distribution gives a nonsingular (kernel-trivial) diagonal state. -/
theorem ofClassical_ker_bot {q : ProbDistribution Qubit} (hq : ∀ i, 0 < (q i : ℝ)) :
    (MState.ofClassical q).M.ker = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [HermitianMat.mem_ker_iff_mulVec_zero, MState.coe_ofClassical, HermitianMat.diagonal_mat] at hx
  ext i
  have hi := congrFun hx i
  rw [Matrix.mulVec_diagonal] at hi
  have hqne : ((q i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hq i))
  simpa [hqne] using hi

/-- The classical relative entropy of the occupation distribution `(1 - N, N)` against the stationary
distribution `(1 - f, f)` is the Bernoulli relative entropy `binaryKL N f`. -/
theorem Hₛ_rel_occDist_stationaryDist_eq_binaryKL
    (d : OneLevelChannelData) {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) (h0N : 0 ≤ N) (h1N : N ≤ 1) :
    Hₛ_rel (occDist N h0N h1N) d.stationaryDist = binaryKL N d.occupation := by
  rw [binaryKL_eq, Real.log_div (ne_of_gt hN0) (ne_of_gt hf0),
    Real.log_div (by linarith) (by linarith)]
  simp only [Hₛ_rel, Fin.sum_univ_two, occDist_apply, stationaryDist_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- **The diagonal-KL bridge.** For the diagonal occupation state `diag(1 - N, N)` and the stationary
reference `diag(1 - f, f)`, the entropic proper time equals the Bernoulli relative entropy of the
occupation against the stationary occupation. The quantum (Umegaki) relative entropy of two states
diagonal in the same basis is the classical KL divergence of their eigenvalue distributions. -/
theorem entropicProperTime_occState_stationaryState
    (d : OneLevelChannelData) {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) :
    ((entropicProperTime (occState N hN0.le hN1.le) d.stationaryState).toEReal : EReal) =
      ((binaryKL N d.occupation : ℝ) : EReal) := by
  have hqpos : ∀ i, 0 < (d.stationaryDist i : ℝ) := by
    intro i
    rw [stationaryDist_apply]
    fin_cases i
    · simpa using (by linarith : (0:ℝ) < 1 - d.occupation)
    · simpa using hf0
  have h_ker : (MState.ofClassical d.stationaryDist).M.ker ≤
      (MState.ofClassical (occDist N hN0.le hN1.le)).M.ker := by
    rw [ofClassical_ker_bot hqpos]; exact bot_le
  rw [entropicProperTime_eq_qRelativeEnt]
  show ((qRelativeEnt (MState.ofClassical (occDist N hN0.le hN1.le))
      (MState.ofClassical d.stationaryDist)).toEReal : EReal) = _
  rw [Physlib.Thermodynamics.SecondLaw.qRelativeEnt_ofClassical_eq_Hₛ_rel _ _ h_ker,
    Hₛ_rel_occDist_stationaryDist_eq_binaryKL d hN0 hN1 hf0 hf1]

/-- The occupation-derivative of the Bernoulli relative entropy is the log-odds difference
`log(N/f) - log((1-N)/(1-f))` — the bracket appearing in the entropy production rate `σ`. -/
theorem binaryKL_hasDerivAt {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1) :
    HasDerivAt (fun x => binaryKL x f)
      (Real.log (N / f) - Real.log ((1 - N) / (1 - f))) N := by
  have hfne : f ≠ 0 := ne_of_gt hf0
  have hNne : N ≠ 0 := ne_of_gt hN0
  have h1Nne : (1 : ℝ) - N ≠ 0 := by linarith
  have h1fne : (1 : ℝ) - f ≠ 0 := by linarith
  have hEq : (fun x => binaryKL x f)
      = fun x => x * Real.log (x / f) + (1 - x) * Real.log ((1 - x) / (1 - f)) :=
    funext (fun x => binaryKL_eq x f)
  rw [hEq]
  have hlogNf : HasDerivAt (fun x => Real.log (x / f)) (1 / N) N := by
    have h1 : HasDerivAt (fun x => x / f) (1 / f) N := (hasDerivAt_id N).div_const f
    have h3 : HasDerivAt (fun x => Real.log (x / f)) ((1 / f) / (N / f)) N :=
      h1.log (div_pos hN0 hf0).ne'
    have hv : (1 / f) / (N / f) = 1 / N := by field_simp
    exact hv ▸ h3
  have hlog1 : HasDerivAt (fun x => Real.log ((1 - x) / (1 - f))) (-(1 / (1 - N))) N := by
    have hs : HasDerivAt (fun x => 1 - x) (-1) N := (hasDerivAt_id N).const_sub 1
    have h1 : HasDerivAt (fun x => (1 - x) / (1 - f)) (-1 / (1 - f)) N := hs.div_const (1 - f)
    have h3 : HasDerivAt (fun x => Real.log ((1 - x) / (1 - f)))
        ((-1 / (1 - f)) / ((1 - N) / (1 - f))) N :=
      h1.log (div_pos (by linarith) (by linarith)).ne'
    have hv : (-1 / (1 - f)) / ((1 - N) / (1 - f)) = -(1 / (1 - N)) := by field_simp
    exact hv ▸ h3
  have ht1 : HasDerivAt (fun x => x * Real.log (x / f)) (Real.log (N / f) + 1) N := by
    have h : HasDerivAt (fun x => x * Real.log (x / f))
        (1 * Real.log (N / f) + N * (1 / N)) N := (hasDerivAt_id N).mul hlogNf
    have hv : (1 : ℝ) * Real.log (N / f) + N * (1 / N) = Real.log (N / f) + 1 := by field_simp
    exact hv ▸ h
  have ht2 : HasDerivAt (fun x => (1 - x) * Real.log ((1 - x) / (1 - f)))
      (-(Real.log ((1 - N) / (1 - f))) - 1) N := by
    have hs : HasDerivAt (fun x => 1 - x) (-1) N := (hasDerivAt_id N).const_sub 1
    have h : HasDerivAt (fun x => (1 - x) * Real.log ((1 - x) / (1 - f)))
        (-1 * Real.log ((1 - N) / (1 - f)) + (1 - N) * (-(1 / (1 - N)))) N := hs.mul hlog1
    have hv : -1 * Real.log ((1 - N) / (1 - f)) + (1 - N) * (-(1 / (1 - N)))
        = -(Real.log ((1 - N) / (1 - f))) - 1 := by
      rw [mul_neg, mul_one_div, div_self h1Nne]; ring
    exact hv ▸ h
  have h := ht1.add ht2
  have hv : Real.log (N / f) + 1 + (-(Real.log ((1 - N) / (1 - f))) - 1)
      = Real.log (N / f) - Real.log ((1 - N) / (1 - f)) := by ring
  exact hv ▸ h

/-- **Above the reference, the Bernoulli relative entropy strictly increases in the occupation.** -/
theorem binaryKL_strictMonoOn {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    StrictMonoOn (fun N => binaryKL N f) (Set.Ioo f 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo f 1)
  · intro x hx
    rw [Set.mem_Ioo] at hx
    exact (binaryKL_hasDerivAt hf0 hf1 (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo, Set.mem_Ioo] at hx
    rw [(binaryKL_hasDerivAt hf0 hf1 (by linarith [hx.1]) hx.2).deriv]
    have hlogNf : 0 < Real.log (x / f) := Real.log_pos ((one_lt_div hf0).mpr hx.1)
    have hlog1 : Real.log ((1 - x) / (1 - f)) < 0 :=
      Real.log_neg (div_pos (by linarith) (by linarith)) ((div_lt_one (by linarith)).mpr (by linarith))
    linarith

/-- **Below the reference, the Bernoulli relative entropy strictly decreases in the occupation.** -/
theorem binaryKL_strictAntiOn {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    StrictAntiOn (fun N => binaryKL N f) (Set.Ioo 0 f) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 f)
  · intro x hx
    rw [Set.mem_Ioo] at hx
    exact (binaryKL_hasDerivAt hf0 hf1 hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo, Set.mem_Ioo] at hx
    rw [(binaryKL_hasDerivAt hf0 hf1 hx.1 (by linarith [hx.2])).deriv]
    have hlogNf : Real.log (x / f) < 0 := Real.log_neg (div_pos hx.1 hf0) ((div_lt_one hf0).mpr hx.2)
    have hlog1 : 0 < Real.log ((1 - x) / (1 - f)) :=
      Real.log_pos ((one_lt_div (by linarith)).mpr (by linarith))
    linarith

/-- **Strict-DPI decrease (above equilibrium).** For occupations `f < a < b < 1`, the occupation `a`
that is strictly closer to the stationary reference `f` has strictly smaller entropic proper time —
the quantum relative-entropy clock strictly decreases as the diagonal state relaxes toward equilibrium
from above. Strengthens the antitone data-processing bound to a strict inequality on the diagonal sector. -/
theorem entropicProperTime_occState_strictLt_above
    (d : OneLevelChannelData) (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1)
    {a b : ℝ} (ha1 : a < 1) (hb1 : b < 1) (hfa : d.occupation < a) (hab : a < b) :
    entropicProperTime (occState a (by linarith) ha1.le) d.stationaryState
      < entropicProperTime (occState b (by linarith) hb1.le) d.stationaryState := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hkl : binaryKL a d.occupation < binaryKL b d.occupation :=
    binaryKL_strictMonoOn hf0 hf1 ⟨hfa, ha1⟩ ⟨by linarith, hb1⟩ hab
  have ea := entropicProperTime_occState_stationaryState d ha0 ha1 hf0 hf1
  have eb := entropicProperTime_occState_stationaryState d hb0 hb1 hf0 hf1
  have hlt : (entropicProperTime (occState a ha0.le ha1.le) d.stationaryState).toEReal
      < (entropicProperTime (occState b hb0.le hb1.le) d.stationaryState).toEReal := by
    rw [ea, eb]; exact_mod_cast hkl
  exact_mod_cast hlt

/-- **Strict-DPI decrease (below equilibrium).** For occupations `0 < b < a < f`, the occupation `a`
strictly closer to the stationary reference has strictly smaller entropic proper time — the clock
strictly decreases as the diagonal state relaxes toward equilibrium from below. -/
theorem entropicProperTime_occState_strictLt_below
    (d : OneLevelChannelData) (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1)
    {a b : ℝ} (hb0 : 0 < b) (ha0 : 0 < a) (hba : b < a) (haf : a < d.occupation) :
    entropicProperTime (occState a ha0.le (by linarith)) d.stationaryState
      < entropicProperTime (occState b hb0.le (by linarith)) d.stationaryState := by
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hkl : binaryKL a d.occupation < binaryKL b d.occupation :=
    binaryKL_strictAntiOn hf0 hf1 ⟨hb0, by linarith⟩ ⟨ha0, haf⟩ hba
  have ea := entropicProperTime_occState_stationaryState d ha0 ha1 hf0 hf1
  have eb := entropicProperTime_occState_stationaryState d hb0 hb1 hf0 hf1
  have hlt : (entropicProperTime (occState a ha0.le ha1.le) d.stationaryState).toEReal
      < (entropicProperTime (occState b hb0.le hb1.le) d.stationaryState).toEReal := by
    rw [ea, eb]; exact_mod_cast hkl
  exact_mod_cast hlt

/-- **Non-commuting strict data-processing reduction.** For any CPTP channel `Φ` and reference `σ`, the
strict decrease of the quantum relative entropy `𝐃(Φρ‖σ) < 𝐃(ρ‖σ)` follows from *just two* ingredients:
the pinching (dephasing in `σ`'s eigenbasis) commutes with the channel, and the **pinched** (commuting,
diagonal) part strictly decreases. No general faithfulness / strict-Klein is needed: the off-diagonal
(coherence) contribution is controlled by the ordinary data-processing inequality (non-strict), and *all
the strictness comes from the classical diagonal part*.

The Pythagorean decomposition `𝐃(ρ‖σ) = 𝐃(ρ‖Pρ) + 𝐃(Pρ‖σ)` (Hayashi; `pinching_pythagoras`) splits the
relative entropy into the coherence term `𝐃(ρ‖Pρ)` and the classical term `𝐃(Pρ‖σ)`. Applying it to both
`ρ` and `Φρ`, using `P(Φρ) = Φ(Pρ)`, the coherence terms satisfy `𝐃(Φρ‖Φ(Pρ)) ≤ 𝐃(ρ‖Pρ)` by DPI while
the classical terms strictly decrease by hypothesis. -/
theorem qRelativeEnt_strictLt_of_pinched_strict {d : Type*} [Fintype d] [DecidableEq d]
    (Φ : CPTPMap d d) (ρ σ : MState d)
    (hcomm : pinching_map σ (Φ ρ) = Φ (pinching_map σ ρ))
    (hdiag : qRelativeEnt (Φ (pinching_map σ ρ)) σ < qRelativeEnt (pinching_map σ ρ) σ)
    (hfin : qRelativeEnt ρ σ ≠ ⊤) :
    qRelativeEnt (Φ ρ) σ < qRelativeEnt ρ σ := by
  have hb_fin : qRelativeEnt ρ (pinching_map σ ρ) ≠ ⊤ := by
    intro h; rw [pinching_pythagoras ρ σ, h, top_add] at hfin; exact hfin rfl
  have hcoh : qRelativeEnt (Φ ρ) (Φ (pinching_map σ ρ)) ≤ qRelativeEnt ρ (pinching_map σ ρ) :=
    sandwichedRenyiEntropy_DPI_eq_one ρ (pinching_map σ ρ) Φ
  rw [pinching_pythagoras ρ σ, pinching_pythagoras (Φ ρ) σ, hcomm]
  calc qRelativeEnt (Φ ρ) (Φ (pinching_map σ ρ)) + qRelativeEnt (Φ (pinching_map σ ρ)) σ
      ≤ qRelativeEnt ρ (pinching_map σ ρ) + qRelativeEnt (Φ (pinching_map σ ρ)) σ := by gcongr
    _ < qRelativeEnt ρ (pinching_map σ ρ) + qRelativeEnt (pinching_map σ ρ) σ :=
        ENNReal.add_lt_add_left hb_fin hdiag

end LindbladDrivenLeads
end QuantumMechanics

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.entropicProperTime_occState_stationaryState where
  formalizes @ "claim:for-diagonal-occupation-states-the-one-level-entropic-proper-time-umegaki-quantum-relative-entropy-against-the-stationary-reference-equals-the-classical-bernoulli-relative-entropy-binary-kl-of-the-occupations",
  supported_by @ "lean:Physlib.Thermodynamics.SecondLaw.qRelativeEnt_ofClassical_eq_Hₛ_rel",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-commuting-state-diagonal-reduction-the-quantum-relative-entropy-of-two-states-diagonal-in-the-same-basis-is-the-classical-kl-of-their-eigenvalue-distributions-it-does-not-extend-to-non-commuting-states-without-a-further-simultaneous-diagonalization-step"

zil attach QuantumMechanics.LindbladDrivenLeads.binaryKL_hasDerivAt where
  supported_by @ "lean:Space.div_const",
  formalizes @ "claim:the-occupation-derivative-of-the-bernoulli-relative-entropy-against-the-reference-is-the-log-odds-difference-log-n-over-f-minus-log-one-minus-n-over-one-minus-f",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.entropicProperTime_occState_strictLt_above where
  formalizes @ "claim:the-one-level-entropic-proper-time-clock-strictly-decreases-as-the-diagonal-occupation-state-relaxes-toward-the-stationary-reference-from-above-a-strict-strengthening-of-the-data-processing-antitone-bound-on-the-diagonal-sector",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.entropicProperTime_occState_stationaryState",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-strict-decrease-in-the-occupation-parameter-for-diagonal-classical-states-via-the-binary-kl-derivative-being-strictly-signed-away-from-equilibrium"

zil attach QuantumMechanics.LindbladDrivenLeads.qRelativeEnt_strictLt_of_pinched_strict where
  formalizes @ "claim:the-full-non-commuting-strict-data-processing-decrease-of-the-quantum-relative-entropy-under-a-cptp-channel-follows-from-the-pinched-classical-diagonal-part-decreasing-strictly-with-the-off-diagonal-coherence-controlled-by-the-ordinary-non-strict-data-processing-inequality-no-general-faithfulness-or-strict-klein-required",
  supported_by @ "lean:pinching_pythagoras",
  supported_by @ "lean:sandwichedRenyiEntropy_DPI_eq_one",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-reduces-the-non-commuting-strict-dpi-to-the-pinched-commuting-strict-decrease-plus-the-channel-pinching-commutation-the-coherence-strictness-that-would-need-general-faithfulness-is-bypassed-because-the-coherence-term-only-needs-monotone-not-strict-data-processing"

/- ZIL-END -/
