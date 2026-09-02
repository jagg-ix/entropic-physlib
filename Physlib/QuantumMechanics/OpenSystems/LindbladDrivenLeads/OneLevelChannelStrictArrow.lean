/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelDiagonalKL
meta import Zil

/-!
# The strict entropic arrow of the one-level channel on arbitrary qubit states

This file instantiates the non-commuting strict data-processing reduction
(`qRelativeEnt_strictLt_of_pinched_strict`) for the one-level generalized-amplitude-damping channel:
for **any** qubit state `ρ` — coherences allowed — whose excited occupation `⟨1|ρ|1⟩` is off the
stationary value, one channel step strictly decreases the quantum relative entropy to the stationary
state:

  `𝐃(Φρ ‖ σ_f) < 𝐃(ρ ‖ σ_f)`.

The three hypotheses of the reduction are discharged concretely:

* **Pinching computes.** For the non-degenerate stationary reference (`f ≠ 1/2`), the pinching channel
  in `σ_f`'s eigenbasis is dephasing to the computational basis: `pinching_map σ_f ρ` is the diagonal
  occupation state `occState ⟨1|ρ|1⟩` (`pinching_map_stationaryState`). This is an explicit
  spectrum/functional-calculus computation: the pinching Kraus projectors are indicator functions of
  the two distinct eigenvalues `1-f ≠ f`, so off-diagonal entries are annihilated and diagonal entries
  survive.
* **Pinching commutes with the channel** (`hcomm`): both sides equal
  `occState (f·damping + ⟨1|ρ|1⟩·survival)`, by the explicit channel action on diagonal states
  (`oneLevelChannel_occState`) and on the occupation (`excitedOccupation_oneLevelChannel`).
* **The pinched part strictly decreases** (`hdiag`): the occupation moves strictly toward `f` by the
  damping step, and `binaryKL (·‖f)` is strictly monotone on each side of `f`
  (`binaryKL_damping_step_lt`), transported through the diagonal-KL bridge.

The complementary **coherence sector** is closed by the strict entropy production of pure dephasing:
a state at the stationary occupation with nonzero coherence has its eigenvalue product (determinant)
strictly raised by `damping·|x|²`, so its von Neumann entropy — the binary entropy of a qubit
eigenvalue, pinned by trace and determinant alone — strictly increases, while the diagonal
contribution to the relative entropy is unchanged (`oneLevelChannel_qRelativeEnt_strictLt_of_coherence`).
Together (`oneLevelChannel_qRelativeEnt_strictLt_of_ne`): **every** interior-occupation qubit state
other than the stationary state strictly decreases.

Honest scope: the degenerate reference `f = 1/2` (infinite-temperature) makes the pinching trivial
(single eigenvalue) and is excluded from the population branch, hence from the combined theorem; the
boundary occupations `⟨1|ρ|1⟩ ∈ {0,1}` are likewise excluded by the interiority hypotheses.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Physlib.Thermodynamics.QuantumRelativeEntropyArrow
open QuantumInfo.Finite
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
open scoped RealInnerProductSpace

/-! ## The excited occupation of a qubit state -/

/-- The excited-state occupation `⟨1|ρ|1⟩` of a qubit state, as a real number. -/
def excitedOccupation (ρ : MState Qubit) : ℝ := (ρ.m 1 1).re

section DiagonalEntries

open ComplexOrder

private theorem m_diag_facts (ρ : MState Qubit) (i : Qubit) :
    0 ≤ (ρ.m i i).re ∧ (ρ.m i i).im = 0 := by
  have hpsd : (0 : ℂ) ≤ ρ.m i i := Matrix.PosSemidef.diag_nonneg ρ.psd
  have hre : (0 : ℂ).re ≤ (ρ.m i i).re := (Complex.le_def.mp hpsd).1
  have him : (0 : ℂ).im = (ρ.m i i).im := (Complex.le_def.mp hpsd).2
  constructor
  · simpa using hre
  · simpa using him.symm

end DiagonalEntries

theorem excitedOccupation_nonneg (ρ : MState Qubit) : 0 ≤ excitedOccupation ρ :=
  (m_diag_facts ρ 1).1

/-- The excited diagonal entry is real, with value `excitedOccupation ρ`. -/
theorem m_one_one_eq (ρ : MState Qubit) :
    ρ.m 1 1 = ((excitedOccupation ρ : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [excitedOccupation]
  · simpa using (m_diag_facts ρ 1).2

/-- The ground diagonal entry is real, with value `1 - excitedOccupation ρ` (unit trace). -/
theorem m_zero_zero_eq (ρ : MState Qubit) :
    ρ.m 0 0 = ((1 - excitedOccupation ρ : ℝ) : ℂ) := by
  have htr : ρ.m.trace = 1 := ρ.tr'
  rw [Matrix.trace_fin_two, m_one_one_eq ρ] at htr
  push_cast
  linear_combination htr

theorem excitedOccupation_le_one (ρ : MState Qubit) : excitedOccupation ρ ≤ 1 := by
  have h0 : 0 ≤ (ρ.m 0 0).re := (m_diag_facts ρ 0).1
  have heq : (ρ.m 0 0).re = 1 - excitedOccupation ρ := by
    rw [m_zero_zero_eq ρ]
    simp
  linarith [heq ▸ h0]

/-! ## The channel action on diagonal occupation states -/

/-- The density matrix of the diagonal occupation state. -/
theorem occState_m (N : ℝ) (h0 : 0 ≤ N) (h1 : N ≤ 1) :
    (occState N h0 h1).m = !![((1 - N : ℝ) : ℂ), 0; 0, ((N : ℝ) : ℂ)] := by
  show (MState.ofClassical (occDist N h0 h1)).M.mat = _
  rw [MState.coe_ofClassical, HermitianMat.diagonal_mat]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [occDist, ProbDistribution.mk']

theorem occState_congr {N₁ N₂ : ℝ} (h : N₁ = N₂)
    {h01 : 0 ≤ N₁} {h11 : N₁ ≤ 1} {h02 : 0 ≤ N₂} {h12 : N₂ ≤ 1} :
    occState N₁ h01 h11 = occState N₂ h02 h12 := by
  subst h; rfl

/-- The damping step keeps the occupation in `[0,1]` (lower bound). -/
theorem occupationStep_nonneg (d : OneLevelChannelData) {N : ℝ} (h0 : 0 ≤ N) :
    0 ≤ d.occupation * d.damping + N * d.survival :=
  add_nonneg (mul_nonneg d.occupation_nonneg d.damping_nonneg)
    (mul_nonneg h0 d.survival_nonneg)

/-- The damping step keeps the occupation in `[0,1]` (upper bound). -/
theorem occupationStep_le_one (d : OneLevelChannelData) {N : ℝ} (h1 : N ≤ 1) :
    d.occupation * d.damping + N * d.survival ≤ 1 := by
  have h2 : d.occupation * d.damping ≤ d.damping :=
    mul_le_of_le_one_left d.damping_nonneg d.occupation_le_one
  have h3 : N * d.survival ≤ d.survival :=
    mul_le_of_le_one_left d.survival_nonneg h1
  have hs : d.survival = 1 - d.damping := rfl
  linarith

/-- **The one-level channel maps diagonal occupation states to diagonal occupation states**, moving the
occupation by the damping step `N ↦ f·damping + N·survival`. -/
theorem oneLevelChannel_occState (d : OneLevelChannelData) {N : ℝ} (h0 : 0 ≤ N) (h1 : N ≤ 1) :
    oneLevelChannel d (occState N h0 h1)
      = occState (d.occupation * d.damping + N * d.survival)
          (occupationStep_nonneg d h0) (occupationStep_le_one d h1) := by
  apply MState.ext_m
  rw [CPTPMap.mat_coe_eq_apply_mat, oneLevelChannel_map_eq, occState_m, occState_m]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, OneLevelChannelData.survival] <;>
    ring

/-- The channel action on the excited occupation of an **arbitrary** qubit state: the same damping
step, regardless of coherences. -/
theorem excitedOccupation_oneLevelChannel (d : OneLevelChannelData) (ρ : MState Qubit) :
    excitedOccupation (oneLevelChannel d ρ)
      = d.occupation * d.damping + excitedOccupation ρ * d.survival := by
  have hm : (oneLevelChannel d ρ).m = (oneLevelChannel d).map ρ.m :=
    CPTPMap.mat_coe_eq_apply_mat (oneLevelChannel d) ρ
  show ((oneLevelChannel d ρ).m 1 1).re = _
  rw [hm, oneLevelChannel_map_eq, m_zero_zero_eq ρ, m_one_one_eq ρ]
  have hs : d.survival = 1 - d.damping := rfl
  simp [Matrix.cons_val_one, hs]
  ring

/-! ## The pinching channel of the stationary reference is computational-basis dephasing -/

/-- Every diagonal entry of a real-diagonal complex matrix is in its real spectrum. -/
theorem mem_spectrum_diagonalCoe (g : Qubit → ℝ) (i : Qubit) :
    g i ∈ spectrum ℝ (Matrix.diagonal fun j => ((g j : ℝ) : ℂ)) := by
  have hC : ((g i : ℝ) : ℂ) ∈ spectrum ℂ (Matrix.diagonal fun j => ((g j : ℝ) : ℂ)) := by
    rw [spectrum_diagonal]
    exact ⟨i, rfl⟩
  exact spectrum.of_algebraMap_mem ℂ hC

/-- The stationary state's Hermitian matrix, in diagonal form. -/
theorem stationaryState_M_diagonal (d : OneLevelChannelData) :
    d.stationaryState.M
      = HermitianMat.diagonal ℂ ![1 - d.occupation, d.occupation] :=
  rfl

/-- The stationary state's density matrix, as a `Matrix.diagonal`. -/
theorem stationaryState_m_diagonal (d : OneLevelChannelData) :
    d.stationaryState.m
      = Matrix.diagonal fun j => ((![1 - d.occupation, d.occupation] j : ℝ) : ℂ) :=
  rfl

/-- The pinching Kraus projectors of the stationary reference are diagonal eigenvalue indicators. -/
theorem pinching_kraus_stationaryState (d : OneLevelChannelData)
    (k : spectrum ℝ d.stationaryState.m) :
    pinching_kraus d.stationaryState k
      = HermitianMat.diagonal ℂ
          (fun i => if (![1 - d.occupation, d.occupation] i : ℝ) = ↑k then 1 else 0) := by
  show d.stationaryState.M.cfc (fun y => if y = ↑k then 1 else 0) = _
  rw [stationaryState_M_diagonal, HermitianMat.cfc_diagonal]
  rfl

/-- **Pinching in the non-degenerate stationary eigenbasis is computational-basis dephasing.** For
`f ≠ 1/2` the two stationary eigenvalues `1-f ≠ f` are distinct, so the pinching projectors are the
two computational-basis projectors: off-diagonal entries are annihilated, diagonal entries survive,
and the result is the diagonal occupation state of `⟨1|ρ|1⟩`. -/
theorem pinching_map_stationaryState (d : OneLevelChannelData)
    (hhalf : d.occupation ≠ 1/2) (ρ : MState Qubit) :
    pinching_map d.stationaryState ρ
      = occState (excitedOccupation ρ) (excitedOccupation_nonneg ρ) (excitedOccupation_le_one ρ) := by
  have hne : (1 - d.occupation : ℝ) ≠ d.occupation := by
    intro hc; exact hhalf (by linarith)
  have hmem0 : (1 - d.occupation : ℝ) ∈ spectrum ℝ d.stationaryState.m := by
    rw [stationaryState_m_diagonal]
    simpa using mem_spectrum_diagonalCoe ![1 - d.occupation, d.occupation] 0
  have hmem1 : d.occupation ∈ spectrum ℝ d.stationaryState.m := by
    rw [stationaryState_m_diagonal]
    simpa using mem_spectrum_diagonalCoe ![1 - d.occupation, d.occupation] 1
  apply MState.ext_m
  have hsum := pinching_eq_sum_conj d.stationaryState ρ
  show (pinching_map d.stationaryState ρ).M.mat = _
  rw [hsum, occState_m]
  funext i j
  rw [Matrix.sum_apply]
  have hterm : ∀ k : spectrum ℝ d.stationaryState.m,
      ((pinching_kraus d.stationaryState k).mat * ρ.M.mat
        * (pinching_kraus d.stationaryState k).mat) i j
      = (if (![1 - d.occupation, d.occupation] i : ℝ) = ↑k then (1:ℂ) else 0)
        * ρ.m i j
        * (if (![1 - d.occupation, d.occupation] j : ℝ) = ↑k then (1:ℂ) else 0) := by
    intro k
    rw [pinching_kraus_stationaryState d k, HermitianMat.diagonal_mat,
      Matrix.mul_diagonal, Matrix.diagonal_mul, MState.mat_M]
    split_ifs <;> simp
  simp only [hterm]
  fin_cases i <;> fin_cases j
  · -- (0,0): the ground diagonal entry survives
    show (∑ k : spectrum ℝ d.stationaryState.m, _) = _
    rw [Finset.sum_eq_single (⟨1 - d.occupation, hmem0⟩ : spectrum ℝ d.stationaryState.m)]
    · simp [m_zero_zero_eq ρ]
    · intro b _ hb
      rw [if_neg (fun hc => hb (Subtype.ext (by simpa using hc.symm)))]
      simp
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · -- (0,1): annihilated (distinct eigenvalues)
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h1 h2
    · exact absurd ((by simpa using h1 : (1 - d.occupation : ℝ) = ↑k).trans
        (by simpa using h2 : (d.occupation : ℝ) = ↑k).symm) hne
    all_goals simp
  · -- (1,0): annihilated (distinct eigenvalues)
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h1 h2
    · exact absurd ((by simpa using h2 : (1 - d.occupation : ℝ) = ↑k).trans
        (by simpa using h1 : (d.occupation : ℝ) = ↑k).symm) hne
    all_goals simp
  · -- (1,1): the excited diagonal entry survives
    show (∑ k : spectrum ℝ d.stationaryState.m, _) = _
    rw [Finset.sum_eq_single (⟨d.occupation, hmem1⟩ : spectrum ℝ d.stationaryState.m)]
    · simp [m_one_one_eq ρ]
    · intro b _ hb
      rw [if_neg (fun hc => hb (Subtype.ext (by simpa using hc.symm)))]
      simp
    · intro habs; exact absurd (Finset.mem_univ _) habs

/-! ## The damping step strictly decreases the Bernoulli relative entropy -/

/-- **The damping step strictly decreases the Bernoulli relative entropy** for any off-equilibrium
occupation: the step `N ↦ f·damping + N·survival` moves `N` strictly toward `f` (landing on `f`
exactly when `damping = 1`), and `binaryKL (·‖f)` is strictly monotone toward its zero at `f`. -/
theorem binaryKL_damping_step_lt (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1)
    {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1) (hNe : N ≠ d.occupation) (hd0 : 0 < d.damping) :
    binaryKL (d.occupation * d.damping + N * d.survival) d.occupation
      < binaryKL N d.occupation := by
  have hs : d.survival = 1 - d.damping := rfl
  have hd1 : d.damping ≤ 1 := d.damping_le_one
  rcases eq_or_lt_of_le hd1 with heq | hlt
  · -- damping = 1: the step lands exactly on the fixed point
    have hval : d.occupation * d.damping + N * d.survival = d.occupation := by
      rw [hs, heq]; ring
    rw [hval]
    have hzero : binaryKL d.occupation d.occupation = 0 := by
      unfold binaryKL
      exact klDivergence_self _
    rw [hzero]
    rcases (binaryKL_nonneg hN0.le hN1.le hf0 hf1).lt_or_eq with hpos | hzero'
    · exact hpos
    · exact absurd ((binaryKL_eq_zero_iff hN0 hN1 hf0 hf1).mp hzero'.symm) hNe
  · -- damping < 1: the step moves strictly toward the fixed point without reaching it
    have hval : d.occupation * d.damping + N * d.survival
        = d.occupation + (N - d.occupation) * (1 - d.damping) := by
      rw [hs]; ring
    rw [hval]
    rcases lt_or_gt_of_ne hNe with hless | hmore
    · -- N < f: N < N' < f, strictly anti side
      have h1 : d.occupation + (N - d.occupation) * (1 - d.damping) < d.occupation := by
        nlinarith
      have h2 : N < d.occupation + (N - d.occupation) * (1 - d.damping) := by
        nlinarith
      exact binaryKL_strictAntiOn hf0 hf1 ⟨hN0, hless⟩ ⟨by linarith, h1⟩ h2
    · -- N > f: f < N' < N, strictly mono side
      have h1 : d.occupation < d.occupation + (N - d.occupation) * (1 - d.damping) := by
        nlinarith
      have h2 : d.occupation + (N - d.occupation) * (1 - d.damping) < N := by
        nlinarith
      exact binaryKL_strictMonoOn hf0 hf1 ⟨h1, by linarith⟩ ⟨hmore, hN1⟩ h2

/-- Transport a strict `binaryKL` comparison of occupations through the diagonal-KL bridge to the
quantum relative entropy of the corresponding diagonal states. -/
theorem qRelativeEnt_occState_lt_occState (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1)
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hkl : binaryKL a d.occupation < binaryKL b d.occupation) :
    qRelativeEnt (occState a ha0.le ha1.le) d.stationaryState
      < qRelativeEnt (occState b hb0.le hb1.le) d.stationaryState := by
  have ea := entropicProperTime_occState_stationaryState d ha0 ha1 hf0 hf1
  have eb := entropicProperTime_occState_stationaryState d hb0 hb1 hf0 hf1
  rw [entropicProperTime_eq_qRelativeEnt] at ea eb
  have hlt : (qRelativeEnt (occState a ha0.le ha1.le) d.stationaryState).toEReal
      < (qRelativeEnt (occState b hb0.le hb1.le) d.stationaryState).toEReal := by
    rw [ea, eb]
    exact_mod_cast hkl
  exact_mod_cast hlt

/-- The stationary reference has trivial kernel (full rank), so relative entropies against it are
finite. -/
theorem stationaryState_ker_bot (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) :
    d.stationaryState.M.ker = ⊥ := by
  have hqpos : ∀ i, 0 < (d.stationaryDist i : ℝ) := by
    intro i
    rw [stationaryDist_apply]
    fin_cases i
    · simpa using (by linarith : (0:ℝ) < 1 - d.occupation)
    · simpa using hf0
  exact ofClassical_ker_bot hqpos

/-! ## The headline: full non-commuting strict decrease -/

/-- **The one-level channel strictly decreases the quantum relative entropy to its stationary state,
on arbitrary qubit states.** For a non-degenerate reference (`0 < f < 1`, `f ≠ 1/2`), positive
damping, and any state `ρ` — coherences allowed — whose excited occupation is off-equilibrium
(`0 < ⟨1|ρ|1⟩ < 1`, `⟨1|ρ|1⟩ ≠ f`), one channel step strictly decreases `𝐃(· ‖ σ_f)`:

the pinching to `σ_f`'s eigenbasis commutes with the channel and the pinched (diagonal) part strictly
decreases by the damping step, so the non-commuting strict data-processing reduction applies — the
off-diagonal coherences are controlled by the (non-strict) DPI, and all strictness comes from the
classical occupation sector. -/
theorem oneLevelChannel_qRelativeEnt_strictLt (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) (hhalf : d.occupation ≠ 1/2)
    (hd0 : 0 < d.damping) (ρ : MState Qubit)
    (hN0 : 0 < excitedOccupation ρ) (hN1 : excitedOccupation ρ < 1)
    (hNe : excitedOccupation ρ ≠ d.occupation) :
    qRelativeEnt (oneLevelChannel d ρ) d.stationaryState
      < qRelativeEnt ρ d.stationaryState := by
  have hN0' : 0 < d.occupation * d.damping + excitedOccupation ρ * d.survival := by
    have hs : d.survival = 1 - d.damping := rfl
    nlinarith [d.damping_le_one]
  have hN1' : d.occupation * d.damping + excitedOccupation ρ * d.survival < 1 := by
    have hs : d.survival = 1 - d.damping := rfl
    nlinarith [d.damping_le_one, d.survival_nonneg]
  apply qRelativeEnt_strictLt_of_pinched_strict (oneLevelChannel d) ρ d.stationaryState
  · -- the pinching commutes with the channel: both sides are the damped occupation state
    calc pinching_map d.stationaryState (oneLevelChannel d ρ)
        = occState (excitedOccupation (oneLevelChannel d ρ)) _ _ :=
          pinching_map_stationaryState d hhalf (oneLevelChannel d ρ)
      _ = occState (d.occupation * d.damping + excitedOccupation ρ * d.survival)
            (occupationStep_nonneg d (excitedOccupation_nonneg ρ))
            (occupationStep_le_one d (excitedOccupation_le_one ρ)) :=
          occState_congr (excitedOccupation_oneLevelChannel d ρ)
      _ = oneLevelChannel d (occState (excitedOccupation ρ)
            (excitedOccupation_nonneg ρ) (excitedOccupation_le_one ρ)) :=
          (oneLevelChannel_occState d (excitedOccupation_nonneg ρ)
            (excitedOccupation_le_one ρ)).symm
      _ = oneLevelChannel d (pinching_map d.stationaryState ρ) := by
          rw [pinching_map_stationaryState d hhalf ρ]
  · -- the pinched part strictly decreases: the damping step moves the occupation toward f
    rw [pinching_map_stationaryState d hhalf ρ,
      oneLevelChannel_occState d (excitedOccupation_nonneg ρ) (excitedOccupation_le_one ρ)]
    have hkl := binaryKL_damping_step_lt d hf0 hf1 hN0 hN1 hNe hd0
    have hlt := qRelativeEnt_occState_lt_occState d hf0 hf1 hN0' hN1' hN0 hN1 hkl
    calc qRelativeEnt (occState (d.occupation * d.damping + excitedOccupation ρ * d.survival)
          (occupationStep_nonneg d (excitedOccupation_nonneg ρ))
          (occupationStep_le_one d (excitedOccupation_le_one ρ))) d.stationaryState
        = qRelativeEnt (occState (d.occupation * d.damping + excitedOccupation ρ * d.survival)
            hN0'.le hN1'.le) d.stationaryState := by rfl
      _ < qRelativeEnt (occState (excitedOccupation ρ) hN0.le hN1.le) d.stationaryState := hlt
      _ = qRelativeEnt (occState (excitedOccupation ρ)
            (excitedOccupation_nonneg ρ) (excitedOccupation_le_one ρ)) d.stationaryState := by rfl
  · -- finiteness: the stationary reference is full-rank
    rw [qRelativeEnt_ne_top_iff, stationaryState_ker_bot d hf0 hf1]
    exact bot_le

/-- The strict entropic-clock form of the headline: one channel step strictly advances the
relative-entropy clock toward equilibrium, for arbitrary (coherence-carrying) off-equilibrium
qubit states. -/
theorem oneLevelChannel_entropicProperTime_strictLt (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) (hhalf : d.occupation ≠ 1/2)
    (hd0 : 0 < d.damping) (ρ : MState Qubit)
    (hN0 : 0 < excitedOccupation ρ) (hN1 : excitedOccupation ρ < 1)
    (hNe : excitedOccupation ρ ≠ d.occupation) :
    entropicProperTime (oneLevelChannel d ρ) d.stationaryState
      < entropicProperTime ρ d.stationaryState :=
  oneLevelChannel_qRelativeEnt_strictLt d hf0 hf1 hhalf hd0 ρ hN0 hN1 hNe

/-! ## The exact time-derivative law `d/dt D_bin(N(t)‖f) = -σ(t)` -/

/-- For nonnegative times the predicted occupation stays strictly inside `(0,1)`: it is the convex
combination `N(t) = (1-s)·f + s·N₀` with weight `s = e^{-2γt} ∈ (0,1]`. -/
theorem RateData.predictedOccupation_mem_Ioo (r : RateData) {N₀ : ℝ}
    (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1) (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    0 < r.predictedOccupation N₀ t ∧ r.predictedOccupation N₀ t < 1 := by
  have hs0 : 0 < Real.exp (-2 * r.gamma * t) := Real.exp_pos _
  have hs1 : Real.exp (-2 * r.gamma * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hγ := r.gamma_pos
    nlinarith
  have hval : r.predictedOccupation N₀ t
      = r.occupation + (N₀ - r.occupation) * Real.exp (-2 * r.gamma * t) := rfl
  constructor
  · rw [hval]
    nlinarith [mul_nonneg hf0.le (by linarith : (0:ℝ) ≤ 1 - Real.exp (-2 * r.gamma * t)),
      mul_pos hN₀0 hs0]
  · rw [hval]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - r.occupation)
        (by linarith : (0:ℝ) ≤ 1 - Real.exp (-2 * r.gamma * t)),
      mul_pos (by linarith : (0:ℝ) < 1 - N₀) hs0]

/-- The exact orbit derivative `Ṅ(t) = -2γ(N(t) - f)`. -/
theorem RateData.predictedOccupation_hasDerivAt (r : RateData) (N₀ t : ℝ) :
    HasDerivAt (fun s => r.predictedOccupation N₀ s)
      (-2 * r.gamma * (r.predictedOccupation N₀ t - r.occupation)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -2 * r.gamma * s) (-2 * r.gamma) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 * r.gamma)
  have hexp : HasDerivAt (fun s => Real.exp (-2 * r.gamma * s))
      (Real.exp (-2 * r.gamma * t) * (-2 * r.gamma)) t := hlin.exp
  have h : HasDerivAt (fun s => r.occupation + (N₀ - r.occupation) * Real.exp (-2 * r.gamma * s))
      ((N₀ - r.occupation) * (Real.exp (-2 * r.gamma * t) * (-2 * r.gamma))) t :=
    (hexp.const_mul (N₀ - r.occupation)).const_add r.occupation
  have hv : (N₀ - r.occupation) * (Real.exp (-2 * r.gamma * t) * (-2 * r.gamma))
      = -2 * r.gamma * (r.predictedOccupation N₀ t - r.occupation) := by
    rw [RateData.predictedOccupation_sub_occupation]
    ring
  exact hv ▸ h

/-- **The exact entropy-production law.** Along the one-level orbit the binary relative entropy to the
stationary occupation satisfies `d/dt D_bin(N(t)‖f) = -σ(t)` exactly, with
`σ = 2γ(N-f)[log(N/f) - log((1-N)/(1-f))]` the entropy production rate: the chain rule composed from
the occupation-derivative of `binaryKL` (the log-odds) and the orbit derivative `Ṅ = -2γ(N-f)`. -/
theorem binaryKL_predictedOccupation_hasDerivAt (r : RateData) {N₀ : ℝ}
    (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1) (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => binaryKL (r.predictedOccupation N₀ s) r.occupation)
      (-(entropyProductionRate r.gamma (r.predictedOccupation N₀ t) r.occupation)) t := by
  obtain ⟨hN0, hN1⟩ := r.predictedOccupation_mem_Ioo hN₀0 hN₀1 hf0 hf1 ht
  have hKL := binaryKL_hasDerivAt hf0 hf1 hN0 hN1
  have hN := r.predictedOccupation_hasDerivAt N₀ t
  have hcomp := HasDerivAt.comp t hKL hN
  have hcomp' : HasDerivAt (fun s => binaryKL (r.predictedOccupation N₀ s) r.occupation)
      ((Real.log (r.predictedOccupation N₀ t / r.occupation)
          - Real.log ((1 - r.predictedOccupation N₀ t) / (1 - r.occupation)))
        * (-2 * r.gamma * (r.predictedOccupation N₀ t - r.occupation))) t := by
    simpa [Function.comp_def] using hcomp
  have hv : (Real.log (r.predictedOccupation N₀ t / r.occupation)
        - Real.log ((1 - r.predictedOccupation N₀ t) / (1 - r.occupation)))
      * (-2 * r.gamma * (r.predictedOccupation N₀ t - r.occupation))
      = -(entropyProductionRate r.gamma (r.predictedOccupation N₀ t) r.occupation) := by
    unfold entropyProductionRate
    ring
  exact hv ▸ hcomp'

/-- **Strictly falling relative entropy.** Away from equilibrium the time-derivative of the binary
relative entropy along the orbit is strictly negative — the strict second law in derivative form. -/
theorem binaryKL_predictedOccupation_deriv_neg (r : RateData) {N₀ : ℝ}
    (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1) (hf0 : 0 < r.occupation) (hf1 : r.occupation < 1)
    (hne : N₀ ≠ r.occupation) {t : ℝ} (ht : 0 ≤ t) :
    -(entropyProductionRate r.gamma (r.predictedOccupation N₀ t) r.occupation) < 0 := by
  obtain ⟨hN0, hN1⟩ := r.predictedOccupation_mem_Ioo hN₀0 hN₀1 hf0 hf1 ht
  have hNe : r.predictedOccupation N₀ t ≠ r.occupation := by
    intro hc
    have hsub := r.predictedOccupation_sub_occupation N₀ t
    rw [hc, sub_self] at hsub
    exact hne (by
      have hexp : Real.exp (-2 * r.gamma * t) ≠ 0 := (Real.exp_pos _).ne'
      have hN₀f : N₀ - r.occupation = 0 := by
        rcases mul_eq_zero.mp hsub.symm with h | h
        · exact h
        · exact absurd h hexp
      linarith)
  have hσ := entropyProductionRate_pos r.gamma_pos hN0 hN1 hf0 hf1 hNe
  linarith

/-! ## Qubit spectral data from trace and determinant -/

/-- The lower-left entry is the conjugate of the coherence (Hermiticity). -/
theorem m_one_zero_eq (ρ : MState Qubit) :
    ρ.m 1 0 = (starRingEnd ℂ) (ρ.m 0 1) := by
  have h := ρ.Hermitian.apply 1 0
  rw [starRingEnd_apply]
  exact h.symm

/-- The determinant of a qubit state: `det ρ = N(1-N) - |x|²` with `N` the excited occupation and
`x` the coherence. -/
theorem det_m_eq (ρ : MState Qubit) :
    ρ.m.det = ((excitedOccupation ρ * (1 - excitedOccupation ρ)
      - Complex.normSq (ρ.m 0 1) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, m_zero_zero_eq ρ, m_one_one_eq ρ, m_one_zero_eq ρ, Complex.mul_conj]
  push_cast
  ring

/-- The two eigenvalues of a qubit state sum to one (unit trace). -/
theorem eigenvalues_sum (ρ : MState Qubit) :
    ρ.M.H.eigenvalues 0 + ρ.M.H.eigenvalues 1 = 1 := by
  have h := HermitianMat.sum_eigenvalues_eq_trace ρ.M
  rw [Fin.sum_univ_two, ρ.tr] at h
  exact h

/-- The two eigenvalues of a qubit state multiply to the determinant `N(1-N) - |x|²`. -/
theorem eigenvalues_prod (ρ : MState Qubit) :
    ρ.M.H.eigenvalues 0 * ρ.M.H.eigenvalues 1
      = excitedOccupation ρ * (1 - excitedOccupation ρ) - Complex.normSq (ρ.m 0 1) := by
  have h0 := ρ.M.H.det_eq_prod_eigenvalues
  rw [Fin.prod_univ_two] at h0
  have h1 : ρ.m.det = ((ρ.M.H.eigenvalues 0 : ℝ) : ℂ) * ((ρ.M.H.eigenvalues 1 : ℝ) : ℂ) := h0
  rw [det_m_eq ρ] at h1
  exact_mod_cast h1.symm

/-- The spectrum entries of a state are its eigenvalues. -/
theorem spectrum_coe (ρ : MState Qubit) (i : Qubit) :
    (ρ.spectrum i : ℝ) = ρ.M.H.eigenvalues i := rfl

/-- **The von Neumann entropy of a qubit state is the binary entropy of an eigenvalue.** -/
theorem Sᵥₙ_qubit (ρ : MState Qubit) :
    Sᵥₙ ρ = Real.binEntropy (ρ.M.H.eigenvalues 0) := by
  have hsum := eigenvalues_sum ρ
  have hcalc : Sᵥₙ ρ
      = Real.negMulLog (ρ.M.H.eigenvalues 0) + Real.negMulLog (ρ.M.H.eigenvalues 1) := by
    unfold Sᵥₙ Hₛ
    rw [Fin.sum_univ_two]
    rfl
  rw [hcalc, show ρ.M.H.eigenvalues 1 = 1 - ρ.M.H.eigenvalues 0 by linarith,
    ← Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- **Binary entropy strictly increases with the eigenvalue product** `a(1-a)`: values closer to the
maximally mixed point `1/2` have strictly larger entropy. -/
theorem binEntropy_lt_binEntropy_of_mul_lt {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h : a * (1 - a) < b * (1 - b)) :
    Real.binEntropy a < Real.binEntropy b := by
  have hsq : (b - 1/2)^2 < (a - 1/2)^2 := by nlinarith
  have habs : |b - 1/2| < |a - 1/2| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq
  have haval : Real.binEntropy a = Real.binEntropy (1/2 + |a - 1/2|) := by
    rcases le_total (1/2 : ℝ) a with hle | hle
    · rw [abs_of_nonneg (by linarith), show (1/2 : ℝ) + (a - 1/2) = a from by ring]
    · rw [abs_of_nonpos (by linarith), show (1/2 : ℝ) + -(a - 1/2) = 1 - a from by ring,
        Real.binEntropy_one_sub]
  have hbval : Real.binEntropy b = Real.binEntropy (1/2 + |b - 1/2|) := by
    rcases le_total (1/2 : ℝ) b with hle | hle
    · rw [abs_of_nonneg (by linarith), show (1/2 : ℝ) + (b - 1/2) = b from by ring]
    · rw [abs_of_nonpos (by linarith), show (1/2 : ℝ) + -(b - 1/2) = 1 - b from by ring,
        Real.binEntropy_one_sub]
  have hmema : (1/2 : ℝ) + |a - 1/2| ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    have hub : |a - 1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hlb : (0:ℝ) ≤ |a - 1/2| := abs_nonneg _
    constructor <;> [norm_num; linarith]
  have hmemb : (1/2 : ℝ) + |b - 1/2| ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    have hub : |b - 1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hlb : (0:ℝ) ≤ |b - 1/2| := abs_nonneg _
    constructor <;> [norm_num; linarith]
  rw [haval, hbval]
  exact Real.binEntropy_strictAntiOn hmemb hmema (by linarith)

/-- The one-level channel scales the coherence by `√survival`, on any state. -/
theorem oneLevelChannel_m_zero_one (d : OneLevelChannelData) (ρ : MState Qubit) :
    (oneLevelChannel d ρ).m 0 1 = ((Real.sqrt d.survival : ℝ) : ℂ) * ρ.m 0 1 := by
  have hm : (oneLevelChannel d ρ).m = (oneLevelChannel d).map ρ.m :=
    CPTPMap.mat_coe_eq_apply_mat (oneLevelChannel d) ρ
  rw [hm, oneLevelChannel_map_eq]
  simp [Matrix.cons_val_one]

/-- At the stationary occupation the channel leaves the occupation fixed. -/
theorem excitedOccupation_oneLevelChannel_fixed (d : OneLevelChannelData) (ρ : MState Qubit)
    (h : excitedOccupation ρ = d.occupation) :
    excitedOccupation (oneLevelChannel d ρ) = d.occupation := by
  rw [excitedOccupation_oneLevelChannel, h, show d.survival = 1 - d.damping from rfl]
  ring

/-- **Pure dephasing strictly increases the von Neumann entropy.** For a state at the stationary
occupation with nonzero coherence, the channel shrinks the coherence by `√survival`, so the
eigenvalue product (determinant) strictly increases by `damping·|x|²`, and the qubit entropy —
the binary entropy of an eigenvalue — strictly increases. -/
theorem Sᵥₙ_lt_oneLevelChannel_of_coherence (d : OneLevelChannelData) (hd0 : 0 < d.damping)
    (ρ : MState Qubit) (hocc : excitedOccupation ρ = d.occupation) (hcoh : ρ.m 0 1 ≠ 0) :
    Sᵥₙ ρ < Sᵥₙ (oneLevelChannel d ρ) := by
  have hN' : excitedOccupation (oneLevelChannel d ρ) = excitedOccupation ρ := by
    rw [excitedOccupation_oneLevelChannel_fixed d ρ hocc, hocc]
  have hcohΦ : Complex.normSq ((oneLevelChannel d ρ).m 0 1)
      = d.survival * Complex.normSq (ρ.m 0 1) := by
    rw [oneLevelChannel_m_zero_one d ρ, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt d.survival_nonneg]
  have hlt : ρ.M.H.eigenvalues 0 * ρ.M.H.eigenvalues 1
      < (oneLevelChannel d ρ).M.H.eigenvalues 0 * (oneLevelChannel d ρ).M.H.eigenvalues 1 := by
    rw [eigenvalues_prod ρ, eigenvalues_prod (oneLevelChannel d ρ), hN', hcohΦ,
      show d.survival = 1 - d.damping from rfl]
    have hx : 0 < Complex.normSq (ρ.m 0 1) := Complex.normSq_pos.mpr hcoh
    nlinarith
  have hsρ := eigenvalues_sum ρ
  have hsΦ := eigenvalues_sum (oneLevelChannel d ρ)
  have hb0ρ : (0:ℝ) ≤ ρ.M.H.eigenvalues 0 := ρ.eigenvalue_nonneg 0
  have hb1ρ : ρ.M.H.eigenvalues 0 ≤ 1 := ρ.eigenvalue_le_one 0
  have hb0Φ : (0:ℝ) ≤ (oneLevelChannel d ρ).M.H.eigenvalues 0 :=
    (oneLevelChannel d ρ).eigenvalue_nonneg 0
  have hb1Φ : (oneLevelChannel d ρ).M.H.eigenvalues 0 ≤ 1 :=
    (oneLevelChannel d ρ).eigenvalue_le_one 0
  rw [Sᵥₙ_qubit, Sᵥₙ_qubit]
  apply binEntropy_lt_binEntropy_of_mul_lt hb0ρ hb1ρ hb0Φ hb1Φ
  rw [show (1 : ℝ) - ρ.M.H.eigenvalues 0 = ρ.M.H.eigenvalues 1 by linarith,
    show (1 : ℝ) - (oneLevelChannel d ρ).M.H.eigenvalues 0
      = (oneLevelChannel d ρ).M.H.eigenvalues 1 by linarith]
  exact hlt

/-- The matrix logarithm of the stationary state is the diagonal of entrywise logarithms. -/
theorem stationaryState_M_log (d : OneLevelChannelData) :
    d.stationaryState.M.log
      = HermitianMat.diagonal ℂ (fun i => Real.log (![1 - d.occupation, d.occupation] i)) := by
  rw [HermitianMat.log, stationaryState_M_diagonal, HermitianMat.cfc_diagonal]
  rfl

/-- The relative-entropy inner product against the diagonal stationary log depends only on the
state's diagonal entries. -/
theorem inner_stationaryLog_eq (d : OneLevelChannelData) (ρ : MState Qubit)
    (hocc : excitedOccupation ρ = d.occupation) :
    ⟪(oneLevelChannel d ρ).M, d.stationaryState.M.log⟫ = ⟪ρ.M, d.stationaryState.M.log⟫ := by
  have hlog := stationaryState_M_log d
  have hinner : ∀ τ : MState Qubit, ∀ L : Qubit → ℝ,
      ⟪τ.M, HermitianMat.diagonal ℂ L⟫
        = (τ.m 0 0 * ((L 0 : ℝ) : ℂ) + τ.m 1 1 * ((L 1 : ℝ) : ℂ)).re := by
    intro τ L
    rw [HermitianMat.inner_eq_re_trace, HermitianMat.diagonal_mat, Matrix.trace_fin_two,
      Matrix.mul_diagonal, Matrix.mul_diagonal]
    rfl
  have h00 : (oneLevelChannel d ρ).m 0 0 = ρ.m 0 0 := by
    rw [m_zero_zero_eq, m_zero_zero_eq, excitedOccupation_oneLevelChannel_fixed d ρ hocc, hocc]
  have h11 : (oneLevelChannel d ρ).m 1 1 = ρ.m 1 1 := by
    rw [m_one_one_eq, m_one_one_eq, excitedOccupation_oneLevelChannel_fixed d ρ hocc, hocc]
  rw [hlog, hinner, hinner, h00, h11]

/-- **The coherence-sector strict decrease.** For a state at the stationary occupation with nonzero
coherence, one channel step strictly decreases the quantum relative entropy to the stationary state:
the diagonal contribution is unchanged, and the entropy strictly increases under the coherence
damping. Together with the population theorem this covers every off-stationary state. -/
theorem oneLevelChannel_qRelativeEnt_strictLt_of_coherence (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) (hd0 : 0 < d.damping)
    (ρ : MState Qubit) (hocc : excitedOccupation ρ = d.occupation) (hcoh : ρ.m 0 1 ≠ 0) :
    qRelativeEnt (oneLevelChannel d ρ) d.stationaryState
      < qRelativeEnt ρ d.stationaryState := by
  have hker := stationaryState_ker_bot d hf0 hf1
  have hk1 : d.stationaryState.M.ker ≤ ρ.M.ker := hker ▸ bot_le
  have hk2 : d.stationaryState.M.ker ≤ (oneLevelChannel d ρ).M.ker := hker ▸ bot_le
  have hS := Sᵥₙ_lt_oneLevelChannel_of_coherence d hd0 ρ hocc hcoh
  have hAe := Sᵥₙ_eq_neg_trace_log (oneLevelChannel d ρ)
  have hBe := Sᵥₙ_eq_neg_trace_log ρ
  have hdiag := inner_stationaryLog_eq d ρ hocc
  have hE : (qRelativeEnt (oneLevelChannel d ρ) d.stationaryState).toEReal
      < (qRelativeEnt ρ d.stationaryState).toEReal := by
    rw [qRelativeEnt_ker hk2, qRelativeEnt_ker hk1]
    norm_cast
    rw [inner_sub_right, inner_sub_right, hdiag]
    have hcommΦ : ⟪(oneLevelChannel d ρ).M, (oneLevelChannel d ρ).M.log⟫
        = ⟪(oneLevelChannel d ρ).M.log, (oneLevelChannel d ρ).M⟫ := real_inner_comm _ _
    have hcommρ : ⟪ρ.M, ρ.M.log⟫ = ⟪ρ.M.log, ρ.M⟫ := real_inner_comm _ _
    linarith
  exact_mod_cast hE

/-- A qubit state is the stationary state exactly when its occupation is stationary and its
coherence vanishes. -/
theorem eq_stationaryState_iff (d : OneLevelChannelData) (ρ : MState Qubit) :
    ρ = d.stationaryState ↔ excitedOccupation ρ = d.occupation ∧ ρ.m 0 1 = 0 := by
  constructor
  · rintro rfl
    constructor
    · show (d.stationaryState.m 1 1).re = _
      rw [OneLevelChannelData.stationaryState_m]
      simp
    · rw [OneLevelChannelData.stationaryState_m]
      simp
  · rintro ⟨hocc, hcoh⟩
    apply MState.ext_m
    rw [OneLevelChannelData.stationaryState_m]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [m_zero_zero_eq, m_one_one_eq, m_one_zero_eq, hocc, hcoh,
        Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The complete strict entropic arrow.** For a non-degenerate stationary reference and positive
damping, one channel step strictly decreases the quantum relative entropy to the stationary state on
**every** interior-occupation qubit state other than the stationary state itself — population
deviations via the pinching decomposition, coherence deviations via the strict entropy increase of
dephasing. -/
theorem oneLevelChannel_qRelativeEnt_strictLt_of_ne (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) (hhalf : d.occupation ≠ 1/2)
    (hd0 : 0 < d.damping) (ρ : MState Qubit)
    (hN0 : 0 < excitedOccupation ρ) (hN1 : excitedOccupation ρ < 1)
    (hne : ρ ≠ d.stationaryState) :
    qRelativeEnt (oneLevelChannel d ρ) d.stationaryState
      < qRelativeEnt ρ d.stationaryState := by
  rcases eq_or_ne (excitedOccupation ρ) d.occupation with hocc | hocc
  · have hcoh : ρ.m 0 1 ≠ 0 := fun hc => hne ((eq_stationaryState_iff d ρ).mpr ⟨hocc, hc⟩)
    exact oneLevelChannel_qRelativeEnt_strictLt_of_coherence d hf0 hf1 hd0 ρ hocc hcoh
  · exact oneLevelChannel_qRelativeEnt_strictLt d hf0 hf1 hhalf hd0 ρ hN0 hN1 hocc

/-! ## Uniqueness of the strictly-contracting fixed point -/

/-- **Uniqueness of a strictly-contracting channel's fixed point.** If `σ` is a
fixed point of `Φ` and the quantum relative entropy to `σ` strictly decreases for
every other state, then `σ` is the only fixed point.  The proof is a
contradiction: a second fixed point would force `𝐃(ρ‖σ) < 𝐃(ρ‖σ)`. -/
@[zil_level bridge_theorem]
theorem fixedPoint_unique_of_strict_qRelativeEnt {d : Type*} [Fintype d] [DecidableEq d]
    (Φ : CPTPMap d d) (σ : MState d) (_hσfix : Φ σ = σ)
    (hstrict : ∀ ρ, ρ ≠ σ → qRelativeEnt (Φ ρ) (Φ σ) < qRelativeEnt ρ σ)
    {ρ : MState d} (hρfix : Φ ρ = ρ) : ρ = σ := by
  by_contra hne
  have h := hstrict ρ hne
  rw [hρfix, _hσfix] at h
  exact lt_irrefl _ h

/-- **Uniqueness of the one-level stationary state** among interior-occupation
qubit states: the stationary state is the only interior fixed point of the
one-level channel, under the existing faithful-reference hypotheses. -/
@[zil_level physical_theorem]
theorem oneLevelChannel_fixedPoint_unique (d : OneLevelChannelData)
    (hf0 : 0 < d.occupation) (hf1 : d.occupation < 1) (hhalf : d.occupation ≠ 1/2)
    (hd0 : 0 < d.damping) (ρ : MState Qubit)
    (hN0 : 0 < excitedOccupation ρ) (hN1 : excitedOccupation ρ < 1)
    (hfix : oneLevelChannel d ρ = ρ) : ρ = d.stationaryState := by
  by_contra hne
  have h := oneLevelChannel_qRelativeEnt_strictLt_of_ne d hf0 hf1 hhalf hd0 ρ hN0 hN1 hne
  rw [hfix] at h
  exact lt_irrefl _ h

/-- **Global uniqueness of the one-level stationary state.** Positive damping
alone makes `diag(1-f,f)` the only fixed qubit state.  This direct proof uses
the exact population and coherence equations, so it includes boundary
populations and the degenerate reference `f = 1/2` that the strict-relative-
entropy proof above deliberately excludes. -/
@[zil_level physical_theorem]
theorem oneLevelChannel_fixedPoint_unique_all (d : OneLevelChannelData)
    (hd0 : 0 < d.damping) (ρ : MState Qubit)
    (hfix : oneLevelChannel d ρ = ρ) : ρ = d.stationaryState := by
  have hocc0 := congrArg excitedOccupation hfix
  rw [excitedOccupation_oneLevelChannel] at hocc0
  have hocc : excitedOccupation ρ = d.occupation := by
    change d.occupation * d.damping +
      excitedOccupation ρ * (1 - d.damping) = excitedOccupation ρ at hocc0
    nlinarith
  have hcoh0 := congrArg (fun τ : MState Qubit => τ.m 0 1) hfix
  rw [oneLevelChannel_m_zero_one] at hcoh0
  have hslt : Real.sqrt d.survival < 1 := by
    rw [Real.sqrt_lt d.survival_nonneg (by positivity)]
    norm_num
    change d.survival < 1
    exact sub_lt_self 1 hd0
  have hcoh : ρ.m 0 1 = 0 := by
    by_contra hne
    have hsqrtC : ((Real.sqrt d.survival : ℝ) : ℂ) = 1 := by
      apply mul_right_cancel₀ hne
      simpa using hcoh0
    have hsqrt : Real.sqrt d.survival = 1 := by
      exact_mod_cast hsqrtC
    exact (ne_of_lt hslt) hsqrt
  exact (eq_stationaryState_iff d ρ).mpr ⟨hocc, hcoh⟩

end LindbladDrivenLeads
end QuantumMechanics

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.pinching_map_stationaryState where
  formalizes @ "claim:the-pinching-channel-of-the-non-degenerate-one-level-stationary-reference-is-computational-basis-dephasing-mapping-any-qubit-state-to-the-diagonal-state-of-its-excited-occupation",
  supported_by @ "lean:pinching_kraus",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:requires-the-non-degenerate-reference-f-not-one-half-so-that-the-two-stationary-eigenvalues-are-distinct-at-f-equal-one-half-the-pinching-is-the-identity-channel"

zil attach QuantumMechanics.LindbladDrivenLeads.binaryKL_damping_step_lt where
  formalizes @ "claim:the-one-level-damping-step-strictly-decreases-the-bernoulli-relative-entropy-of-any-off-equilibrium-occupation-against-the-stationary-occupation",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.binaryKL_strictMonoOn",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.binaryKL_predictedOccupation_hasDerivAt where
  formalizes @ "claim:the-time-derivative-of-the-binary-relative-entropy-along-the-one-level-orbit-is-exactly-minus-the-entropy-production-rate",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.binaryKL_hasDerivAt",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.entropyProductionRate_pos",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt where
  formalizes @ "claim:one-step-of-the-one-level-channel-strictly-decreases-the-quantum-relative-entropy-to-the-stationary-state-on-arbitrary-coherence-carrying-qubit-states-with-off-equilibrium-occupation",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.qRelativeEnt_strictLt_of_pinched_strict",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.pinching_map_stationaryState",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-branch-covers-off-equilibrium-population-the-complementary-coherence-only-sector-is-the-pure-dephasing-strict-entropy-production-theorem-and-the-degenerate-infinite-temperature-reference-f-equal-one-half-is-excluded"

zil attach QuantumMechanics.LindbladDrivenLeads.Sᵥₙ_lt_oneLevelChannel_of_coherence where
  formalizes @ "claim:pure-dephasing-strictly-increases-the-von-neumann-entropy-of-a-qubit-state-at-stationary-occupation-with-nonzero-coherence-the-eigenvalue-product-rises-by-damping-times-coherence-squared",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.Sᵥₙ_qubit",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt_of_coherence where
  formalizes @ "claim:one-step-of-the-one-level-channel-strictly-decreases-the-quantum-relative-entropy-to-the-stationary-state-on-coherence-only-deviations-at-stationary-occupation",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.Sᵥₙ_lt_oneLevelChannel_of_coherence",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt where
  formalizes @ "claim:a-strictly-relative-entropy-contracting-channel-has-at-most-one-fixed-point",
  unique_up_to @ "lean:QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt",
  supported_by @ "lean:qRelativeEnt"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_fixedPoint_unique where
  formalizes @ "claim:the-one-level-stationary-state-is-the-unique-interior-occupation-fixed-point-of-the-one-level-channel",
  unique_up_to @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt_of_ne",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt_of_ne",
  caveat @ "claim:uniqueness-is-among-interior-occupation-states-under-the-faithful-non-degenerate-reference-hypotheses-not-every-cptp-map"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_fixedPoint_unique_all where
  formalizes @ "claim:positive-damping-makes-the-one-level-stationary-state-the-unique-fixed-point-among-all-qubit-density-operators",
  unique_up_to @ "lean:QuantumMechanics.LindbladDrivenLeads.eq_stationaryState_iff",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.excitedOccupation_oneLevelChannel",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_m_zero_one",
  epistemic_status @ "conditional-model",
  requires @ "assumption:strictly-positive-one-level-damping",
  caveat @ "claim:global-over-the-finite-qubit-state-space-not-an-arbitrary-dimensional-or-continuum-gkls-uniqueness-theorem"

zil attach QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt_of_ne where
  formalizes @ "claim:one-step-of-the-one-level-channel-strictly-decreases-the-quantum-relative-entropy-to-the-stationary-state-on-every-interior-occupation-qubit-state-other-than-the-stationary-state",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_qRelativeEnt_strictLt_of_coherence",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-degenerate-infinite-temperature-reference-f-equal-one-half-and-the-boundary-occupations-zero-and-one-are-excluded-by-the-interiority-hypotheses"

/- ZIL-END -/
