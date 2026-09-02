/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
public import Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
public import Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
public import Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
public import Physlib.QuantumMechanics.EntanglementConcurrence

/-!
# The Bell arc meets the Bloch, decoherence-functional, and variational layers

Mechanical links from the Bell/CHSH modules to three carriers this library already holds
— each statement combines two independently built layers, so their agreement is a theorem:

* **Qubit/Bloch** (`LorenzQubitBlochDynamics`, `Hopf.StokesSpinorIsomorphism`):
  `blochOf` reads the Bloch vector of a density matrix off its Pauli expectations;
  `blochOf_pure_blochSphere` — pure qubits sit **on** the Bloch sphere (the repository's
  `BlochSphere` predicate), by `4·normSq(ab̄) + (n_a−n_b)² = (n_a+n_b)² = 1`;
  `pure_isHopfBlochVector` — for a pure state the construction agrees with the existing
  spinor Hopf base (`IsHopfBlochVector`, the Stokes/Pauli expectations);
  `blochOf_uniform_center`, `blochOf_bellMarginal_center` — the maximally mixed state and
  the **computed Bell marginal** sit at the center of the Bloch ball: no-signalling read
  as Bloch geometry.
* **Decoherence functional / histories** (`QuantumMeasureHistoryHilbert`, the
  path-integral event algebra of Dowker–Johnston–Sorkin):
  `branchGram_isDecoherenceFunctional` — the pure-state branch Gram
  `D(S,T) = (Σ_{i∈S} c_i)* (Σ_{j∈T} c_j)` on the finite event algebra **is** a
  decoherence functional (Hermitian, biadditive, strongly positive) — a concrete
  instantiation of the module's axioms;
  `bellBranch_quantalMeasure_eq_marginal` — for the Bell amplitudes, the quantal measure
  of each branch equals the diagonal of the computed no-signalling marginal: the
  history-Hilbert Born weight and the density-matrix population are the same `1/2`;
  `bellBranch_maximal_interference` — the Bell superposition is maximally coherent: the
  double-slit interference term `2 Re D(α,β)` of the `interference` lemma equals the full
  sum of the branch weights.
* **Variational** (the extremal side of the Tsirelson bound):
  `chshVector_attains_tsirelson` — the bound `2√2` of
  `VectorBanachStoneDistortion.chshVector_le_tsirelson` is **attained** on
  `EuclideanSpace ℝ (Fin 2)` at the optimal `45°` configuration, whose measurement pairs
  are orthogonal — exactly the configuration `chshVector_saturation_orthogonal` forces.
* **Witness-filtered Bloch geometry** (Ikeda–Rayan):
  `modeConcurrence_sq_add_polarization_sq` identifies sublattice mode concurrence with
  the transverse radius of the pure-state Bloch sphere; `abs_witnessAlignment_le_modeConcurrence`
  proves that an arbitrary unit-phase witness sees no more coherence than the mode concurrence;
  `abs_filteredQFI_le_concurrence_mul` then proves the paper's filtered-QFI bound.  These are
  statements about quantum-geometric sensitivity and mode coherence, not an identification of
  the Haldane Dirac gap coefficient with an inertial carrier effective mass.

## References

* F. Dowker, S. Johnston, R. Sorkin (histories/decoherence); the Bloch/Stokes carriers of
  `LorenzQubitBlochDynamics` and `Hopf.StokesSpinorIsomorphism`; the Bell/CHSH arc of
  `BellStateNoSignalling` and `CHSHCorrelationBounds`.
* K. Ikeda and S. Rayan, *Quantum Entanglement, Stratified Spaces, and Topological Matter:
  Towards Entanglement-Sensitive Langlands Data*, arXiv:2601.13467v2.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.VectorBanachStoneDistortion
open Physlib.QuantumMechanics.EntanglementConcurrence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BellBlochHistoryLinks

/-! ## §A — density matrices on the Bloch ball -/

/-- **The Bloch vector of a qubit density matrix**, read off its Pauli expectations:
`r = (2 Re ρ₀₁, −2 Im ρ₀₁, ρ₀₀ − ρ₁₁)`. -/
noncomputable def blochOf (ρ : MState (Fin 2)) : BlochVector :=
  fun i => if i = 0 then 2 * (ρ.m 0 1).re
    else if i = 1 then -(2 * (ρ.m 0 1).im)
    else (ρ.m 0 0).re - (ρ.m 1 1).re

/-- The pure-state density matrix, entrywise. -/
lemma pure_m_eq (ψ : Ket (Fin 2)) :
    (MState.pure ψ).m
      = Matrix.of (fun i j : Fin 2 => ψ.vec i * (starRingEnd ℂ) (ψ.vec j)) :=
  rfl

/-- **The maximally mixed state sits at the center of the Bloch ball.** -/
theorem blochOf_uniform_center :
    blochOf (MState.uniform : MState (Fin 2)) = fun _ => 0 := by
  funext i
  fin_cases i <;>
    simp [blochOf, uniform_m_eq, Matrix.diagonal]

/-- **No-signalling as Bloch geometry**: the computed Bell marginal sits at the center of
the Bloch ball — Alice's qubit carries no Bloch direction at all. -/
theorem blochOf_bellMarginal_center :
    blochOf ((MState.pure bellPhiPlus).traceRight) = fun _ => 0 := by
  rw [bellPhiPlus_traceRight_uniform, blochOf_uniform_center]

/-- The center lies in the repository's Bloch ball. -/
theorem center_mem_blochBall : BlochBall (fun _ => 0) := by
  unfold BlochBall
  norm_num

/-- **Pure qubits sit on the Bloch sphere**: for a normalized ket,
`(2 Re ab̄)² + (2 Im ab̄)² + (n_a − n_b)² = (n_a + n_b)² = 1`. -/
theorem blochOf_pure_blochSphere (ψ : Ket (Fin 2)) :
    BlochSphere (blochOf (MState.pure ψ)) := by
  unfold BlochSphere blochOf
  simp +decide only [pure_m_eq, Matrix.of_apply, if_true, if_false]
  set a := ψ.vec 0
  set b := ψ.vec 1
  have hn : Complex.normSq a + Complex.normSq b = 1 := by
    have h := ψ.normalized
    rw [Fin.sum_univ_two] at h
    simpa [Ket.apply, a, b] using h
  have haa : a * (starRingEnd ℂ) a = (Complex.normSq a : ℂ) := Complex.mul_conj a
  have hbb : b * (starRingEnd ℂ) b = (Complex.normSq b : ℂ) := Complex.mul_conj b
  have habs : (a * (starRingEnd ℂ) b).re ^ 2 + (a * (starRingEnd ℂ) b).im ^ 2
      = Complex.normSq a * Complex.normSq b := by
    rw [show (a * (starRingEnd ℂ) b).re ^ 2 + (a * (starRingEnd ℂ) b).im ^ 2
        = Complex.normSq (a * (starRingEnd ℂ) b) from by
      rw [Complex.normSq_apply]; ring]
    rw [map_mul, Complex.normSq_conj]
  have hre_a : (a * (starRingEnd ℂ) a).re = Complex.normSq a := by
    rw [haa, Complex.ofReal_re]
  have hre_b : (b * (starRingEnd ℂ) b).re = Complex.normSq b := by
    rw [hbb, Complex.ofReal_re]
  rw [hre_a, hre_b]
  linear_combination 4*habs + (Complex.normSq a + Complex.normSq b + 1)*hn

/-- **The construction agrees with the spinor Hopf base**: for a pure state, `blochOf`
coincides with the Stokes/Pauli expectations of the existing Hopf fibration layer
(`IsHopfBlochVector`). -/
theorem pure_isHopfBlochVector (ψ : Ket (Fin 2)) :
    IsHopfBlochVector ψ.vec (blochOf (MState.pure ψ)) := by
  have hz : (MState.pure ψ).m 0 1 = ψ.vec 0 * (starRingEnd ℂ) (ψ.vec 1) := rfl
  have hd0 : (MState.pure ψ).m 0 0 = ψ.vec 0 * (starRingEnd ℂ) (ψ.vec 0) := rfl
  have hd1 : (MState.pure ψ).m 1 1 = ψ.vec 1 * (starRingEnd ℂ) (ψ.vec 1) := rfl
  intro i
  fin_cases i
  · show stokesS (Sum.inr 0) ψ.vec = _
    rw [stokesS1_apply]
    simp +decide only [blochOf, if_true, if_false]
    rw [hz]
    simp only [Complex.star_def]
    have h := Complex.add_conj (ψ.vec 0 * (starRingEnd ℂ) (ψ.vec 1))
    rw [map_mul, Complex.conj_conj] at h
    push_cast at h ⊢
    linear_combination h
  · show stokesS (Sum.inr 1) ψ.vec = _
    rw [stokesS2_apply]
    simp +decide only [blochOf, if_true, if_false]
    rw [hz]
    simp only [Complex.star_def]
    have h := Complex.sub_conj (ψ.vec 0 * (starRingEnd ℂ) (ψ.vec 1))
    rw [map_mul, Complex.conj_conj] at h
    push_cast at h ⊢
    linear_combination Complex.I * h
      + ((2 : ℂ) * ((ψ.vec 0 * (starRingEnd ℂ) (ψ.vec 1)).im : ℂ)) * Complex.I_sq
  · show stokesS (Sum.inr 2) ψ.vec = _
    rw [stokesS3_apply]
    simp +decide only [blochOf, if_true, if_false]
    rw [hd0, hd1, Complex.mul_conj, Complex.mul_conj, Complex.ofReal_re,
      Complex.ofReal_re]
    simp only [Complex.star_def]
    have h0 := Complex.mul_conj (ψ.vec 0)
    have h1 := Complex.mul_conj (ψ.vec 1)
    push_cast at h0 h1 ⊢
    linear_combination h0 - h1

/-! ## §B — the pure-state branch Gram is a decoherence functional -/

/-- **The branch Gram of a pure superposition** on the finite event algebra:
`D(S,T) = (Σ_{i∈S} c_i)^* · (Σ_{j∈T} c_j)` — the decoherence functional of a pure state
over branches with amplitudes `c`. -/
noncomputable def branchGram {n : ℕ} (c : Fin n → ℂ) (S T : Finset (Fin n)) : ℂ :=
  (starRingEnd ℂ) (∑ i ∈ S, c i) * (∑ j ∈ T, c j)

/-- **The branch Gram is a decoherence functional** — Hermitian, biadditive on disjoint
events, and strongly positive: the axioms of `QuantumMeasureHistoryHilbert` instantiated
by a concrete pure-state history system. -/
theorem branchGram_isDecoherenceFunctional {n : ℕ} (c : Fin n → ℂ) :
    IsDecoherenceFunctional (branchGram c) where
  hermitian S T := by
    unfold branchGram
    rw [map_mul, Complex.conj_conj, mul_comm]
  biadditive α β γ hd := by
    unfold branchGram
    rw [Finset.sup_eq_union, Finset.sum_union hd, mul_add]
  posSemidef s u := by
    have key : ∑ α ∈ s, ∑ β ∈ s, (starRingEnd ℂ) (u α) * u β * branchGram c α β
        = (starRingEnd ℂ) (∑ α ∈ s, u α * ∑ i ∈ α, c i)
            * (∑ β ∈ s, u β * ∑ j ∈ β, c j) := by
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      unfold branchGram
      rw [map_mul]
      ring
    rw [key, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _

/-- The Bell branch amplitudes: two branches, each of weight `1/√2`. -/
noncomputable def bellBranchAmplitude : Fin 2 → ℂ := fun _ => ((Real.sqrt 2 : ℂ))⁻¹

/-- **Each Bell branch carries quantal measure `1/2`.** -/
theorem bellBranch_quantalMeasure (i : Fin 2) :
    quantalMeasure (branchGram bellBranchAmplitude) {i} = 1/2 := by
  simp only [quantalMeasure, branchGram, bellBranchAmplitude, Finset.sum_singleton,
    map_inv₀, Complex.conj_ofReal, inv_sqrt2_sq]
  norm_num

/-- **The history-Hilbert Born weight equals the density-matrix population**: the quantal
measure of each Bell branch coincides with the diagonal of the computed no-signalling
marginal — the decoherence-functional and partial-trace descriptions of the same physics
agree at `1/2`. -/
theorem bellBranch_quantalMeasure_eq_marginal (i : Fin 2) :
    quantalMeasure (branchGram bellBranchAmplitude) {i}
      = (((MState.pure bellPhiPlus).traceRight).m i i).re := by
  rw [bellBranch_quantalMeasure, bellPhiPlus_traceRight_uniform, uniform_m_eq]
  simp [Matrix.diagonal]

/-- **The Bell superposition is maximally coherent**: the double-slit interference term of
the `interference` lemma equals the full sum of the branch weights — constructive
interference is total. -/
theorem bellBranch_maximal_interference :
    2 * ((branchGram bellBranchAmplitude) {0} {1}).re
      = quantalMeasure (branchGram bellBranchAmplitude) {0}
        + quantalMeasure (branchGram bellBranchAmplitude) {1} := by
  rw [bellBranch_quantalMeasure, bellBranch_quantalMeasure]
  simp only [branchGram, bellBranchAmplitude, Finset.sum_singleton, map_inv₀,
    Complex.conj_ofReal, inv_sqrt2_sq]
  norm_num

/-! ## §C — the Tsirelson bound is attained: the variational optimum -/

/-- **The Tsirelson bound is attained** at the optimal `45°` configuration on the real
plane: unit vectors with `chshVector = 2√2` exist — the extremal configuration whose
measurement pairs `chshVector_saturation_orthogonal` proves orthogonal. -/
theorem chshVector_attains_tsirelson :
    ∃ a₀ a₁ b₀ b₁ : EuclideanSpace ℝ (Fin 2),
      ‖a₀‖ = 1 ∧ ‖a₁‖ = 1 ∧ ‖b₀‖ = 1 ∧ ‖b₁‖ = 1 ∧
        chshVector a₀ a₁ b₀ b₁ = 2 * Real.sqrt 2 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 with he0
  set e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1 with he1
  have h00 : inner ℝ e0 e0 = 1 := by
    simp [he0, PiLp.inner_apply, EuclideanSpace.single_apply, Fin.sum_univ_two]
  have h11 : inner ℝ e1 e1 = 1 := by
    simp [he1, PiLp.inner_apply, EuclideanSpace.single_apply, Fin.sum_univ_two]
  have h01 : inner ℝ e0 e1 = 0 := by
    simp [he0, he1, PiLp.inner_apply, EuclideanSpace.single_apply, Fin.sum_univ_two]
  have h10 : inner ℝ e1 e0 = 0 := by
    simp [he0, he1, PiLp.inner_apply, EuclideanSpace.single_apply, Fin.sum_univ_two]
  have hnorm_add : ‖e0 + e1‖ = Real.sqrt 2 := by
    have hsq : ‖e0 + e1‖^2 = 2 := by
      rw [← real_inner_self_eq_norm_sq, real_inner_add_add_self, h00, h11, h01]
      norm_num
    have h := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hnorm_sub : ‖e0 - e1‖ = Real.sqrt 2 := by
    have hsq : ‖e0 - e1‖^2 = 2 := by
      rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self, h00, h11, h01]
      norm_num
    have h := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  refine ⟨e0, e1, (Real.sqrt 2)⁻¹ • (e0 + e1), (Real.sqrt 2)⁻¹ • (e0 - e1),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [he0, EuclideanSpace.norm_single]
    norm_num
  · rw [he1, EuclideanSpace.norm_single]
    norm_num
  · rw [norm_smul, hnorm_add, norm_inv, Real.norm_eq_abs, abs_of_pos hspos]
    field_simp
  · rw [norm_smul, hnorm_sub, norm_inv, Real.norm_eq_abs, abs_of_pos hspos]
    field_simp
  · unfold chshVector
    rw [real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, inner_add_right, inner_add_right,
      inner_sub_right, inner_sub_right, h00, h11, h01, h10]
    field_simp
    linarith [hs2]

/-! ## §D — witness-filtered Bloch geometry and quantum Fisher information -/

/-- **The A/B mode concurrence** of the single-excitation state
`a |10⟩ + b |01⟩`, defined by reusing the repository's pure two-qubit Wootters
concurrence rather than introducing a second entanglement measure. -/
noncomputable def modeConcurrence (a b : ℂ) : ℝ :=
  concurrence 0 b a 0

/-- The occupied two-band state's sublattice polarization `n_z = |a|² - |b|²`. -/
noncomputable def sublatticePolarization (a b : ℂ) : ℝ :=
  Complex.normSq a - Complex.normSq b

/-- **Mode concurrence is the transverse Bloch radius.**  For a normalized occupied
two-band spinor, `C² + n_z² = 1`.  Hence the state is mode-separable at a Bloch pole and
maximally mode-entangled on the equator. -/
lemma modeConcurrence_sq_add_polarization_sq (a b : ℂ)
    (hnorm : Complex.normSq a + Complex.normSq b = 1) :
    modeConcurrence a b ^ 2 + sublatticePolarization a b ^ 2 = 1 := by
  have hab : ‖a * b‖ ^ 2 = Complex.normSq a * Complex.normSq b := by
    rw [norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [modeConcurrence, concurrence, zero_mul, mul_zero, zero_sub, norm_neg]
  rw [show b * a = a * b by ring, sublatticePolarization, mul_pow, hab]
  nlinarith

/-- **The phase-resolved A/B witness alignment** used by the single-orbit filtered
QGT/QFI construction.  A physical witness phase has unit norm. -/
noncomputable def witnessAlignment (phase a b : ℂ) : ℝ :=
  -2 * (phase * a * (starRingEnd ℂ) b).re

/-- **A unit-phase witness cannot exceed the available mode concurrence.**  This is the
pointwise coherence estimate `|η| ≤ C` underlying the filtered QGT and QFI bounds. -/
lemma abs_witnessAlignment_le_modeConcurrence (phase a b : ℂ)
    (hphase : ‖phase‖ = 1) :
    |witnessAlignment phase a b| ≤ modeConcurrence a b := by
  have hre := Complex.abs_re_le_norm (phase * a * (starRingEnd ℂ) b)
  calc
    |witnessAlignment phase a b| = 2 * |(phase * a * (starRingEnd ℂ) b).re| := by
      simp [witnessAlignment]
    _ ≤ 2 * ‖phase * a * (starRingEnd ℂ) b‖ :=
      mul_le_mul_of_nonneg_left hre (by norm_num)
    _ = modeConcurrence a b := by
      simp [modeConcurrence, concurrence, hphase, norm_mul, mul_comm]

/-- The signed witness-filtered quantum Fisher response `η F_Q`. -/
noncomputable def filteredQFI (phase a b : ℂ) (qfi : ℝ) : ℝ :=
  witnessAlignment phase a b * qfi

/-- **Witness-filtered QFI is concurrence-controlled.**  For nonnegative ordinary QFI,
`|F_Q^(S)| ≤ C F_Q`; in particular, a locally mode-separable Bloch state cannot carry
response in the selected coherence channel. -/
lemma abs_filteredQFI_le_concurrence_mul (phase a b : ℂ) (qfi : ℝ)
    (hphase : ‖phase‖ = 1) (hqfi : 0 ≤ qfi) :
    |filteredQFI phase a b qfi| ≤ modeConcurrence a b * qfi := by
  rw [filteredQFI, abs_mul, abs_of_nonneg hqfi]
  exact mul_le_mul_of_nonneg_right
    (abs_witnessAlignment_le_modeConcurrence phase a b hphase) hqfi

end Physlib.QuantumMechanics.ComplexAction.BellBlochHistoryLinks

end
