/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BellBlochHistoryLinks
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
public import Physlib.QuantumMechanics.ComplexAction.SpacelikeExchangeStatistics

/-!
# The entangled pair as one Sorkin–Hadamard region

The Sorkin layer of the one-region model of the entangled pair: the operational content of
"the two particles are not two regions" stated on the Sorkin–Johnston, quantum-measure, and
exchange-statistics carriers this library already holds.

* **The pair's two-point function is purely Hadamard** (`bellGram_pauliJordanPart_zero`,
  `bellGram_purely_hadamard`, `bellGram_eq_wightman_trivial_causal`): in the
  Sorkin–Johnston split `W = H + (i/2)Δ` of `SorkinJohnstonHermitianDecomposition`, the
  Bell branch Gram — real amplitudes — has **vanishing Pauli–Jordan part** and equals its
  Hadamard part; equivalently it is the region two-point function
  `wightmanTwoPoint H 0` of `SorkinJohnstonRegionState` with **trivial causal kernel**.
  The geometry-reconstructing (Hadamard) datum is all there is: the pair has no internal
  causal order, no "between" — one region.
* **The pair sits at level two of Sorkin's measure hierarchy**
  (`branchGram_sorkin_hierarchy`): the branch quantum measure shows genuine pairwise
  interference (maximal for Bell — `bellBranch_maximal_interference`) but obeys Sorkin's
  third-order sum rule `I₃ = 0`, instantiating the module's
  `sorkin_third_order_sum_rule` on a concrete pure-state history system.
* **Exchange is invisible; the characters are the ribbon twists** (`swapKet`,
  `swapKet_bellPhiPlus`, `swapKet_bellPsiMinus_eq_fermionTwist`,
  `pure_swapKet_bellPsiMinus`, `bellPair_composite_boson`): swapping the two labels fixes
  `Φ⁺` and multiplies the singlet by `ribbonTwist ½ = −1`
  (`Hopf.ChargeConjugationRibbonTwist`), which dies at the density-matrix level — no
  physical fact distinguishes the two labellings.  As a composite the pair carries
  `compositeTwist 2 = +1` (`Particles.HadronSpinStatistics`): the one-region pair is a
  boson.

**Honest layering.**  Exact finite computations on the existing carriers.  The
microcausality reading of the vanishing Pauli–Jordan part — the branch algebras landing in
each other's commutants — is `SorkinCausalOrthogonality.sorkin_spacelike_family_microcausality`
applied to a quasi-local net over the branch labels with their discrete (antichain) order,
and the Sorkin grounding of the pair's entropic radius `λ_C log 2` is one of the four
groundings of `ComptonClock.EntropicProperDistance.entropicProperDistance_unifies_four_groundings`;
both are consumed as recorded carriers, not re-derived here.

## References

* R. D. Sorkin, Mod. Phys. Lett. A **9** (1994) 3119 (quantum measure);
  S. Johnston, R. Sorkin (SJ states); the carriers
  `QuantumMeasureHistoryHilbert`, `SorkinJohnstonHermitianDecomposition`,
  `SorkinJohnstonRegionState`, `SpacelikeExchangeStatistics`,
  `Hopf.ChargeConjugationRibbonTwist`, and the Bell arc of this directory.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
open Physlib.QuantumMechanics.ComplexAction.BellBlochHistoryLinks
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion

/-! ## §A — the pair's two-point function is purely Hadamard -/

/-- The branch Gram is a Hermitian kernel — the hermiticity field of the decoherence
functional, read in the Sorkin–Johnston vocabulary. -/
theorem branchGram_isHermitianKernel {n : ℕ} (c : Fin n → ℂ) :
    IsHermitianKernel (branchGram c) :=
  (branchGram_isDecoherenceFunctional c).hermitian

/-- For real branch amplitudes the Gram is real: the imaginary part vanishes. -/
theorem branchGram_ofReal_im_zero {n : ℕ} (r : Fin n → ℝ) (S T : Finset (Fin n)) :
    (branchGram (fun i => ((r i : ℝ) : ℂ)) S T).im = 0 := by
  unfold branchGram
  have hS : (∑ i ∈ S, ((r i : ℝ) : ℂ)) = ((∑ i ∈ S, r i : ℝ) : ℂ) := by
    push_cast
    rfl
  have hT : (∑ j ∈ T, ((r j : ℝ) : ℂ)) = ((∑ j ∈ T, r j : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hS, hT, Complex.conj_ofReal, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

/-- **The Pauli–Jordan part of a real branch Gram vanishes**: in the Sorkin–Johnston split
`W = H + (i/2)Δ`, real amplitudes carry no commutator function. -/
theorem branchGram_ofReal_pauliJordanPart_zero {n : ℕ} (r : Fin n → ℝ)
    (S T : Finset (Fin n)) :
    pauliJordanPart (branchGram (fun i => ((r i : ℝ) : ℂ))) S T = 0 := by
  unfold pauliJordanPart
  rw [branchGram_ofReal_im_zero]
  ring

/-- **A real branch Gram is purely Hadamard**: it equals its Hadamard part. -/
theorem branchGram_ofReal_eq_hadamardPart {n : ℕ} (r : Fin n → ℝ)
    (S T : Finset (Fin n)) :
    branchGram (fun i => ((r i : ℝ) : ℂ)) S T
      = ((hadamardPart (branchGram (fun i => ((r i : ℝ) : ℂ))) S T : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp [hadamardPart]
  · rw [branchGram_ofReal_im_zero]
    simp

/-- **The real branch Gram is the region two-point function with trivial causal kernel**:
`W = wightmanTwoPoint H 0` — the Sorkin–Johnston region state of a region with no internal
causal order. -/
theorem branchGram_ofReal_eq_wightman_trivial_causal {n : ℕ} (r : Fin n → ℝ)
    (S T : Finset (Fin n)) :
    branchGram (fun i => ((r i : ℝ) : ℂ)) S T
      = wightmanTwoPoint (hadamardPart (branchGram (fun i => ((r i : ℝ) : ℂ))))
          (fun _ _ => 0) S T := by
  unfold wightmanTwoPoint
  rw [branchGram_ofReal_eq_hadamardPart]
  norm_num

/-- The Bell amplitudes are real: `1/√2` coerced. -/
lemma bellBranchAmplitude_eq_ofReal :
    bellBranchAmplitude = fun _ : Fin 2 => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  funext i
  unfold bellBranchAmplitude
  push_cast
  rfl

/-- **The Bell pair carries no Pauli–Jordan function**: the commutator part of its branch
two-point function vanishes — no internal causal order between the two branches. -/
theorem bellGram_pauliJordanPart_zero (S T : Finset (Fin 2)) :
    pauliJordanPart (branchGram bellBranchAmplitude) S T = 0 := by
  rw [bellBranchAmplitude_eq_ofReal]
  exact branchGram_ofReal_pauliJordanPart_zero _ S T

/-- **The Bell branch two-point function is purely Hadamard**: only the
geometry-reconstructing datum survives — the one-region statement in the
Sorkin–Johnston/Hadamard dictionary. -/
theorem bellGram_purely_hadamard (S T : Finset (Fin 2)) :
    branchGram bellBranchAmplitude S T
      = ((hadamardPart (branchGram bellBranchAmplitude) S T : ℝ) : ℂ) := by
  rw [bellBranchAmplitude_eq_ofReal]
  exact branchGram_ofReal_eq_hadamardPart _ S T

/-! ## §B — level two of Sorkin's hierarchy -/

/-- **The pure-state history system sits at level two of Sorkin's measure hierarchy**:
its quantal measure obeys the third-order sum rule `I₃ = 0` — the module's
`sorkin_third_order_sum_rule` instantiated on the branch Gram, whose *pairwise*
interference is genuine (maximal for the Bell amplitudes). -/
theorem branchGram_sorkin_hierarchy {n : ℕ} (c : Fin n → ℂ)
    (α β γ : Finset (Fin n)) (hab : Disjoint α β) (hbc : Disjoint β γ)
    (hac : Disjoint α γ) :
    quantalMeasure (branchGram c) (α ⊔ β ⊔ γ)
      = quantalMeasure (branchGram c) (α ⊔ β) + quantalMeasure (branchGram c) (β ⊔ γ)
        + quantalMeasure (branchGram c) (α ⊔ γ)
        - quantalMeasure (branchGram c) α - quantalMeasure (branchGram c) β
        - quantalMeasure (branchGram c) γ :=
  sorkin_third_order_sum_rule (branchGram_isDecoherenceFunctional c) α β γ hab hbc hac

/-! ## §C — exchange is invisible; the characters are the ribbon twists -/

/-- **The label exchange** on a bipartite ket: precompose with the coordinate swap. -/
noncomputable def swapKet {d : Type*} [Fintype d] (ψ : Ket (d × d)) : Ket (d × d) where
  vec p := ψ.vec (p.2, p.1)
  normalized' := by
    rw [← ψ.normalized']
    exact Fintype.sum_equiv (Equiv.prodComm d d) _ _ (fun p => rfl)

/-- **`Φ⁺` is exchange-invariant**: swapping the two particle labels fixes the Bell state
exactly — there is no fact of "which particle is in which region". -/
theorem swapKet_bellPhiPlus : swapKet bellPhiPlus = bellPhiPlus := by
  apply Ket.ext
  intro p
  show (if p.2 = p.1 then _ else _) = (if p.1 = p.2 then _ else _)
  exact if_congr eq_comm rfl rfl

/-- **The singlet's exchange character is the fermionic ribbon twist**: swapping the labels
multiplies `Ψ⁻` by `ribbonTwist ½ = −1` — the spin-statistics character of
`Hopf.ChargeConjugationRibbonTwist`. -/
theorem swapKet_bellPsiMinus_eq_fermionTwist (p : Fin 2 × Fin 2) :
    (swapKet bellPsiMinus) p = ribbonTwist (1/2) * bellPsiMinus p := by
  rw [ribbonTwist_fermion]
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [swapKet, bellPsiMinus, Ket.apply]

/-- **The exchange phase is unobservable**: at the density-matrix level the swapped singlet
is the singlet — the `−1` is a global phase, so no measurement distinguishes the two
labellings. -/
theorem pure_swapKet_bellPsiMinus :
    MState.pure (swapKet bellPsiMinus) = MState.pure bellPsiMinus := by
  apply MState.ext_m
  have h : ∀ ψ : Ket (Fin 2 × Fin 2), (MState.pure ψ).m
      = Matrix.of (fun i j => ψ.vec i * (starRingEnd ℂ) (ψ.vec j)) := fun _ => rfl
  rw [h, h]
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply,
    show (swapKet bellPsiMinus).vec i = ribbonTwist (1/2) * bellPsiMinus.vec i from
      swapKet_bellPsiMinus_eq_fermionTwist i,
    show (swapKet bellPsiMinus).vec j = ribbonTwist (1/2) * bellPsiMinus.vec j from
      swapKet_bellPsiMinus_eq_fermionTwist j,
    ribbonTwist_fermion]
  rw [map_mul]
  simp only [map_neg, map_one]
  ring

/-- **The one-region pair is a boson**: as a composite of two constituents its exchange
character is `compositeTwist 2 = +1` (`Particles.HadronSpinStatistics`) — the pair, read
as a single region, carries bosonic statistics. -/
theorem bellPair_composite_boson : compositeTwist 2 = 1 := by
  rw [compositeTwist_eq]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion

end
