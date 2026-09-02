/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.States.Mixed.MState
public import Physlib.QuantumMechanics.ComplexAction.CHSHCorrelationBounds

/-!
# Bell states, no-signalling marginals, and no-cloning

The quantum layer of the CHSH arc, authored on the density-matrix carriers this library
already provides (`MState` — positive-semidefinite, trace-one Hermitian matrices — with its
computed partial traces `traceLeft`/`traceRight`, `pure`, `uniform`, and the product
`⊗ᴹ`).  The reference tree (`NoFTLBellBridge.lean`) stated the no-signalling layer against
an abstract partial-trace interface; here the marginals are **computed**:

* `bellPhiPlus`, `bellPhiMinus`, `bellPsiPlus`, `bellPsiMinus` — the four Bell states as
  normalized kets on `Fin 2 × Fin 2`.
* `bellPhiPlus_traceRight_uniform` (and its family) — **no signalling**: each Bell state's
  reduced state on either side is the maximally mixed state.  Bob's local physics is the
  coin flip `I/2` no matter which Bell state was shared —
* `bell_marginals_indistinguishable` — and therefore the four Bell states are locally
  indistinguishable: all reduced states coincide, so no local measurement reveals which
  maximally entangled state (hence no faster-than-light signal) was prepared.
* `uniform_ne_pure`, `bellPhiPlus_not_prod` — **entanglement**: the maximally mixed state
  is not pure, so the Bell state is not a product of pure states — its marginal `I/2`
  contradicts the pure marginal every product state has (`traceRight_prod_eq`).
* `no_cloning_coefficient`, `no_cloning` — **the no-cloning theorem**: a map that
  preserves the bipartite inner product and clones every qubit state would force
  `⟨0|+⟩ = ⟨0|+⟩²`, but `1/√2` is neither `0` nor `1`.

**Honest layering.**  All marginals are finite `Fin 2 × Fin 2` computations on the real
`MState` partial traces — no assumed partial-trace interface.  The unitary-invariance form
of no-signalling (`Tr_A[(U⊗I)ρ(U⊗I)†] = Tr_A ρ`) and the CHSH expectation `S² = 8` of the
Bell state at the optimal angles are the remaining quantum layer, recorded; the
correlation-level Tsirelson bound is `Bell.DeterministicBounds.tsirelson_correlation_bound`.

## References

* J. S. Bell (1964); W. K. Wootters, W. H. Zurek, Nature **299** (1982) 802 (no-cloning).
  Source: reference-tree `NoFTLBellBridge.lean` (own authorship), re-authored on the
  `MState` density-matrix carriers.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling

/-! ## §A — the four Bell states -/

private lemma sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

private lemma normSq_inv_sqrt2 : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1/2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- **The Bell state `Φ⁺ = (|00⟩ + |11⟩)/√2`** as a normalized ket. -/
noncomputable def bellPhiPlus : Ket (Fin 2 × Fin 2) where
  vec p := if p.1 = p.2 then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0
  normalized' := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [one_ne_zero, zero_ne_one, if_false, if_true, norm_zero]
    rw [normSq_inv_sqrt2]
    norm_num

/-- **The Bell state `Φ⁻ = (|00⟩ − |11⟩)/√2`**. -/
noncomputable def bellPhiMinus : Ket (Fin 2 × Fin 2) where
  vec p := if p = (0,0) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
    else if p = (1,1) then -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0
  normalized' := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self, and_false, false_and,
      if_false, if_true, norm_zero, norm_neg]
    rw [normSq_inv_sqrt2]
    norm_num

/-- **The Bell state `Ψ⁺ = (|01⟩ + |10⟩)/√2`**. -/
noncomputable def bellPsiPlus : Ket (Fin 2 × Fin 2) where
  vec p := if p.1 = p.2 then 0 else (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  normalized' := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [one_ne_zero, zero_ne_one, if_false, if_true, norm_zero]
    rw [normSq_inv_sqrt2]
    norm_num

/-- **The singlet `Ψ⁻ = (|01⟩ − |10⟩)/√2`**. -/
noncomputable def bellPsiMinus : Ket (Fin 2 × Fin 2) where
  vec p := if p = (0,1) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
    else if p = (1,0) then -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0
  normalized' := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self, and_false, false_and,
      if_false, if_true, norm_zero, norm_neg]
    rw [normSq_inv_sqrt2]
    norm_num

/-! ## §B — no signalling: every Bell marginal is maximally mixed -/

lemma inv_sqrt2_sq :
    ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma uniform_m_eq :
    (MState.uniform : MState (Fin 2)).m
      = Matrix.diagonal (fun _ : Fin 2 => ((1/2 : ℝ) : ℂ)) := by
  have h : (MState.uniform : MState (Fin 2)).m
      = (HermitianMat.diagonal ℂ (fun x : Fin 2 => (ProbDistribution.uniform x : ℝ))).mat :=
    rfl
  rw [h, HermitianMat.diagonal_mat]
  congr 1

lemma pure_traceRight_m (ψ : Ket (Fin 2 × Fin 2)) :
    ((MState.pure ψ).traceRight).m
      = Matrix.of (fun i j : Fin 2 =>
          ∑ k : Fin 2, ψ.vec (i, k) * (starRingEnd ℂ) (ψ.vec (j, k))) :=
  rfl

lemma pure_traceLeft_m (ψ : Ket (Fin 2 × Fin 2)) :
    ((MState.pure ψ).traceLeft).m
      = Matrix.of (fun i j : Fin 2 =>
          ∑ k : Fin 2, ψ.vec (k, i) * (starRingEnd ℂ) (ψ.vec (k, j))) :=
  rfl

/-- **No signalling for `Φ⁺`**: Alice's reduced state is the maximally mixed state. -/
theorem bellPhiPlus_traceRight_uniform :
    (MState.pure bellPhiPlus).traceRight = MState.uniform := by
  apply MState.ext_m
  rw [pure_traceRight_m, uniform_m_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bellPhiPlus, Matrix.diagonal, Complex.conj_ofReal] <;>
    norm_num [inv_sqrt2_sq]

/-- **No signalling for `Φ⁺`**, Bob's side. -/
theorem bellPhiPlus_traceLeft_uniform :
    (MState.pure bellPhiPlus).traceLeft = MState.uniform := by
  apply MState.ext_m
  rw [pure_traceLeft_m, uniform_m_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bellPhiPlus, Matrix.diagonal, Complex.conj_ofReal] <;>
    norm_num [inv_sqrt2_sq]

/-- **No signalling for the singlet `Ψ⁻`**. -/
theorem bellPsiMinus_traceRight_uniform :
    (MState.pure bellPsiMinus).traceRight = MState.uniform := by
  apply MState.ext_m
  rw [pure_traceRight_m, uniform_m_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bellPsiMinus, Fin.sum_univ_two, Matrix.diagonal, Complex.conj_ofReal] <;>
    norm_num [inv_sqrt2_sq]

/-- **No signalling for `Φ⁻`**. -/
theorem bellPhiMinus_traceRight_uniform :
    (MState.pure bellPhiMinus).traceRight = MState.uniform := by
  apply MState.ext_m
  rw [pure_traceRight_m, uniform_m_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bellPhiMinus, Fin.sum_univ_two, Matrix.diagonal, Complex.conj_ofReal] <;>
    norm_num [inv_sqrt2_sq]

/-- **No signalling for `Ψ⁺`**. -/
theorem bellPsiPlus_traceRight_uniform :
    (MState.pure bellPsiPlus).traceRight = MState.uniform := by
  apply MState.ext_m
  rw [pure_traceRight_m, uniform_m_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bellPsiPlus, Fin.sum_univ_two, Matrix.diagonal, Complex.conj_ofReal] <;>
    norm_num [inv_sqrt2_sq]

/-- **The four Bell states are locally indistinguishable**: their reduced states on
Alice's side all coincide — no local measurement reveals which maximally entangled state
was shared, hence no faster-than-light signal. -/
theorem bell_marginals_indistinguishable :
    (MState.pure bellPhiPlus).traceRight = (MState.pure bellPhiMinus).traceRight ∧
    (MState.pure bellPhiPlus).traceRight = (MState.pure bellPsiPlus).traceRight ∧
    (MState.pure bellPhiPlus).traceRight = (MState.pure bellPsiMinus).traceRight := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bellPhiPlus_traceRight_uniform, bellPhiMinus_traceRight_uniform]
  · rw [bellPhiPlus_traceRight_uniform, bellPsiPlus_traceRight_uniform]
  · rw [bellPhiPlus_traceRight_uniform, bellPsiMinus_traceRight_uniform]

/-! ## §C — entanglement: the Bell state is not a product -/

/-- **The maximally mixed qubit state is not pure**: its off-diagonal vanishes while its
diagonal is `1/2`, which no rank-one projector satisfies. -/
theorem uniform_ne_pure (ψ : Ket (Fin 2)) :
    (MState.uniform : MState (Fin 2)) ≠ MState.pure ψ := by
  intro h
  have hm := congrArg MState.m h
  have hp : (MState.pure ψ).m
      = Matrix.of (fun i j : Fin 2 => ψ.vec i * (starRingEnd ℂ) (ψ.vec j)) := rfl
  rw [uniform_m_eq, hp] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h11 := congrFun (congrFun hm 1) 1
  simp [Matrix.diagonal] at h00 h01 h11
  rcases h01 with h0 | h1
  · rw [h0] at h00
    simp at h00
  · rw [h1] at h11
    simp at h11

/-- **The Bell state is not a product of pure states**: its Alice marginal is maximally
mixed, but every pure product has the pure state itself as marginal
(`traceRight_prod_eq`). -/
theorem bellPhiPlus_not_prod (ψ φ : Ket (Fin 2)) :
    MState.pure bellPhiPlus ≠ (MState.pure ψ) ⊗ᴹ (MState.pure φ) := by
  intro h
  have hmarg := congrArg MState.traceRight h
  rw [bellPhiPlus_traceRight_uniform, MState.traceRight_prod_eq] at hmarg
  exact uniform_ne_pure ψ hmarg

/-! ## §D — the no-cloning theorem -/

/-- **The cloning fixed-point equation collapses**: `α = α²` forces `α ∈ {0, 1}`. -/
theorem no_cloning_coefficient (α : ℂ) (h : α = α ^ 2) : α = 0 ∨ α = 1 := by
  have hfact : α * (1 - α) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfact with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1).symm

/-- **The no-cloning theorem** (abstract qubit form): no map can both preserve the
bipartite inner product and clone every qubit state — cloning `|0⟩` and `|+⟩` would force
`⟨0|+⟩ = ⟨0|+⟩²`, but `⟨0|+⟩ = 1/√2` is neither `0` nor `1`. -/
theorem no_cloning
    (f : (Fin 2 → ℂ) → (Fin 2 → Fin 2 → ℂ))
    (h_isometric : ∀ u v : Fin 2 → ℂ,
      ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (f u i j) * f v i j
        = ∑ i : Fin 2, (starRingEnd ℂ) (u i) * v i)
    (h_clone : ∀ ψ : Fin 2 → ℂ, f ψ = fun i j => ψ i * ψ j) :
    False := by
  set ket0 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0 with hket0
  set ketplus : Fin 2 → ℂ := fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hketplus
  have h_ip : ∑ i : Fin 2, (starRingEnd ℂ) (ket0 i) * ketplus i
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    simp [hket0, hketplus]
  have h_iso := h_isometric ket0 ketplus
  have h_clone_ip : ∑ i : Fin 2, ∑ j : Fin 2,
      (starRingEnd ℂ) (f ket0 i j) * f ketplus i j
        = (∑ i : Fin 2, (starRingEnd ℂ) (ket0 i) * ketplus i) ^ 2 := by
    rw [h_clone ket0, h_clone ketplus]
    simp only [map_mul, Fin.sum_univ_two]
    ring
  rw [h_clone_ip, h_ip] at h_iso
  rcases no_cloning_coefficient _ h_iso.symm with h | h
  · rw [Complex.ofReal_eq_zero, inv_eq_zero] at h
    exact sqrt2_ne_zero h
  · have h' : ((Real.sqrt 2)⁻¹ : ℝ) = 1 := by exact_mod_cast h
    have hs : Real.sqrt 2 = 1 := by
      field_simp at h'
      linarith [h']
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), hs]

end Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling

end
