/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion
public import Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
public import QuantumInfo.States.Mixed.TraceDistance

/-!
# The one-region geometry of the entangled pair

The remaining pillars of the one-region model, each a finite computation on existing
carriers:

* `trDistance_marginals_zero` — the informational distance **between** the two subsystem
  states is zero: the trace distance of the computed Bell marginals vanishes (they are the
  same maximally mixed state).  Together with the entropic radius `λ_C log 2` **across**
  the pair (`ComptonClock.EntropicProperDistance`, Schmidt number `2`), the two notions of
  distance separate cleanly: zero separation between the "ends", positive size of the
  region.
* `graphTransport`, `graphTransport_support`, `bellPhiPlus_eq_graphTransport`,
  `bellPsiPlus_eq_graphTransport_swap` — **one wavefunction**: each Bell state is a single
  one-qubit ket transported to the graph `{(x, σx)}` of a permutation, and its amplitude
  vanishes off the graph — the pair's configuration space collapses onto an identification
  locus.
* `bellMarginal_collision_trace` — the collision entropy datum: `Tr ρ_A² = 1/2`, so the
  Schmidt number `(Tr ρ_A²)⁻¹ = 2` — the `K` whose logarithm sets the region's entropic
  radius `r = λ_C log 2` in `expEntropicDistance_eq_schmidtNumber`.
* `historyInner_branchGram_factorizes`, `historyInner_branchGram_self` — **one ray**: the
  history inner product of the pure-state branch system factors through the single linear
  functional `u ↦ Σ_α u(α)·σ(α)`; every history vector is null-equivalent to its total
  amplitude, so the GNS/history Hilbert space of the pair is one-dimensional.
* `chshVector_attains_envelope_maximal` — the endpoint link: the maximal point `C = 1` of
  the entropic CHSH envelope (`Bell.EntropicEnvelope`) is attained by the explicit
  `45°` configuration of the vector CHSH functional — `C` is the one-region order
  parameter, `C = 1` one region (Tsirelson), `C = 0` two independent regions (classical).

## References

* The Bell arc of this directory; `ComptonClock.EntropicProperDistance` (Schmidt/radius
  dictionary); `QuantumInfo.States.Mixed.TraceDistance`.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
open Physlib.QuantumMechanics.ComplexAction.BellBlochHistoryLinks
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.VectorBanachStoneDistortion
open Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.OneRegionGeometry

/-! ## §A — zero informational distance between the two ends -/

/-- **The two subsystem states are at trace distance zero**: the computed Bell marginals
are the same maximally mixed state, so the informational separation between the pair's two
"ends" vanishes. -/
theorem trDistance_marginals_zero :
    TrDistance ((MState.pure bellPhiPlus).traceLeft)
      ((MState.pure bellPhiPlus).traceRight) = 0 := by
  rw [bellPhiPlus_traceLeft_uniform, bellPhiPlus_traceRight_uniform]
  unfold TrDistance
  simp

/-! ## §B — one wavefunction on the graph of a permutation -/

private lemma normSq_inv_sqrt2' : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1/2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- The uniform one-qubit superposition `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def ketPlus : Ket (Fin 2) where
  vec _ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  normalized' := by
    rw [Fin.sum_univ_two, normSq_inv_sqrt2']
    norm_num

/-- **The graph transport**: a one-qubit ket carried onto the graph `{(x, σx)}` of a
permutation — the bipartite state whose two coordinates are identified by `σ`. -/
noncomputable def graphTransport (σ : Equiv.Perm (Fin 2)) (χ : Ket (Fin 2)) :
    Ket (Fin 2 × Fin 2) where
  vec p := if p.2 = σ p.1 then χ.vec p.1 else 0
  normalized' := by
    have h : ∀ x : Fin 2,
        (∑ y : Fin 2, ‖if y = σ x then χ.vec x else 0‖ ^ 2) = ‖χ.vec x‖ ^ 2 := by
      intro x
      have hy : ∀ y : Fin 2, ‖if y = σ x then χ.vec x else 0‖ ^ 2
          = if y = σ x then ‖χ.vec x‖ ^ 2 else 0 := by
        intro y
        by_cases hc : y = σ x <;> simp [hc]
      simp only [hy]
      rw [Finset.sum_ite_eq' Finset.univ (σ x) (fun _ => ‖χ.vec x‖ ^ 2)]
      simp
    rw [Fintype.sum_prod_type]
    simp only [h]
    exact χ.normalized'

/-- **The pair's amplitude vanishes off the identification locus**: the graph-transported
state is supported on `{(x, σx)}`. -/
theorem graphTransport_support (σ : Equiv.Perm (Fin 2)) (χ : Ket (Fin 2))
    (p : Fin 2 × Fin 2) (h : (graphTransport σ χ).vec p ≠ 0) :
    p.2 = σ p.1 := by
  by_contra hc
  exact h (if_neg hc)

/-- **`Φ⁺` is one wavefunction on the diagonal**: the Bell state is the uniform one-qubit
ket transported to the graph of the identity — the two coordinates are the same point. -/
theorem bellPhiPlus_eq_graphTransport :
    bellPhiPlus = graphTransport (Equiv.refl (Fin 2)) ketPlus := by
  apply Ket.ext
  intro p
  show (if p.1 = p.2 then _ else _) = (if p.2 = p.1 then _ else _)
  exact if_congr eq_comm rfl rfl

/-- **`Ψ⁺` is one wavefunction on the graph of the flip**: the two coordinates are
identified by the transposition. -/
theorem bellPsiPlus_eq_graphTransport_swap :
    bellPsiPlus = graphTransport (Equiv.swap 0 1) ketPlus := by
  apply Ket.ext
  intro p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [bellPsiPlus, graphTransport, ketPlus, Equiv.swap_apply_def, Ket.apply]

/-! ## §C — the Schmidt datum: collision trace `1/2`, Schmidt number `2` -/

/-- **The collision trace of the Bell marginal is `1/2`**: `Tr ρ_A² = 1/2`, so the Schmidt
number is `(Tr ρ_A²)⁻¹ = 2` — the `K` whose logarithm sets the pair-region's entropic
radius `r = λ_C log 2` in the `ComptonClock.EntropicProperDistance` dictionary
(`expEntropicDistance_eq_schmidtNumber`). -/
theorem bellMarginal_collision_trace :
    Matrix.trace (((MState.pure bellPhiPlus).traceRight).m
      * ((MState.pure bellPhiPlus).traceRight).m) = 1/2 := by
  rw [bellPhiPlus_traceRight_uniform, uniform_m_eq, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  rw [Fin.sum_univ_two]
  push_cast
  norm_num

/-! ## §D — one ray: the history Hilbert space of the pair is one-dimensional -/

/-- **The history inner product of the pure branch system factors** through the single
linear functional `u ↦ Σ_α u(α)·σ(α)`: the branch Gram is rank one, so every history
vector is null-equivalent to its total amplitude — the GNS/history Hilbert space is one
ray. -/
theorem historyInner_branchGram_factorizes {n : ℕ} (c : Fin n → ℂ)
    (s : Finset (Finset (Fin n))) (u v : Finset (Fin n) → ℂ) :
    historyInner (branchGram c) s u v
      = (starRingEnd ℂ) (∑ α ∈ s, u α * ∑ i ∈ α, c i)
          * (∑ β ∈ s, v β * ∑ j ∈ β, c j) := by
  unfold historyInner
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  unfold branchGram
  rw [map_mul]
  ring

/-- **The history norm is the total amplitude's modulus**: `⟨u,u⟩_D = |Σ_α u(α)σ(α)|²` —
the one-ray statement in norm form. -/
theorem historyInner_branchGram_self {n : ℕ} (c : Fin n → ℂ)
    (s : Finset (Finset (Fin n))) (u : Finset (Fin n) → ℂ) :
    historyInner (branchGram c) s u u
      = ((Complex.normSq (∑ α ∈ s, u α * ∑ i ∈ α, c i) : ℝ) : ℂ) := by
  rw [historyInner_branchGram_factorizes, ← Complex.normSq_eq_conj_mul_self]

/-! ## §E — the envelope endpoint: `C = 1` is attained -/

/-- **The maximal point of the entropic CHSH envelope is attained**: the explicit `45°`
configuration realizes `chshEnvelope 1` — the coherence parameter `C` is the one-region
order parameter, with `C = 1` one region (Tsirelson) and `C = 0` two independent regions
(the classical bound `chshEnvelope_separable`). -/
theorem chshVector_attains_envelope_maximal :
    ∃ a₀ a₁ b₀ b₁ : EuclideanSpace ℝ (Fin 2),
      ‖a₀‖ = 1 ∧ ‖a₁‖ = 1 ∧ ‖b₀‖ = 1 ∧ ‖b₁‖ = 1 ∧
        chshVector a₀ a₁ b₀ b₁ = chshEnvelope 1 := by
  rw [chshEnvelope_maximal]
  show ∃ a₀ a₁ b₀ b₁ : EuclideanSpace ℝ (Fin 2), _ ∧ _ ∧ _ ∧ _ ∧
    chshVector a₀ a₁ b₀ b₁ = 2 * Real.sqrt 2
  exact chshVector_attains_tsirelson

end Physlib.QuantumMechanics.ComplexAction.Bell.OneRegionGeometry

end
