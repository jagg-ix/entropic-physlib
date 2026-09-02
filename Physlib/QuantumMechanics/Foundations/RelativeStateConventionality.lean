/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.SMatrixDensityHerglotz
public import Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics
public import Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse
public import Physlib.QuantumMechanics.Lindblad.LindbladCPTP
public import Physlib.Relativity.Special.SimultaneityConventionShear
public import Physlib.Thermodynamics.Landauer
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import QuantumInfo.States.Ensemble

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.Foundations.RelativeStateConventionality -/

/-!
# Relative-state conventionality: the Everett–Deutsch face of the synchrony shear

Re-evaluates the Ghosal conventionality-of-simultaneity arc
(`Relativity.Special.SimultaneityConventionShear`) through Everett's relative-state
formulation (Rev. Mod. Phys. **29** (1957) 454) and Deutsch's derivations — the same
three mathematical shapes appear on the quantum side, and each is exact:

* `branchWeight_symmetric_uniform` — **Deutsch's symmetry step** (Proc. R. Soc. A
  **455** (1999) 3129, the pivotal move of the decision-theoretic Born derivation): any
  branch-weight assignment invariant under relabeling the branches of an
  equal-amplitude superposition is uniform, `w i = 1/n` (stated for any finite branch
  type);
* `born_aspects_agree` (§D) — **the three routes are three aspects of one weight**: on
  the equal-amplitude branch with orthonormal records, the Deutsch-symmetric weight, the
  decoherence-functional diagonal
  (`MinimalModalOnticDynamics.born_diagonal_eq_historyWeight`) and the entropic history
  weight at entanglement action `log n`
  (`DecoherenceFunctionalSorkinJohnston.historyWeight_born`) are the *same* number —
  not three derivations of Born's rule but one Born weight presented through symmetry,
  through decoherence, and through entropy;
* `traceRight_env_unitary_invariant` — **the quantum synchrony shear**: a unitary
  acting on the traced-out (environment) factor alone relabels Everett's relative
  states without changing the reduced state of the system,
  `Tr_E[(1⊗V)·M·(1⊗V)ᴴ] = Tr_E[M]`.  This is the exact analogue of
  `synchronyShear_fixes_space`: resynchronization relabels time and fixes space;
  an environment unitary relabels the branch decomposition and fixes every
  system observable — in both cases the "relativity" (of simultaneity, of the
  relative state) is descriptive gauge, and the invariant expresses the physics;
* `implicitOrbit_unique_fixedPoint`, `lorentz_orbit_unique` — **self-consistency as a
  contraction fixed point**, the mathematical shape of Deutsch's closed-timelike-curve
  consistency condition `ρ = Tr_A[U(ρ_in ⊗ ρ)U†]` (Phys. Rev. D **44** (1991) 3197):
  the implicit tippe-top orbit `x_s = f(x_s)` (Ghosal Eq. (34)) has a *unique*
  self-consistent solution whenever the iteration bound of Eq. (35) contracts — in
  particular, by `lorentz_iteration_light_bound`, whenever no particle of the top
  is superluminal (`ωR < c`, Eq. (36)).

**Honest layering.**  Deutsch's refinement and continuity steps are formalized
(`rational_born_realized`, `continuous_rational_born_extension`,
`deutsch_born_unequal`): symmetric weights extend from equal amplitudes to arbitrary
kets.  What remains *un*formalized is the decision-theoretic layer proper — the
rationality axioms and utility representation that justify reading the weights as
betting probabilities — and Deutsch's CTC theorem (existence of a consistent state for
*every* channel, which needs Schauder rather than Banach); the contraction case is its
exact kernel.
Everett's branch/record machinery on Hilbert spaces is the concurrent module
`Foundations.EverettHeisenbergRelativeStates` (uncommitted at the time of writing —
the weld of `traceRight_env_unitary_invariant` to its `branchBornWeight` is held until
it lands).

## References

* H. Everett III, *"Relative state" formulation of quantum mechanics*, Rev. Mod. Phys.
  **29** (1957) 454.
* D. Deutsch, *Quantum theory of probability and decisions*, Proc. R. Soc. Lond. A
  **455** (1999) 3129 (the symmetry step); *Quantum mechanics near closed timelike
  lines*, Phys. Rev. D **44** (1991) 3197 (self-consistency as fixed point).
* K. A. Kirkpatrick, *The Schrödinger--HJW theorem*, Found. Phys. Lett. **19**
  (2006) 95--102, arXiv:quant-ph/0305068v3.
* S. K. Ghosal et al., Found. Phys. Lett. **16** (2003) 549 (Eqs. (34)–(36)).
* Carrier reuse: `Foundations.MinimalModalOnticDynamics` (QuantumInfo `traceRight`,
  Kronecker toolkit), `Relativity.Special.SimultaneityConventionShear`
  (`implicitOrbit`, `implicitOrbit_hasDerivAt`, `implicitOrbit_deriv_bound`,
  `lorentz_iteration_light_bound`, `synchronyShear_fixes_space`).
-/

set_option autoImplicit false

open Physlib.Relativity.Special.SimultaneityConventionShear
open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.Foundations.RelativeStateConventionality

/-! ## §A — Deutsch's symmetry step: branch relabeling pins uniform weights -/

/-- **Equal amplitudes force equal weights** (Deutsch 1999): a weight assignment on `n`
branches that is invariant under every relabeling of the branches, and sums to one, is
the uniform distribution — the pivotal step of the decision-theoretic Born derivation,
with the "relabeling" playing exactly the role of the synchrony shear: pure descriptive
gauge. -/
theorem branchWeight_symmetric_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (w : α → ℝ)
    (hsym : ∀ σ : Equiv.Perm α, ∀ i, w (σ i) = w i)
    (hsum : ∑ i, w i = 1) (i : α) : w i = 1 / (Fintype.card α) := by
  have hconst : ∀ j, w j = w i := by
    intro j
    have h := hsym (Equiv.swap i j) j
    rw [Equiv.swap_apply_right] at h
    exact h.symm
  have hcard : 0 < Fintype.card α := Fintype.card_pos
  have hn' : ((Fintype.card α : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hcard.ne'
  have hkey : (Fintype.card α : ℝ) * w i = 1 := by
    calc (Fintype.card α : ℝ) * w i = ∑ _j : α, w i := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ j, w j := Finset.sum_congr rfl fun j _ => (hconst j).symm
      _ = 1 := hsum
  field_simp
  linarith [hkey]

/-- Amplitude helper: the Born weight of the amplitude `√x` is `x`. -/
lemma normSq_sqrt_amplitude (x : ℝ) (hx : 0 ≤ x) :
    Complex.normSq ((Real.sqrt x : ℝ) : ℂ) = x := by
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt hx]

/-- **Deutsch's refinement move — the unequal-amplitude extension**: coarse-grain the
`n` symmetric branches by any map `π`; the weight of a coarse branch is its fiber
fraction `k/n`, which *is* the Born weight of the amplitude `√(k/n)`.  This is the
aspects theorem's "correction ledger" off the uniform stratum, the exact analogue of
`zahar_eq_alt_plus_gamma_correction`: unequal weights are equal weights, refined. -/
theorem branchWeight_refinement {n : ℕ} {α : Type*} [DecidableEq α] (hn : 0 < n)
    (w : Fin n → ℝ)
    (hsym : ∀ σ : Equiv.Perm (Fin n), ∀ i, w (σ i) = w i)
    (hsum : ∑ i, w i = 1) (π : Fin n → α) (a : α) :
    ∑ i ∈ Finset.univ.filter (fun i => π i = a), w i =
      Complex.normSq ((Real.sqrt
        (((Finset.univ.filter (fun i => π i = a)).card : ℝ) / n) : ℝ) : ℂ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have huni : ∀ i, w i = 1 / n := by
    intro i
    rw [branchWeight_symmetric_uniform w hsym hsum i, Fintype.card_fin]
  rw [normSq_sqrt_amplitude _ (by positivity)]
  rw [Finset.sum_congr rfl fun i _ => huni i, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The explicit fiber: the first `k` of `n` branches, with cardinality `k`. -/
lemma card_fiber_lt (k n : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k := by
  have himg : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)
      = Finset.map (Fin.castLEEmb hk) Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hj
      exact ⟨⟨(j : ℕ), hj⟩, by simp [Fin.castLEEmb, Fin.castLE]⟩
    · rintro ⟨i, rfl⟩
      simp [Fin.castLEEmb, Fin.castLE, i.isLt]
  rw [himg, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- **Every rational weight is realized by a refinement**: for `k ≤ n` there is an
explicit coarse-graining of the `n` symmetric branches whose coarse branch has
exactly the weight `k/n` — Deutsch's refinement is constructive, not existential. -/
theorem rational_born_realized (k n : ℕ) (hk : k ≤ n) :
    ∃ π : Fin n → Bool,
      ∑ _i ∈ Finset.univ.filter (fun i => π i = true), (1 : ℝ) / n = (k : ℝ) / n := by
  refine ⟨fun i => decide ((i : ℕ) < k), ?_⟩
  have hfilter : (Finset.univ.filter (fun i : Fin n => decide ((i : ℕ) < k) = true))
      = Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) := by
    simp
  rw [hfilter, Finset.sum_const, card_fiber_lt k n hk, nsmul_eq_mul]
  ring

/-- Refinement values transfer to all rationals of `[0,1]`: a weight functional
agreeing with `k/n ↦ k/n` agrees with the identity on every rational in `[0,1]`. -/
lemma rational_agreement_of_refinement (f : ℝ → ℝ)
    (hrat : ∀ (k n : ℕ), 0 < n → k ≤ n → f ((k : ℝ) / n) = (k : ℝ) / n)
    (q : ℚ) (hq0 : (0 : ℝ) ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ 1) : f (q : ℝ) = (q : ℝ) := by
  have hden : 0 < q.den := q.pos
  have hnum0 : 0 ≤ q.num := by
    by_contra hneg
    push Not at hneg
    have hqneg : (q : ℝ) < 0 := by
      rw [Rat.cast_def]
      apply div_neg_of_neg_of_pos
      · exact_mod_cast hneg
      · exact_mod_cast hden
    linarith
  have hcast : (q : ℝ) = ((q.num.toNat : ℕ) : ℝ) / ((q.den : ℕ) : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hnum0).symm
  have hle : q.num.toNat ≤ q.den := by
    have hden' : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hden
    have hnumLeDen := (div_le_one hden').mp (by rw [← hcast]; exact hq1)
    exact_mod_cast hnumLeDen
  rw [hcast]
  exact hrat q.num.toNat q.den hden hle

/-- **The continuity extension** (the last step of Deutsch's derivation): a continuous
weight functional of the squared amplitude that matches the refinement values on all
rationals is the identity on `[0,1]` — via the clamp trick and the density of `ℚ`. -/
theorem continuous_rational_born_extension (f : ℝ → ℝ) (hf : Continuous f)
    (hrat : ∀ (k n : ℕ), 0 < n → k ≤ n → f ((k : ℝ) / n) = (k : ℝ) / n)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : f x = x := by
  have hQ : ∀ q : ℚ, (0 : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ 1 → f (q : ℝ) = (q : ℝ) :=
    fun q => rational_agreement_of_refinement f hrat q
  have hclampC : Continuous (fun y : ℝ => min 1 (max 0 y)) := by fun_prop
  have hgC : Continuous (fun y : ℝ => f (min 1 (max 0 y))) := hf.comp hclampC
  have hext : (fun y : ℝ => f (min 1 (max 0 y))) = fun y : ℝ => min 1 (max 0 y) := by
    apply Continuous.ext_on Rat.denseRange_cast hgC hclampC
    rintro y ⟨q, rfl⟩
    show f (min 1 (max 0 (q : ℝ))) = min 1 (max 0 (q : ℝ))
    have hmem0 : (0 : ℝ) ≤ min 1 (max 0 (q : ℝ)) := le_min zero_le_one (le_max_left 0 _)
    have hmem1 : min 1 (max 0 (q : ℝ)) ≤ 1 := min_le_left _ _
    have hratval : min 1 (max 0 ((q : ℝ))) = ((min 1 (max 0 q) : ℚ) : ℝ) := by
      push_cast
      rfl
    rw [hratval]
    exact hQ (min 1 (max 0 q)) (by rw [← hratval]; exact hmem0)
      (by rw [← hratval]; exact hmem1)
  have hx : min 1 (max 0 x) = x := by
    rw [max_eq_right hx0, min_eq_right hx1]
  calc f x = f (min 1 (max 0 x)) := by rw [hx]
    _ = min 1 (max 0 x) := congrFun hext x
    _ = x := hx

open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics in
/-- A ket's squared amplitude never exceeds one. -/
lemma ket_normSq_le_one {dS : Type*} [Fintype dS] (Ψ : Ket dS) (m : dS) :
    Complex.normSq (Ψ m) ≤ 1 := by
  have hsum := Ψ.normalized
  have hle : Complex.normSq (Ψ m) ≤ ∑ x, Complex.normSq (Ψ x) :=
    Finset.single_le_sum (fun x _ => Complex.normSq_nonneg (Ψ x)) (Finset.mem_univ m)
  linarith

open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics in
/-- **Deutsch's unequal-amplitude Born rule** (Proc. R. Soc. A 455 (1999) 3129, the
refinement + continuity steps): a branch-weight functional of the squared amplitude
that is continuous and matches the symmetric-refinement values `k/n ↦ k/n`
(`rational_born_realized`) on all rationals assigns to *every* branch of *any* ket
exactly its Born weight — `f(|Ψ_m|²) = |Ψ_m|²`.  With
`branchWeight_symmetric_uniform` (symmetry ⟹ the rational values) this completes the
derivation from equal amplitudes to arbitrary ones. -/
theorem deutsch_born_unequal {dS : Type*} [Fintype dS] (Ψ : Ket dS) (f : ℝ → ℝ)
    (hf : Continuous f)
    (hrat : ∀ (k n : ℕ), 0 < n → k ≤ n → f ((k : ℝ) / n) = (k : ℝ) / n)
    (m : dS) : f (Complex.normSq (Ψ m)) = Complex.normSq (Ψ m) :=
  continuous_rational_born_extension f hf hrat
    (Complex.normSq_nonneg (Ψ m)) (ket_normSq_le_one Ψ m)

/-! ## §B — the quantum synchrony shear: environment unitaries fix the reduced state -/

open scoped Kronecker in
/-- Entry helper: `(1 ⊗ V)·M` acts on the environment index only. -/
lemma kron_one_mul_apply {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁]
    (V : Matrix d₂ d₂ ℂ) (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (i : d₁) (k : d₂)
    (q : d₁ × d₂) :
    (((1 : Matrix d₁ d₁ ℂ) ⊗ₖ V) * M) (i, k) q = ∑ p₂, V k p₂ * M (i, p₂) q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_comm]
  simp

open scoped Kronecker in
/-- Entry helper: `M·(1 ⊗ V)ᴴ` acts on the environment index only. -/
lemma mul_kron_one_conj_apply {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁]
    (V : Matrix d₂ d₂ ℂ) (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (j : d₁) (k : d₂)
    (q : d₁ × d₂) :
    (M * ((1 : Matrix d₁ d₁ ℂ) ⊗ₖ V)ᴴ) q (j, k) = ∑ q₂, M q (j, q₂) * star (V k q₂) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    apply_ite (star : ℂ → ℂ), star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, one_mul]
  rw [Finset.sum_comm]
  simp

open scoped Kronecker in
/-- **Relative-state relabeling is gauge** (Everett): conjugating by `1 ⊗ V` — a
unitary on the traced-out factor alone — leaves the partial trace untouched:
`Tr_E[(1⊗V)·M·(1⊗V)ᴴ] = Tr_E[M]`.  Relabeling the environment's relative states
changes no system observable, exactly as the synchrony shear
(`synchronyShear_fixes_space`) relabels distant time while fixing space: the
"relativity of the relative state" is conventionality, and the reduced state is its
invariant. -/
theorem traceRight_env_unitary_invariant {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂]
    (V : Matrix d₂ d₂ ℂ) (hV : Vᴴ * V = 1) (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (((1 : Matrix d₁ d₁ ℂ) ⊗ₖ V) * M * ((1 : Matrix d₁ d₁ ℂ) ⊗ₖ V)ᴴ).traceRight
      = M.traceRight := by
  have key : ∀ p₂ q₂ : d₂,
      (∑ k, V k p₂ * star (V k q₂)) = if p₂ = q₂ then 1 else 0 := by
    intro p₂ q₂
    have h := congrFun (congrFun hV p₂) q₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    calc (∑ k, V k p₂ * star (V k q₂))
        = star (∑ k, star (V k p₂) * V k q₂) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [star_mul, star_star]
          ring
      _ = star (if p₂ = q₂ then (1 : ℂ) else 0) := by rw [h]
      _ = if p₂ = q₂ then 1 else 0 := by split_ifs <;> simp
  ext i j
  simp only [Matrix.traceRight, Matrix.of_apply]
  calc (∑ k, (((1 : Matrix d₁ d₁ ℂ) ⊗ₖ V) * M * ((1 : Matrix d₁ d₁ ℂ) ⊗ₖ V)ᴴ) (i, k) (j, k))
      = ∑ k, ∑ p₂, ∑ q₂, V k p₂ * (M (i, p₂) (j, q₂) * star (V k q₂)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc, kron_one_mul_apply]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        rw [mul_kron_one_conj_apply, Finset.mul_sum]
    _ = ∑ p₂, ∑ q₂, M (i, p₂) (j, q₂) * ∑ k, V k p₂ * star (V k q₂) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q₂ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ p₂, ∑ q₂, M (i, p₂) (j, q₂) * if p₂ = q₂ then 1 else 0 := by
        simp_rw [key]
    _ = ∑ p₂, M (i, p₂) (j, p₂) := by simp

/-! ## §C — the finite Schrödinger--HJW ensemble/ancilla theorem

Kirkpatrick's formulation of the Schrödinger--HJW theorem starts from a pure-state ensemble
`{pₐ, |ψₐ⟩}` of a density matrix and correlates its labels with orthogonal ancilla records.  The
following construction uses the repository's actual `PEnsemble`, `Ket`, `MState.pure`,
`MState.traceRight`, and `Ensemble.mix` carriers:

`|Ψₑ⟩ = ∑ₐ √pₐ |ψₐ⟩ ⊗ |a⟩`.

Thus it proves the finite exact core of parts (a), (b), and (d): every ensemble has an explicit
orthogonal-record purification; reading its ancilla basis recovers exactly that ensemble; and any
unitary relabeling of the ancilla leaves the system density matrix fixed.  The converse orbit
statement--that every two purifications of the same marginal are related by an ancilla unitary--is
the remaining uniqueness-of-purification direction and is not silently assumed here.
-/

private lemma norm_sq_sqrt_prob (p : Prob) :
    ‖((Real.sqrt (p : ℝ) : ℝ) : ℂ)‖ ^ 2 = (p : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt p.2.1]

/-- The Schrödinger--HJW ancilla ket associated with a finite pure-state ensemble:
`Ψₑ(i,a) = √pₐ ψₐ(i)`.  The ancilla basis is the ensemble's own finite label type, so its records
are orthogonal by construction rather than introduced through an abstract partial-trace axiom. -/
noncomputable def ensemblePurification {d α : Type*} [Fintype d] [Fintype α]
    (e : PEnsemble d α) : Ket (d × α) where
  vec x := ((Real.sqrt (e.distr x.2 : ℝ) : ℝ) : ℂ) * e.states x.2 x.1
  normalized' := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      ∑ a, ∑ i, ‖((Real.sqrt (e.distr a : ℝ) : ℝ) : ℂ) * e.states a i‖ ^ 2 =
          ∑ a, (e.distr a : ℝ) * ∑ i, ‖e.states a i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, mul_pow, norm_sq_sqrt_prob]
      _ = ∑ a, (e.distr a : ℝ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        have hnorm : ∑ i, ‖e.states a i‖ ^ 2 = 1 := by
          simpa only [Ket.apply] using (e.states a).normalized'
        rw [hnorm, mul_one]
      _ = 1 := e.distr.normalized

/-- **Schrödinger--HJW part (a), constructive finite form.**  Tracing out the orthogonal
ancilla labels of `ensemblePurification e` returns exactly the mixture represented by `e`:
`Tr_A |Ψₑ⟩⟨Ψₑ| = Σₐ pₐ |ψₐ⟩⟨ψₐ|`. -/
theorem ensemblePurification_traceRight {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] [DecidableEq α] (e : PEnsemble d α) :
    (MState.pure (ensemblePurification e)).traceRight =
      Ensemble.mix (e : MEnsemble d α) := by
  apply MState.ext_m
  rw [Ensemble.mix_of]
  ext i j
  simp only [MState.traceRight, HermitianMat.traceRight, Matrix.traceRight,
    MState.pure_apply, ensemblePurification, Ket.apply, Matrix.sum_apply, Matrix.smul_apply,
    MState.mat_M, map_mul, Complex.real_smul,
    Ensemble.distr_toMEnsemble]
  refine Finset.sum_congr rfl fun a _ => ?_
  change
    ((Real.sqrt (e.distr a : ℝ) : ℂ) * e.states a i) *
        ((starRingEnd ℂ) (Real.sqrt (e.distr a : ℝ) : ℂ) *
          (starRingEnd ℂ) (e.states a j)) =
      ((e.distr a : ℝ) : ℂ) * (e.states a i * (starRingEnd ℂ) (e.states a j))
  rw [starRingEnd_apply, RCLike.star_def, Complex.conj_ofReal]
  have hsqrt : ((Real.sqrt (e.distr a : ℝ) : ℂ) *
      (Real.sqrt (e.distr a : ℝ) : ℂ)) = (e.distr a : ℝ) := by
    exact_mod_cast Real.mul_self_sqrt (e.distr a).2.1
  rw [← hsqrt]
  ring

/-- **Schrödinger--HJW part (b), ancilla readout.**  The diagonal probability of record `a`
in the ancilla marginal is exactly the ensemble probability `pₐ`.  This is the operational
content of reading the orthogonal ancilla basis of `ensemblePurification e`: it recovers the
original ensemble distribution, without a collapse or measurement postulate. -/
theorem ensemblePurification_traceLeft_diag {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] [DecidableEq α] (e : PEnsemble d α) (a : α) :
    ((MState.pure (ensemblePurification e)).traceLeft).m a a = (e.distr a : ℝ) := by
  change (MState.pure (ensemblePurification e)).m.traceLeft a a = (e.distr a : ℝ)
  simp only [Matrix.traceLeft, Matrix.of_apply, MState.pure_apply,
    ensemblePurification, Ket.apply, map_mul]
  calc
    ∑ i, (Real.sqrt (e.distr a : ℝ) : ℂ) * e.states a i *
        ((starRingEnd ℂ) (Real.sqrt (e.distr a : ℝ) : ℂ) *
          (starRingEnd ℂ) (e.states a i)) =
        ((e.distr a : ℝ) : ℂ) * ∑ i, e.states a i * (starRingEnd ℂ) (e.states a i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [starRingEnd_apply, RCLike.star_def, Complex.conj_ofReal]
      have hsqrt : ((Real.sqrt (e.distr a : ℝ) : ℂ) *
          (Real.sqrt (e.distr a : ℝ) : ℂ)) = (e.distr a : ℝ) := by
        exact_mod_cast Real.mul_self_sqrt (e.distr a).2.1
      rw [← hsqrt]
      ring
    _ = (e.distr a : ℝ) := by
      have hnorm : ∑ i, e.states a i * (starRingEnd ℂ) (e.states a i) = 1 := by
        calc
          ∑ i, e.states a i * (starRingEnd ℂ) (e.states a i) =
              ((∑ i, Complex.normSq (e.states a i) : ℝ) : ℂ) := by
                push_cast
                exact Finset.sum_congr rfl fun i _ => Complex.mul_conj _
          _ = 1 := by exact_mod_cast (e.states a).normalized
      rw [hnorm, mul_one]

open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

/-- **A positive HJW coefficient is the complex-action history amplitude itself.**  At
zero real action and unit `ℏ`, the Sorkin--Nagao--Nielsen history weight with entropic
action `-log p` is exactly `√p`, not merely a complex number whose norm-square is `p`.
The nonzero hypothesis is precisely what makes `log p` invertible. -/
theorem historyWeight_zero_negLog_one (p : Prob) (hp : p ≠ 0) :
    historyWeight 0 (-Real.log (p : ℝ)) 1 =
      ((Real.sqrt (p : ℝ) : ℝ) : ℂ) := by
  have hp' : 0 < (p : ℝ) := Prob.zero_lt_coe hp
  unfold historyWeight complexActionPathIntegralWeight
  rw [show (1 / 2 * -Real.log (p : ℝ)) / 1 = -Real.log (p : ℝ) / 2 by ring]
  norm_num
  rw [show -(-((Real.log (p : ℝ) : ℝ) : ℂ) / 2) =
      (((Real.log (p : ℝ) / 2 : ℝ) : ℂ)) by push_cast; ring]
  change Complex.exp (((Real.log (p : ℝ) / 2 : ℝ) : ℂ)) =
    ((Real.sqrt (p : ℝ) : ℝ) : ℂ)
  rw [← Complex.ofReal_exp, Real.exp_half, Real.exp_log hp']

/-- **The full HJW purification is a complex-action branch superposition.**  Every
nonzero record coefficient `√pₐ` in the explicit purification is exactly the existing
history amplitude at entropic action `-log pₐ`; the system ket supplies the corresponding
relative state. -/
theorem ensemblePurification_eq_historyWeight_smul {d α : Type*} [Fintype d] [Fintype α]
    (e : PEnsemble d α) (i : d) (a : α) (ha : e.distr a ≠ 0) :
    ensemblePurification e (i, a) =
      historyWeight 0 (-Real.log (e.distr a : ℝ)) 1 * e.states a i := by
  change ((Real.sqrt (e.distr a : ℝ) : ℝ) : ℂ) * e.states a i = _
  rw [historyWeight_zero_negLog_one (e.distr a) ha]

/-- **Every HJW record block is the Sorkin decoherence-functional coherence.**  The
`(a,b)` block of the joint pure density matrix factors into the rank-one complex-action
decoherence kernel of the two branch amplitudes and the cross-relative-state matrix
element.  The diagonal recovers Born probability; the off-diagonal retains the phase
coherence that the earlier probability-only bridge did not expose. -/
theorem ensemblePurification_jointBlock_eq_decoherenceFunctional
    {d α : Type*} [Fintype d] [DecidableEq d] [Fintype α] [DecidableEq α]
    (e : PEnsemble d α) (i j : d) (a b : α)
    (ha : e.distr a ≠ 0) (hb : e.distr b ≠ 0) :
    (MState.pure (ensemblePurification e)).m (i, a) (j, b) =
      decoherenceFunctional
          (fun x => historyWeight 0 (-Real.log (e.distr x : ℝ)) 1) a b *
        (e.states a i * (starRingEnd ℂ) (e.states b j)) := by
  rw [MState.pure_apply, decoherenceFunctional_apply,
    ensemblePurification_eq_historyWeight_smul e i a ha,
    ensemblePurification_eq_historyWeight_smul e j b hb]
  simp only [map_mul]
  ring

open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
/-- **HJW branch probability is a complex-action Born weight.**  For every nonzero ensemble
branch, the ancilla readout probability is the squared norm of the Nagao--Nielsen/Sorkin
history weight with entropic action `S_ent(a) = -log pₐ`.  Hence HJW steering labels and the
repository's imaginary-action damping use the same probability, not merely analogous ones. -/
theorem ensemblePurification_diag_eq_historyWeight {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] [DecidableEq α] (e : PEnsemble d α) (a : α) (ha : e.distr a ≠ 0)
    (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ((MState.pure (ensemblePurification e)).traceLeft).m a a =
      (Complex.normSq
        (historyWeight S_R (-Real.log (e.distr a : ℝ)) ℏ) : ℂ) := by
  rw [ensemblePurification_traceLeft_diag, historyWeight_born S_R _ ℏ hℏ, neg_neg]
  have hp : 0 < (e.distr a : ℝ) := Prob.zero_lt_coe ha
  rw [Real.exp_log hp]

/-- Two finite pure ensembles represent the same density matrix exactly when their explicit HJW
ancilla purifications have the same system marginal.  This is the ensemble-classification fiber
before proving the converse unitary-orbit parameterization. -/
theorem ensemblePurification_sameMarginal_iff {d α β : Type*}
    [Fintype d] [DecidableEq d] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : PEnsemble d α) (f : PEnsemble d β) :
    (MState.pure (ensemblePurification e)).traceRight =
        (MState.pure (ensemblePurification f)).traceRight ↔
      Ensemble.mix (e : MEnsemble d α) = Ensemble.mix (f : MEnsemble d β) := by
  rw [ensemblePurification_traceRight, ensemblePurification_traceRight]

/-- Every finite mixed state has both its existing spectral ensemble and an explicit HJW ancilla
purification of that ensemble.  This reuses `Ensemble.spectral_ensemble_mix`; no second spectral
decomposition or purification implementation is introduced. -/
theorem schrodingerHJW_exists_ensemble_and_ancilla {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) :
    ∃ (e : PEnsemble d d) (Ψ : Ket (d × d)),
      Ensemble.mix (e : MEnsemble d d) = ρ ∧ (MState.pure Ψ).traceRight = ρ := by
  refine ⟨Ensemble.spectral_ensemble ρ,
    ensemblePurification (Ensemble.spectral_ensemble ρ), Ensemble.spectral_ensemble_mix, ?_⟩
  rw [ensemblePurification_traceRight, Ensemble.spectral_ensemble_mix]

open scoped Kronecker in
/-- **Schrödinger--HJW part (d), exact invariant direction.**  Acting unitarily only on the
ancilla of the explicit ensemble purification preserves the reduced density matrix, hence
preserves the represented ensemble state. -/
theorem schrodingerHJW_ancilla_unitary_preserves_mix {d α : Type*}
    [Fintype d] [DecidableEq d] [Fintype α] [DecidableEq α]
    (e : PEnsemble d α) (V : Matrix α α ℂ) (hV : Vᴴ * V = 1) :
    (((1 : Matrix d d ℂ) ⊗ₖ V) * (MState.pure (ensemblePurification e)).m *
        ((1 : Matrix d d ℂ) ⊗ₖ V)ᴴ).traceRight =
      (Ensemble.mix (e : MEnsemble d α)).m := by
  rw [traceRight_env_unitary_invariant V hV,
    show (MState.pure (ensemblePurification e)).m.traceRight =
      ((MState.pure (ensemblePurification e)).traceRight).m from rfl,
    ensemblePurification_traceRight]

/-! ## §D — the three routes are three aspects of one weight

`branchWeight_symmetric_uniform` (symmetry), `born_diagonal_eq_historyWeight`
(decoherence diagonal) and `historyWeight_born` (entropic) are not three derivations of
three numbers: on the equal-amplitude branch they are three presentations of the *same*
weight.  The entanglement action of a uniform amplitude is `−log(1/n) = log n`, so the
entropic weight is `e^{−log n} = 1/n` — the symmetric weight — and the decoherence
diagonal has the identical value. -/

open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics in
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
open ComplexConjugate in
/-- **One weight, three aspects**: for an equal-amplitude branch structure with
orthonormal records, (i) the decoherence-functional diagonal of outcome `m` *is* the
Deutsch-symmetric weight `w m`, and (ii) that weight *is* the entropic history weight at
entanglement action `log n` — the symmetry route, the decoherence route and the entropic
route of the repository are one Born weight seen three ways. -/
theorem born_aspects_agree {dS dE : Type*} [Fintype dS] [Fintype dE]
    [DecidableEq dS] [DecidableEq dE] [Nonempty dS]
    (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0)
    (huni : ∀ m', Complex.normSq (Ψ m') = ((Fintype.card dS : ℝ))⁻¹)
    (w : dS → ℝ)
    (hsym : ∀ σ : Equiv.Perm dS, ∀ i, w (σ i) = w i) (hsum : ∑ i, w i = 1)
    (m : dS) (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m = (w m : ℂ)
    ∧ w m = Complex.normSq (historyWeight S_R (Real.log (Fintype.card dS)) ℏ) := by
  have hcard : 0 < Fintype.card dS := Fintype.card_pos
  have hcardR : (0 : ℝ) < (Fintype.card dS : ℝ) := by exact_mod_cast hcard
  have hw : w m = ((Fintype.card dS : ℝ))⁻¹ := by
    rw [branchWeight_symmetric_uniform w hsym hsum m, one_div]
  have hm : Ψ m ≠ 0 := by
    intro h0
    have h := huni m
    rw [h0] at h
    simp only [map_zero] at h
    exact (inv_pos.mpr hcardR).ne' h.symm
  constructor
  · rw [born_diagonal_eq_historyWeight Ψ χ horth m hm S_R ℏ hℏ,
      historyWeight_born _ _ _ hℏ, huni m, Real.log_inv, neg_neg,
      Real.exp_neg, Real.exp_log hcardR, hw]
  · rw [hw, historyWeight_born _ _ _ hℏ, Real.exp_neg, Real.exp_log hcardR]

/-! ## §C — self-consistency as a contraction fixed point (Deutsch's CTC shape) -/

/-- **The implicit orbit has a unique self-consistent solution when it contracts**: if
the iteration bound `|A|·|ω|·|g| < 1` of Ghosal Eq. (35) holds, the transcendental
equation `x_s = f(x_s)` (Eq. (34)) has exactly one solution — the Banach fixed point,
the same self-consistency shape as Deutsch's closed-timelike-curve condition
`ρ = Φ(ρ)`. -/
theorem implicitOrbit_unique_fixedPoint (A ω φ g : ℝ)
    (hK : |A| * (|ω| * |g|) < 1) :
    ∃! xs : ℝ, implicitOrbit A ω φ g xs = xs := by
  set K : NNReal := (|A| * (|ω| * |g|)).toNNReal with hKdef
  have hcoe : (K : ℝ) = |A| * (|ω| * |g|) := by
    rw [hKdef]
    exact Real.coe_toNNReal _ (by positivity)
  have hlip : LipschitzWith K (implicitOrbit A ω φ g) := by
    rw [← lipschitzOnWith_univ]
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le convex_univ
      (f' := fun xs => A * (-Real.sin (ω * (φ + g * xs)) * (ω * g)))
      (fun x _ => (implicitOrbit_hasDerivAt A ω φ g x).hasDerivWithinAt)
    intro x _
    rw [← NNReal.coe_le_coe, coe_nnnorm, hcoe, Real.norm_eq_abs]
    exact implicitOrbit_deriv_bound A ω φ g x
  have hcontract : ContractingWith K (implicitOrbit A ω φ g) := by
    constructor
    · rw [← NNReal.coe_lt_coe, hcoe, NNReal.coe_one]
      exact hK
    · exact hlip
  refine ⟨hcontract.fixedPoint, hcontract.fixedPoint_isFixedPt, fun y hy => ?_⟩
  exact hcontract.fixedPoint_unique hy

/-- **The tippe top has a unique orbit below light speed**: combining the contraction
with `lorentz_iteration_light_bound`, the Lorentz-frame implicit orbit is uniquely
determined at every rocket speed `β < 1` as soon as `ωR < c` — Ghosal's Eq. (36)
upgraded from an iteration criterion to existence and uniqueness. -/
theorem lorentz_orbit_unique (β c γ R ω φ : ℝ)
    (hc : 0 < c) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hR : 0 ≤ R) (hω : 0 ≤ ω)
    (hγ0 : γ ≠ 0) (hlight : ω * R < c) :
    ∃! xs : ℝ, implicitOrbit (R / γ) ω φ (-(γ * β / c)) xs = xs :=
  implicitOrbit_unique_fixedPoint (R / γ) ω φ (-(γ * β / c))
    (lorentz_iteration_light_bound β c γ R ω hc hβ0 hβ1 hR hω hγ0 hlight)

/-! ## §E — the weight is the velocity: closing the circle with the shear module

At entanglement action `S_ent = log K = r/λ_C` — the entropic proper distance in
Compton units — the entropic aspect of the Born weight is `e^{−log K} = 1/K = tanh η`.
But `tanh η` is exactly the Ghosal boost velocity `β = e^{−r/λ_C}` of
`boost_velocity_eq_vacuumBell_decay`.  The weight of an Everett branch *is* the
velocity of the frame in which the tippe top distorts. -/

open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification in
/-- **The Born weight at the entanglement action is the boost velocity**:
`|w(S_ent = log K)|² = tanh η` — the entropic branch weight at the Schmidt action
equals the vacuum-Bell decay, i.e. the Ghosal rocket velocity. -/
theorem bornWeight_eq_boost_velocity (S_R ℏ η : ℝ) (hℏ : ℏ ≠ 0) (hη : 0 < η) :
    Complex.normSq (historyWeight S_R (Real.log (schmidtNumber η)) ℏ) = Real.tanh η := by
  have hK : 0 < schmidtNumber η :=
    div_pos (Real.cosh_pos η) (Real.sinh_pos_iff.mpr hη)
  rw [historyWeight_born _ _ _ hℏ, Real.exp_neg, Real.exp_log hK, schmidtNumber,
    Real.tanh_eq_sinh_div_cosh, inv_div]

open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification in
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance in
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity in
/-- The same weight with the action written as the **entropic proper distance in
Compton units**: `|w(S_ent = r/λ_C)|² = tanh η` — the Born weight literally at the
entanglement action of the separated regions. -/
theorem bornWeight_at_entropicDistance (S_R ℏ m c ħ η : ℝ) (hℏ : ℏ ≠ 0) (hη : 0 < η)
    (hlam : comptonWavelength m c ħ ≠ 0) :
    Complex.normSq (historyWeight S_R
      (entropicProperDistance m c ħ η / comptonWavelength m c ħ) ℏ) = Real.tanh η := by
  rw [entropicProperDistance, mul_div_cancel_left₀ _ hlam]
  exact bornWeight_eq_boost_velocity S_R ℏ η hℏ hη

open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification in
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart in
/-- **The frame whose velocity is the branch weight implements the Bogoliubov boost**:
substituting the Born weight for `β` in the Ghosal Lorentz map yields exactly
`thermoBogoliubov (−η)` — the Everett weight, the vacuum-Bell decay, the rocket
velocity, and the TFD boost parameter are one quantity read four ways. -/
theorem bornWeight_frame_eq_thermoBogoliubov (S_R ℏ η : ℝ) (hℏ : ℏ ≠ 0) (hη : 0 < η) :
    lorentzFrame (Complex.normSq (historyWeight S_R (Real.log (schmidtNumber η)) ℏ))
        1 (Real.cosh η) = thermoBogoliubov (-η) := by
  rw [bornWeight_eq_boost_velocity S_R ℏ η hℏ hη]
  exact lorentzFrame_eq_thermoBogoliubov η

/-! ## §F — the spacetime causal path integral reproduces the derived weight

The Sorkin quantal measure of the history path integral — `quantalMeasure D α =
(D α α).re` on the decoherence functional `D(α,β) = w(α)·conj(w(β))` — is exactly the
squared history amplitude, so the Deutsch derivation applies to it verbatim: Feynman's
path democracy (equal-action histories enter symmetrically) is the symmetric stratum,
and on decoherent branch partitions the diagonal is the *unique* continuous
refinement-consistent weight.  (The weld to the curved causal-diamond path integral
`PathIntegral.CurvedCausalHistoryPathIntegral` is held until that concurrent module
lands.) -/

open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert in
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
/-- **The quantal measure is the squared history amplitude**: Sorkin's diagonal measure
of the path-integral decoherence functional is the Born numerator `|w(α)|²`. -/
theorem quantalMeasure_decoherenceFunctional {ι : Type*} (w : ι → ℂ) (α : ι) :
    quantalMeasure (decoherenceFunctional w) α = Complex.normSq (w α) := by
  rw [quantalMeasure, decoherenceFunctional_apply, Complex.mul_conj, Complex.ofReal_re]

open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert in
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
/-- **Feynman's path democracy is the Deutsch symmetric stratum**: `n` histories of
equal entropic action have equal weights, so their normalized quantal measure is
forced to `1/n` by `branchWeight_symmetric_uniform` — "all paths enter with equal
weight" is precisely the symmetry premise of the Born derivation. -/
theorem equal_action_measure_uniform (n : ℕ) (hn : 0 < n) (S_R S ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (i : Fin n) :
    quantalMeasure (decoherenceFunctional (fun _ : Fin n => historyWeight S_R S ℏ)) i /
      (∑ j, quantalMeasure
        (decoherenceFunctional (fun _ : Fin n => historyWeight S_R S ℏ)) j)
      = 1 / n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hμ : ∀ j : Fin n,
      quantalMeasure (decoherenceFunctional (fun _ : Fin n => historyWeight S_R S ℏ)) j
        = Real.exp (-S) := fun j => by
    rw [quantalMeasure_decoherenceFunctional, historyWeight_born _ _ _ hℏ]
  have hSum : (∑ j : Fin n, quantalMeasure
      (decoherenceFunctional (fun _ : Fin n => historyWeight S_R S ℏ)) j)
      = n * Real.exp (-S) := by
    rw [Finset.sum_congr rfl (fun j _ => hμ j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hSum0 : (∑ j : Fin n, quantalMeasure
      (decoherenceFunctional (fun _ : Fin n => historyWeight S_R S ℏ)) j) ≠ 0 := by
    rw [hSum]
    positivity
  have h := branchWeight_symmetric_uniform
    (fun j : Fin n => quantalMeasure
      (decoherenceFunctional (fun _ : Fin n => historyWeight S_R S ℏ)) j /
      ∑ k, quantalMeasure
        (decoherenceFunctional (fun _ : Fin n => historyWeight S_R S ℏ)) k)
    (fun σ j => by simp only [hμ]) (by rw [← Finset.sum_div, div_self hSum0]) i
  simpa [Fintype.card_fin] using h

open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics in
open ComplexConjugate in
/-- **The decoherent path-integral diagonal is the unique Deutsch weight**: on a
decoherent branch partition (orthonormal records — the histories condition), the
reduced diagonal of the causal-history state is a fixed point of *every* continuous
refinement-consistent reweighting `f`: the spacetime path integral cannot introduce any
branch weight other than the derived Born weight. -/
theorem causal_diagonal_eq_deutsch_weight {dS dE : Type*} [Fintype dS] [Fintype dE]
    [DecidableEq dS] [DecidableEq dE]
    (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hrat : ∀ (k n : ℕ), 0 < n → k ≤ n → f ((k : ℝ) / n) = (k : ℝ) / n) (m : dS) :
    ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m
      = ((f (Complex.normSq (Ψ m)) : ℝ) : ℂ) := by
  rw [traceRight_correlatedKet_orthonormal Ψ χ horth, Matrix.diagonal_apply_eq,
    deutsch_born_unequal Ψ f hf hrat m]

end Physlib.QuantumMechanics.Foundations.RelativeStateConventionality

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight where
  formalizes @ "claim:every-finite-pure-state-ensemble-has-an-explicit-orthogonal-record-purification-whose-system-marginal-is-its-mixture",
  supported_by @ "lean:Ensemble.mix_of",
  supported_by @ "lean:MState.pure_apply",
  caveat @ "epistemic:constructive-finite-ensemble-to-purification-direction-not-the-converse-uniqueness-of-purification-theorem"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceLeft_diag where
  formalizes @ "claim:the-ancilla-record-diagonal-of-the-explicit-purification-is-exactly-the-original-ensemble-probability",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification",
  caveat @ "epistemic:orthogonal-record-readout-identity-not-a-claim-of-deterministic-remote-steering-or-post-facto-preparation"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.historyWeight_zero_negLog_one where
  formalizes @ "claim:a-positive-branch-coefficient-sqrt-p-is-exactly-the-zero-phase-unit-hbar-history-amplitude-at-entropic-action-minus-log-p",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston.historyWeight",
  caveat @ "epistemic:exact-log-exp-reparameterization-of-a-given-positive-probability-not-an-independent-derivation-of-that-probability"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_eq_historyWeight_smul where
  formalizes @ "claim:the-explicit-hjw-purification-is-a-superposition-of-relative-system-states-weighted-by-the-existing-complex-action-history-amplitudes",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.historyWeight_zero_negLog_one",
  caveat @ "epistemic:finite-positive-probability-amplitude-factorization-with-zero-branch-phases-not-a-dynamical-selection-principle"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_jointBlock_eq_decoherenceFunctional where
  formalizes @ "claim:every-joint-purification-record-block-factors-as-the-sorkin-rank-one-decoherence-kernel-times-the-relative-state-cross-matrix-element",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston.decoherenceFunctional_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_eq_historyWeight_smul",
  caveat @ "epistemic:exact-finite-rank-one-coherence-factorization-not-environmental-diagonalization-outcome-selection-or-the-full-hjw-unitary-orbit-converse"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_diag_eq_historyWeight where
  formalizes @ "claim:every-nonzero-ensemble-record-probability-is-the-history-weight-norm-at-entropic-action-minus-log-p",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston.historyWeight_born",
  caveat @ "epistemic:exact-reparameterization-of-an-existing-probability-as-imaginary-action-not-an-independent-dynamical-selection-law"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_sameMarginal_iff where
  formalizes @ "claim:two-explicit-ensemble-purifications-have-the-same-system-marginal-exactly-when-their-ensembles-mix-to-the-same-density-state",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight",
  caveat @ "epistemic:classifies-the-fiber-by-equal-marginals-but-does-not-yet-parameterize-that-fiber-by-the-full-ancilla-unitary-orbit"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.schrodingerHJW_exists_ensemble_and_ancilla where
  formalizes @ "claim:every-finite-mixed-state-has-a-reused-spectral-ensemble-and-an-explicit-orthogonal-record-purification",
  supported_by @ "lean:Ensemble.spectral_ensemble_mix",
  caveat @ "epistemic:finite-spectral-witness-existence-not-uniqueness-of-linearly-independent-ensembles-or-the-paper-support-vector-clause"

zil attach Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.schrodingerHJW_ancilla_unitary_preserves_mix where
  formalizes @ "claim:any-unitary-acting-only-on-the-ancilla-of-the-explicit-purification-preserves-the-system-density-state",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.traceRight_env_unitary_invariant",
  caveat @ "epistemic:proves-the-unitary-invariant-direction-not-that-every-pair-of-equal-marginal-purifications-is-related-by-such-a-unitary"

zil_file_contract physlib.schrodingerHJWFinite where
  promises "A dependency-reusing finite Schrödinger--HJW construction: an ensemble gives a normalized orthogonal-record purification, its system marginal is exactly the ensemble mixture, every positive branch coefficient is the existing complex-action history amplitude, every joint record block factors through the Sorkin decoherence kernel, spectral ensembles provide witnesses for all finite mixed states, and ancilla unitaries preserve the system mixture."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:QuantumInfo.States.Ensemble.PEnsemble",
    "lean:QuantumInfo.States.Ensemble.mix",
    "lean:Ensemble.spectral_ensemble_mix",
    "lean:QuantumInfo.States.Mixed.MState.pure",
    "lean:QuantumInfo.States.Mixed.MState.traceRight",
    "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.traceRight_env_unitary_invariant"]
  forbids_substitutes ["claiming the unproved converse uniqueness-of-purification/unitary-orbit theorem",
    "claiming uniqueness from linear independence without a proof",
    "claiming the support-vector realization clause or a deterministic post-facto steering protocol"]
  witnessed_by [Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceLeft_diag,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.historyWeight_zero_negLog_one,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_eq_historyWeight_smul,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_jointBlock_eq_decoherenceFunctional,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_diag_eq_historyWeight,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_sameMarginal_iff,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.schrodingerHJW_exists_ensemble_and_ancilla,
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.schrodingerHJW_ancilla_unitary_preserves_mix]

/- ZIL-END -/

/- Consolidated from Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement -/

/-!
# Unitary decoherent measurement

This file records the repository-level measurement dynamics that avoids taking
wave-function collapse as a primitive postulate:

1. the closed system evolves through a unitary interaction/S-matrix;
2. environmental coupling appears in the reduced system as complex-action
   damping/decoherence;
3. the reduced dynamics is represented by the finite-dimensional Lindblad/GKLS
   structure already available in the repo;
4. observed outcomes are handled by Born-weighted conditioning.

The formal scope is deliberately precise.  The current Lindblad infrastructure
proves the jump part is completely positive, the GKLS generator preserves trace,
and the GKLS rate is non-negative.  The full theorem that the integrated
Lindblad semigroup `exp(t L)` is CPTP remains downstream, as stated in
`LindbladCPTP`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped MState
open scoped ComplexOrder
open QuantumInfo.Finite
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.SMatrixDensityHerglotz
open Physlib.QuantumMechanics.Foundations.WeinbergStateVectorCollapse
open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.Lindblad
open Physlib.Thermodynamics.Landauer

namespace Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement


/-- The operational steps used by the unitary decoherent measurement model. -/
inductive MeasurementStep where
  /-- Unitary interaction of system, apparatus, and environment. -/
  | unitaryInteraction
  /-- Environmental decoherence / complex-action damping. -/
  | environmentalDecoherence
  /-- Reduced open-system dynamics in the Lindblad/GKLS channel layer. -/
  | lindbladReducedDynamics
  /-- Updating on an observed branch using Born weights. -/
  | bornWeightedConditioning
  /-- A primitive state-vector collapse postulate. -/
  | primitiveStateVectorCollapse
deriving DecidableEq, Repr

/-- Which operational step is the primitive collapse postulate. -/
def IsPrimitiveCollapse (step : MeasurementStep) : Prop :=
  step = .primitiveStateVectorCollapse

@[simp] lemma unitaryInteraction_not_primitiveCollapse :
    ¬ IsPrimitiveCollapse .unitaryInteraction := by
  simp [IsPrimitiveCollapse]

@[simp] lemma environmentalDecoherence_not_primitiveCollapse :
    ¬ IsPrimitiveCollapse .environmentalDecoherence := by
  simp [IsPrimitiveCollapse]

@[simp] lemma lindbladReducedDynamics_not_primitiveCollapse :
    ¬ IsPrimitiveCollapse .lindbladReducedDynamics := by
  simp [IsPrimitiveCollapse]

@[simp] lemma bornWeightedConditioning_not_primitiveCollapse :
    ¬ IsPrimitiveCollapse .bornWeightedConditioning := by
  simp [IsPrimitiveCollapse]


/-- Closed-system unitary interaction preserves von Neumann entropy of the joint density matrix. -/
lemma unitaryInteraction_preserves_vonNeumann
    {d dE : Type*} [Fintype d] [DecidableEq d] [Fintype dE] [DecidableEq dE]
    (ρ : MState (d × dE)) (S : 𝐔[d × dE]) :
    Sᵥₙ (S ◃ ρ) = Sᵥₙ ρ :=
  smatrix_preserves_vonNeumann ρ S

/-- Environmental decoherence is the modulus of the complex-action path-integral weight. -/
lemma environmentalDecoherence_is_pathIntegralDamping
    (S_R S_I ℏ : ℝ) :
    ‖complexActionPathIntegralWeight S_R S_I ℏ‖ = kuikenWeight ℏ S_I :=
  master_modulus_is_kuiken S_R S_I ℏ

/--
The finite Lindblad/GKLS reduced-dynamics layer currently available in the
repo: CP jump part, PSD drift coefficient, trace-preserving generator, and
non-negative entropic rate.
-/
lemma lindbladReducedDynamics_structural
    {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
    (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ) (ℏ : ℝ)
    (ρMat : Matrix d d ℂ) (ρ : MState d) :
    (lindbladJumpChannel L).IsCompletelyPositive ∧
      (lindbladDriftCoefficient L).PosSemidef ∧
      (gklsGenerator H L ℏ ρMat).trace = 0 ∧
      0 ≤ gklsEntropicRate L ρ := by
  exact ⟨lindbladJumpChannel_isCompletelyPositive L,
    lindbladDriftCoefficient_posSemidef L,
    trace_gklsGenerator_eq_zero H L ℏ ρMat,
    gklsEntropicRate_nonneg L ρ⟩

/-- Born-weighted conditioning: average branch imaginary action equals `ℏ` times Shannon entropy. -/
lemma bornWeightedConditioning_averageImagAction
    {α : Type*} [Fintype α] (ℏ : ℝ) (p : ProbDistribution α) :
    ∑ i, (p.prob i : ℝ) * (-ℏ * Real.log (p.prob i)) = ℏ * Hₛ p :=
  bornAvgImagAction_eq_Hbar_Hₛ ℏ p


/-- **HJW realizes Born conditioning through the complex-action branch weight.**  Every
finite pure-state ensemble has one normalized system--ancilla state whose system marginal is
the ensemble mixture; each nonzero ancilla-record probability is exactly the squared norm of
the complex-action history weight at `S_ent = -log pₐ`; and the ensemble-average imaginary
action is `ℏ` times its Shannon entropy.  This packages preparation, branch readout and
entropic cost while still excluding primitive collapse. -/
theorem hjwBornConditioning_complexAction_realization
    {d α : Type*} [Fintype d] [DecidableEq d] [Fintype α] [DecidableEq α]
    (e : PEnsemble d α) (a : α) (ha : e.distr a ≠ 0)
    (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    (MState.pure (ensemblePurification e)).traceRight =
        Ensemble.mix (e : MEnsemble d α) ∧
      ((MState.pure (ensemblePurification e)).traceLeft).m a a =
        (Complex.normSq
          (historyWeight S_R (-Real.log (e.distr a : ℝ)) ℏ) : ℂ) ∧
      (∑ i, (e.distr.prob i : ℝ) * (-ℏ * Real.log (e.distr.prob i)) =
        ℏ * Hₛ e.distr) ∧
      ¬ IsPrimitiveCollapse .bornWeightedConditioning := by
  exact ⟨ensemblePurification_traceRight e,
    ensemblePurification_diag_eq_historyWeight e a ha S_R ℏ hℏ,
    bornWeightedConditioning_averageImagAction ℏ e.distr,
    bornWeightedConditioning_not_primitiveCollapse⟩


/--
Weinberg-style finite collapse kernels can still be used as an effective
description: if the Born weights are left zero modes and the pointer basis is
dual to them, the final conditioned distribution recovers the same initial Born
weights.  This is not taken as primitive measurement dynamics in this file.
-/
lemma effectiveKernel_recovers_born_weights
    {Ω A : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
    (K : CollapseKernel Ω) (pointer : A → Ω → ℝ) (weight : A → Ω → ℝ)
    (P : ProbabilityDensity Ω)
    (hzero : ∀ a : A, leftZeroMode K (weight a))
    (hdual : dualPointerWeight pointer weight) (a : A) :
    expectation (weight a) (kernelAction K P) = 0 ∧
      expectation (weight a) (collapsedDistribution pointer weight P)
        = expectation (weight a) P :=
  born_weights_conserved_and_recovered K pointer weight P hzero hdual a


/--
Main package theorem.  A measurement model can use unitary interaction,
environmental damping, Lindblad/GKLS reduced dynamics, and Born-weighted
conditioning while explicitly excluding a primitive collapse postulate.
-/
lemma unitaryDecoherentMeasurement_summary
    {d dE ι α : Type*}
    [Fintype d] [DecidableEq d] [Fintype dE] [DecidableEq dE]
    [Fintype ι] [Fintype α]
    (ρSE : MState (d × dE)) (S : 𝐔[d × dE])
    (S_R S_I ℏ : ℝ)
    (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ)
    (ρMat : Matrix d d ℂ) (ρ : MState d)
    (p : ProbDistribution α) :
    Sᵥₙ (S ◃ ρSE) = Sᵥₙ ρSE ∧
      ‖complexActionPathIntegralWeight S_R S_I ℏ‖ = kuikenWeight ℏ S_I ∧
      (lindbladJumpChannel L).IsCompletelyPositive ∧
      (lindbladDriftCoefficient L).PosSemidef ∧
      (gklsGenerator H L ℏ ρMat).trace = 0 ∧
      0 ≤ gklsEntropicRate L ρ ∧
      (∑ i, (p.prob i : ℝ) * (-ℏ * Real.log (p.prob i)) = ℏ * Hₛ p) ∧
      ¬ IsPrimitiveCollapse .unitaryInteraction ∧
      ¬ IsPrimitiveCollapse .environmentalDecoherence ∧
      ¬ IsPrimitiveCollapse .lindbladReducedDynamics ∧
      ¬ IsPrimitiveCollapse .bornWeightedConditioning := by
  exact ⟨unitaryInteraction_preserves_vonNeumann ρSE S,
    environmentalDecoherence_is_pathIntegralDamping S_R S_I ℏ,
    lindbladJumpChannel_isCompletelyPositive L,
    lindbladDriftCoefficient_posSemidef L,
    trace_gklsGenerator_eq_zero H L ℏ ρMat,
    gklsEntropicRate_nonneg L ρ,
    bornWeightedConditioning_averageImagAction ℏ p,
    unitaryInteraction_not_primitiveCollapse,
    environmentalDecoherence_not_primitiveCollapse,
    lindbladReducedDynamics_not_primitiveCollapse,
    bornWeightedConditioning_not_primitiveCollapse⟩

end Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement

end

end


/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement.hjwBornConditioning_complexAction_realization where
  formalizes @ "claim:one-explicit-purification-composes-system-mixture-ancilla-born-readout-minus-log-p-history-weight-shannon-imaginary-action-average-and-no-primitive-collapse",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_diag_eq_historyWeight",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement.bornWeightedConditioning_averageImagAction",
  caveat @ "epistemic:finite-orthogonal-record-realization-and-probability-identity-not-a-dynamical-proof-of-outcome-selection-or-the-full-hjw-converse"

zil_file_contract physlib.hjwUnitaryDecoherentMeasurement where
  promises "A finite measurement bridge composing HJW ensemble purification, complex-action branch damping, the Shannon average imaginary action, and the explicit exclusion of primitive state-vector collapse."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_traceRight",
    "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.ensemblePurification_diag_eq_historyWeight",
    "lean:Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement.bornWeightedConditioning_averageImagAction"]
  forbids_substitutes ["claiming a primitive collapse mechanism",
    "claiming deterministic remote steering",
    "claiming the unproved converse HJW unitary-orbit theorem"]
  witnessed_by [Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement.hjwBornConditioning_complexAction_realization]

/- ZIL-END -/

