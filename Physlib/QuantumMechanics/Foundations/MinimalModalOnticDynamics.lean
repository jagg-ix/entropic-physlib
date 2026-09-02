/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.Channels.CPTP
public import QuantumInfo.ClassicalInfo.Entropy
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

/-!
# Minimal modal ontic dynamics (Barandes–Kagan)

Barandes & Kagan, *Measurement and Quantum Dynamics in the Minimal Modal Interpretation of
Quantum Theory*, Found. Phys. **50**, 1189–1218 (2020). The interpretation identifies a system's
*possible ontic states* with the eigenstates of its reduced density matrix (Axioms 1–2), reads
the eigenvalues as objective probabilities, localizes ontology system-by-system through partial
traces (Axiom 3), and supplements the density-matrix dynamics with *quantum conditional
probabilities* `p(i₁,i₂;t′|w;t) = Tr[(P̂₁⊗P̂₂) ℰ{P̂_w}]` over a linear CPTP evolution `ℰ`
(Axiom 4, Eqs. 7–8, 60–61). This file formalizes the paper's exact mathematics on the
`QuantumInfo` carriers (`MState`, `Ket`, `CPTPMap`).

**No axioms — everything is derived.** The paper presents its interpretation as four numbered
"Axioms"; this file postulates none of them. It contains no `axiom` declaration, and an
`#print axioms` audit of every theorem below reports only Lean's standard foundations
(`propext`, `Classical.choice`, `Quot.sound`). Each of the paper's Axioms enters as a
*construction whose defining properties are theorems*: Axioms 1–2 (eigenstate ontology,
eigenvalue probabilities) are carried by `MState.spectralDecomposition` and by
`MState.spectrum` being a `ProbDistribution` by proof; Axiom 3 (system-centric ontology) is
the partial-trace construction `MState.traceLeft`/`traceRight`; Axiom 4's conditional
probabilities are a *definition* assembled from standard ingredients — eigenprojectors, a
CPTP map, the trace — whose right to the name "probability" is *derived*
(`onticConditionalProb_mem_unitInterval`, `onticConditionalProbPair_sum`,
`bayesian_propagation`), in line with the paper's own Appendix remark that the formula is
constructed "out of standard ingredients without introducing any exotic elements or
assumptions"; and the Born rule is not assumed but obtained exactly in the
distinguishable-record limit (`traceRight_correlatedKet_orthonormal`). Where the paper's
axiom numbering appears below it is a *citation label* into the paper, not a postulate of
this module.

**The Born rule was already derived in this repository before this module** — this file adds
a *second, independent route* and proves the two agree. The prior route is entropic:
`DecoherenceFunctionalSorkinJohnston.historyWeight_born` derives `|w|² = e^{−S_ent}` (the Born
weight is the exponentiated entanglement/imaginary action), with its measurement-hub readings
`UnitaryDecoherentMeasurement.bornWeightedConditioning_averageImagAction` (average branch
imaginary action = `ℏ·Hₛ`) and `effectiveKernel_recovers_born_weights`, the hydrodynamic form
`MadelungPolarDecomposition.madelung_born_rule` (`ρ = R²`), and the model-level off-diagonal
suppression `CaldeiraLeggettDecoherence` (Born diagonal preserved) — of which §D's Gram factor
is the exact partial-trace counterpart. The new route here is reduced-density-matrix
decoherence: Born weights as the diagonal of the traced-out correlated state. The weld
`born_diagonal_eq_historyWeight` shows the routes coincide exactly: each outcome's diagonal
Born weight *is* the squared modulus of an entropic history weight at branch entanglement
action `S_ent(m) = −log |Ψ_m|²`.

* **§A — quantum conditional probabilities** (Eqs. 7–8, 60–61 and the Appendix).
  `onticConditionalProb`/`onticConditionalProbPair`; membership in the unit interval
  (Eqs. 62–63) is inherited from `MState.exp_val_prob`; the joint conditionals sum to one over
  complete final eigenbases (`onticConditionalProbPair_sum`, the Appendix unit-measure claim);
  and the spectral mixture propagates by linearity (`bayesian_propagation`, Eqs. 57–59), the
  Bayesian formula that motivates Axiom 4.
* **§B — unitary dynamics has no ontic jumps** (§4.3). Under `CPTPMap.ofUnitary U` the
  conditional probability from an ontic state to its own unitary transport is `1`
  (`unitary_no_jump`) and to the transport of any orthogonal ontic state is `0`
  (`unitary_orthogonal_no_jump`) — pure reuse of `MState.inner_U_conj`: the unitary case is the
  unique scenario with no trajectory uncertainty. The Deutsch–Jozsa-shaped corollaries
  `deterministic_readout`/`excluded_readout` express one-query algorithmic certainty as this
  trivialization of the conditional probabilities (the AFP Isabelle-Marries-Dirac port's
  `dj_constant_output_all_zeros`/`dj_balanced_output_not_all_zeros` are their intended
  instantiations once that Phase-1 port derives its axiomatized laws).
* **§C — the correlation operator** (Eq. 28). `correlationMatrix ρ = ρ − ρ_S ⊗ ρ_E` has
  vanishing partial traces over both factors and vanishing trace — the object whose nonzero-ness
  is the entanglement that masks the actual ontic state.
* **§D — measurement as entangling correlation** (Eqs. 13–19 and Eq. 10).
  `correlatedKet Ψ χ` is the post-measurement state `Σ_m Ψ_m |m⟩|χ_m⟩` produced by the linear
  two-step chain (Eqs. 14–15); its reduced density matrix is exactly the coefficient matrix
  times the record-state overlap Gram factor (`traceRight_pure_correlatedKet`, Eq. 16). With
  perfectly distinguishable records the improper mixture is *exactly* the Born-diagonal state
  (`traceRight_correlatedKet_orthonormal`, Eqs. 10 and 17–19 in the ideal limit); in general the
  off-diagonal coherences carry the full overlap in norm (`traceRight_offdiagonal_norm`), the
  overlap of factorized many-degree-of-freedom records is the product of single-degree overlaps
  (`recordOverlap_factorizes`, the structure behind `⟨E(m₂)|E(m₁)⟩ ∼ e^{−N_E f_E}`), and a
  uniform single-factor bound `e^{−γ}` gives the exponential suppression `e^{−Nγ}`
  (`record_overlap_exponential_bound`).
* **§E — the error–entropy bound** (Eq. 23). The minimum apparatus error, one over the number
  of available ontic states, is `exp(−S_max)` of the maximal (uniform) Shannon entropy
  (`minimum_error_eq_exp_neg_maxEntropy`), and an `N`-degree-of-freedom apparatus with `#`
  states per degree of freedom has `S_max = N·log #` (`apparatus_maxEntropy`) — the corrections
  to the Born rule sit at the apparatus's own error–entropy floor.
* **§F — the environment-induced Kraus decomposition** (Eqs. 30–32). Tracing the environment
  out of unitarily evolved uncorrelated initial data is *exactly* the Kraus sum over the
  paper's explicit operators `Ê_{ee′} = √(p_e) ⟨e′|Û_W|e⟩` (`environment_kraus_decomposition`)
  — linear CPTP subsystem dynamics is derived from closed-system unitarity, not posited, and
  the map's dependence on the environment's initial spectral data (§4.4 observation (a)) is
  visible in the operators themselves.
* **§G — subsystem conditionals and the no-entanglement factorization** (Eqs. 44–47, 49–56).
  Padding a subsystem eigenprojector with the identity and evaluating on the parent equals
  evaluating on the partial trace (`marginal_probability_consistency`) — the derived
  consistency of Axiom 3's system-centric ontology; the entangled-case conditional probability
  `subsystemConditionalProb` (Eq. 44) computes in the reduced state, and factorized initial
  projectors reduce it to the environment-conditioned evolution of Eq. 47
  (`subsystemConditionalProb_factorized`) — entanglement at the initial time is exactly what
  blocks this classical-in-form reduction (§4.6).
* **§I — zero-time conditionals and a semigroup-failure witness** (Eqs. 37–40). At zero time
  the conditionals are Kronecker deltas (`instantaneous_self`/`instantaneous_orthogonal`,
  Eq. 37's exact core — the anchor of §4.7's instability smoothing). Centrally: the semigroup
  property Eq. 40 is *witnessed to fail* (`semigroup_property_fails`) — for partial-swap
  dynamics `U = (1+i·SWAP)/√2` on a qubit pair, composing the two single-step reduced maps
  gives `¼|1⟩⟨1| + ¾|0⟩⟨0|` while the directly-induced map of `U² = i·SWAP` (the replacement
  channel) gives `|0⟩⟨0|`. This is the paper's obstruction to an a priori measure on exact
  ontic trajectories — the origin of the non-probabilistic (Knightian) uncertainty. General
  reusable helpers: `swapMatrix` with `swap_conj_kron` (`S(A⊗B)S = B⊗A`),
  `traceRight_kronecker`, `traceRight_kron_mul_swap`/`traceRight_swap_mul_kron`
  (`Tr_E[(A⊗B)S] = AB`), and the closed form `reducedDynamics_partialSwap`
  (`ℰ{ρ} = ½(ρ + Tr(ρ)P + i[P,ρ])`).
* **§J — the subsystem state does not determine subsystem dynamics** (§4.6, Eqs. 43, 48).
  Witness (`reduced_state_does_not_determine_dynamics`): the uncorrelated `½·1 ⊗ |0⟩⟨0|` and
  the classically correlated `½(|00⟩⟨00| + |11⟩⟨11|)` have identical reduced states, yet the
  same parent unitary (the swap) evolves them to different reduced states — no map on
  subsystem density matrices, linear or otherwise, captures correlated open-subsystem
  dynamics. Even *classical* correlations suffice for this obstruction; entanglement makes it
  uniquely quantum. This is why the actual ontic trajectory of a correlated subsystem is
  hidden (Eq. 48, footnote 15).
* **§H — Kraus composition and the coarse-grained trajectory measure** (Eqs. 38, 42).
  Composing Kraus families gives the multi-indexed product family (`kraus_composition`,
  Eq. 38); chained row-normalized conditionals stay normalized
  (`chained_conditionals_normalized`), so the coarse-grained trajectory probabilities of
  Eq. 42 sum to one over all trajectories (`trajectory_measure_normalized`) — a genuine
  probability measure exists on the coarse-grained trajectory space, in contrast with the
  exact-trajectory space where the generic failure of the semigroup property (Eq. 40) blocks
  the construction.

**Honest layering.** Exact and proven here: the Appendix well-definedness of the conditional
probabilities, spectral Bayesian propagation, the no-jump property of unitary evolution, the
vanishing partial traces of the correlation operator, the reduced post-measurement matrix with
its Gram overlap factor, the exact Born diagonal for distinguishable records, the product
factorization and exponential bound for record overlaps, the error–entropy identity, the
environment-induced Kraus form with the paper's explicit operators, the marginal/partial-trace
consistency and no-entanglement factorization, the Kraus composition law, and the normalization
of the coarse-grained trajectory measure. Carried by the `QuantumInfo` library and cited, not
re-proven: non-negativity/unit-trace bundling (`MState`), generic Kraus existence
(`MatrixMap.exists_kraus`, `CPTPMap.of_kraus_CPTPMap`), purification (the converse of Eq. 10,
`MState.purify_spec`). Interpretation, not theorems: reading eigenstates as ontic possibilities
and eigenvalues as objective probabilities. Deferred (model-dependent or analytic): the
decoherence *rates* `f_A, f_E` (Eq. 16 asymptotics and Eqs. 18–22 eigenvector-perturbation
corrections), the analytic `t → 0` *limit* of Eq. 37 (its zero-time value is exact in §I), the
dynamically-set Markovian coarse-graining timescale `δt_S` (§4.5), and the Bloch-sphere
double-helix illustration of §4.2.1 (Eq. 26's parametrization is library content,
`QuantumInfo…BlochSphere`/`Qubit`); the semigroup failure of Eq. 40 and the §4.6
state-does-not-determine-dynamics obstruction, formerly deferred, are now witnessed
concretely in §I and §J. Related repo modules:
`Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement` (the no-primitive-collapse
measurement hub) and `Physlib.QuantumMechanics.ComplexAction.RudolphHomogeneousDecoherence`
(history-space decoherence functionals).

## References

* J. A. Barandes, D. Kagan, "Measurement and Quantum Dynamics in the Minimal Modal
  Interpretation of Quantum Theory", Found. Phys. 50, 1189 (2020).
* J. A. Barandes, D. Kagan, "The Minimal Modal Interpretation of Quantum Theory",
  arXiv:1405.6755.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped MState
open scoped HermitianMat
open scoped InnerProductSpace RealInnerProductSpace
open scoped Matrix
open ComplexConjugate

namespace Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics

variable {d d₁ d₂ dS dE : Type*}
variable [Fintype d] [DecidableEq d] [Fintype d₁] [DecidableEq d₁]
variable [Fintype d₂] [DecidableEq d₂]
variable [Fintype dS] [DecidableEq dS] [Fintype dE] [DecidableEq dE]

/-! ## §A — quantum conditional probabilities (the paper's Axiom 4, here derived —
Eqs. 7–8, 60–61, Appendix) -/

/-- **The quantum conditional probability** (the paper's Axiom 4, Eq. 8 — here a definition
from standard ingredients, with its probability character derived below):
`p(s′;t′|s;t) = Tr[P̂(s′;t′) ℰ{P̂(s;t)}]` — the probability for the system to be in the
possible ontic state `P′` at the later time given that it was in the ontic state `ψ` at the
earlier time, when the interval is governed by the linear CPTP map `Λ`. The initial
eigenprojector is the rank-one `|ψ⟩⟨ψ|`; the final possible ontic state is carried as an
`MState` (positive-semidefinite, unit trace), of which the rank-one eigenprojectors of the
evolved density matrix are the intended case. -/
def onticConditionalProb (Λ : CPTPMap d d) (P' : MState d) (ψ : Ket d) : ℝ :=
  (Λ (MState.pure ψ)).exp_val P'.M

/-- **The conditional probabilities are probabilities** (Appendix, Eqs. 62–63): each lies in
the unit interval — non-negativity is the paper's `Tr[ÂB̂] ≥ 0` for positive-semidefinite
pairs, carried here by `MState.exp_val_prob`. -/
theorem onticConditionalProb_mem_unitInterval (Λ : CPTPMap d d) (P' : MState d) (ψ : Ket d) :
    0 ≤ onticConditionalProb Λ P' ψ ∧ onticConditionalProb Λ P' ψ ≤ 1 :=
  (Λ (MState.pure ψ)).exp_val_prob ⟨P'.nonneg, P'.le_one⟩

/-- **The joint conditional probability for two disjoint subsystems** (Eqs. 7 and 60):
`p(i₁,i₂;t′|w;t) = Tr[(P̂_{Q₁}(i₁;t′) ⊗ P̂_{Q₂}(i₂;t′)) ℰ_W{P̂_W(w;t)}]` — the parent system
`W = Q₁ + Q₂` was in the ontic state `ψ`; the probability that the subsystems land in the
respective possible ontic states `φ₁`, `φ₂`. -/
def onticConditionalProbPair (Λ : CPTPMap (d₁ × d₂) (d₁ × d₂))
    (φ₁ : Ket d₁) (φ₂ : Ket d₂) (ψ : Ket (d₁ × d₂)) : ℝ :=
  (Λ (MState.pure ψ)).exp_val ((MState.pure φ₁ ⊗ᴹ MState.pure φ₂).M)

/-- The joint conditionals lie in the unit interval (Appendix, Eqs. 62–63). -/
theorem onticConditionalProbPair_mem_unitInterval (Λ : CPTPMap (d₁ × d₂) (d₁ × d₂))
    (φ₁ : Ket d₁) (φ₂ : Ket d₂) (ψ : Ket (d₁ × d₂)) :
    0 ≤ onticConditionalProbPair Λ φ₁ φ₂ ψ ∧ onticConditionalProbPair Λ φ₁ φ₂ ψ ≤ 1 :=
  (Λ (MState.pure ψ)).exp_val_prob
    ⟨(MState.pure φ₁ ⊗ᴹ MState.pure φ₂).nonneg, (MState.pure φ₁ ⊗ᴹ MState.pure φ₂).le_one⟩

/-- Expectation values are additive over finite families of observables. -/
theorem exp_val_finsetSum {ι : Type*} (s : Finset ι) (ρ : MState d)
    (T : ι → HermitianMat d ℂ) :
    ρ.exp_val (∑ i ∈ s, T i) = ∑ i ∈ s, ρ.exp_val (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MState.exp_val_zero]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, MState.exp_val_add, ih, Finset.sum_insert hx]

/-- Complete families of final eigenprojectors tensor to a complete family on the parent
system: the resolution of the identity behind the Appendix unit-measure computation. -/
theorem sum_pure_prod_M {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (P : ι₁ → MState d₁) (Q : ι₂ → MState d₂)
    (h₁ : ∑ i, (P i).M = 1) (h₂ : ∑ j, (Q j).M = 1) :
    ∑ p : ι₁ × ι₂, (P p.1 ⊗ᴹ Q p.2).M = 1 := by
  apply HermitianMat.ext
  rw [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
  have h₁' : ∑ i, (P i).M.mat = (1 : Matrix d₁ d₁ ℂ) := by
    rw [← HermitianMat.mat_finset_sum, h₁, HermitianMat.mat_one]
  have h₂' : ∑ j, (Q j).M.mat = (1 : Matrix d₂ d₂ ℂ) := by
    rw [← HermitianMat.mat_finset_sum, h₂, HermitianMat.mat_one]
  ext ⟨a, b⟩ ⟨c, e⟩
  calc (∑ p : ι₁ × ι₂, (MState.prod (P p.1) (Q p.2)).M.mat) (a, b) (c, e)
      = ∑ p : ι₁ × ι₂, (P p.1).M.mat a c * (Q p.2).M.mat b e := by
        rw [Matrix.sum_apply]
        exact Finset.sum_congr rfl fun p _ => rfl
    _ = (∑ i, (P i).M.mat a c) * ∑ j, (Q j).M.mat b e := by
        rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    _ = (∑ i, (P i).M.mat) a c * (∑ j, (Q j).M.mat) b e := by
        rw [Matrix.sum_apply, Matrix.sum_apply]
    _ = (1 : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (a, b) (c, e) := by
        rw [h₁', h₂']
        by_cases hac : a = c <;> by_cases hbe : b = e <;>
          simp [Matrix.one_apply, hac, hbe, Prod.ext_iff]

/-- **Unit measure** (Appendix, the computation closing Eq. 61 → 1): over complete families of
final possible ontic states of the two subsystems, the joint conditional probabilities sum to
one — trace preservation of `ℰ` plus the resolution of the identity. The quantum conditional
probabilities of the paper's Axiom 4 are, by derivation, genuine probability
distributions. -/
theorem onticConditionalProbPair_sum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (Λ : CPTPMap (d₁ × d₂) (d₁ × d₂))
    (φ₁ : ι₁ → Ket d₁) (φ₂ : ι₂ → Ket d₂) (ψ : Ket (d₁ × d₂))
    (h₁ : ∑ i, (MState.pure (φ₁ i)).M = 1) (h₂ : ∑ j, (MState.pure (φ₂ j)).M = 1) :
    ∑ p : ι₁ × ι₂, onticConditionalProbPair Λ (φ₁ p.1) (φ₂ p.2) ψ = 1 := by
  unfold onticConditionalProbPair
  rw [← exp_val_finsetSum,
    sum_pure_prod_M (fun i => MState.pure (φ₁ i)) (fun j => MState.pure (φ₂ j)) h₁ h₂,
    MState.exp_val_one]

/-- The expectation value as a complex trace: `⟨T⟩_σ = Tr[σT]` — the coercion workhorse for
transferring matrix trace identities to `MState.exp_val` statements. -/
theorem exp_val_coe_trace (σ : MState d) (T : HermitianMat d ℂ) :
    ((σ.exp_val T : ℝ) : ℂ) = (σ.m * T.mat).trace := by
  have h := HermitianMat.inner_eq_trace_rc σ.M T
  rw [MState.mat_M] at h
  exact_mod_cast h

/-- **Bayesian propagation** (Eqs. 57–59): if the parent state is spectrally decomposed as
`ρ = Σ_w p(w) |Ψ_w⟩⟨Ψ_w|`, then any expectation value after the linear CPTP evolution is the
`p(w)`-mixture of the conditional expectation values from the individual eigenstates —
specializing the observable to a final eigenprojector gives `p(w′;t′) = Σ_w p(w′|w) p(w;t)`,
the law of total probability from which the paper's Axiom 4 formula is read off — here the
direction is derivation, not postulate. The decomposition hypothesis is provided by
`MState.spectralDecomposition`. -/
theorem bayesian_propagation (Λ : CPTPMap d d) (ρ : MState d) (T : HermitianMat d ℂ)
    (ψs : d → Ket d)
    (hspec : ρ.M = ∑ w, (ρ.spectrum w : ℝ) • (MState.pure (ψs w)).M) :
    (Λ ρ).exp_val T = ∑ w, (ρ.spectrum w : ℝ) * (Λ (MState.pure (ψs w))).exp_val T := by
  have hmat : ρ.m = ∑ w, (ρ.spectrum w : ℝ) • (MState.pure (ψs w)).m := by
    have hmatCoe := congrArg HermitianMat.mat hspec
    rwa [HermitianMat.mat_finset_sum] at hmatCoe
  have happ : (Λ ρ).m = ∑ w, (ρ.spectrum w : ℝ) • (Λ (MState.pure (ψs w))).m := by
    rw [CPTPMap.mat_coe_eq_apply_mat, hmat, map_sum]
    exact Finset.sum_congr rfl fun w _ => by
      rw [LinearMap.map_smul_of_tower, CPTPMap.mat_coe_eq_apply_mat]
  have hval : ∀ σ : MState d, ((σ.exp_val T : ℝ) : ℂ) = (σ.m * T.mat).trace :=
    fun σ => exp_val_coe_trace σ T
  have htr : ((Λ ρ).m * T.mat).trace
      = ∑ w, ((ρ.spectrum w : ℝ) : ℂ) * ((Λ (MState.pure (ψs w))).m * T.mat).trace := by
    rw [happ, Finset.sum_mul, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun w _ => by
      rw [Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]
  have key : (((Λ ρ).exp_val T : ℝ) : ℂ)
      = ((∑ w, (ρ.spectrum w : ℝ) * (Λ (MState.pure (ψs w))).exp_val T : ℝ) : ℂ) := by
    rw [hval (Λ ρ), htr]
    push_cast
    exact Finset.sum_congr rfl fun w _ => by rw [hval (Λ (MState.pure (ψs w)))]
  exact_mod_cast key

/-! ## §B — unitary evolution has no ontic jumps (§4.3) -/

/-- **Unitary dynamics never jumps** (§4.3): if the closed-system evolution is exactly unitary,
the conditional probability from the ontic state `ψ` to its own unitary transport `U|ψ⟩⟨ψ|U†`
is `1` — the unique scenario with no uncertainty about the ontic trajectory. Pure reuse of
`MState.inner_U_conj`. -/
theorem unitary_no_jump (U : Matrix.unitaryGroup d ℂ) (ψ : Ket d) :
    onticConditionalProb (CPTPMap.ofUnitary U) (U ◃ MState.pure ψ) ψ = 1 := by
  have h : onticConditionalProb (CPTPMap.ofUnitary U) (U ◃ MState.pure ψ) ψ
      = (⟪(CPTPMap.ofUnitary U) (MState.pure ψ), U ◃ MState.pure ψ⟫_Prob : ℝ) :=
    (MState.val_inner _ _).symm
  rw [h, CPTPMap.ofUnitary_eq_conj, MState.inner_U_conj, MState.pure_inner,
    Braket.dot_self_eq_one]
  simp

/-- **Jumps to orthogonal transported states have probability zero** (§4.3): for `φ ⊥ ψ`, the
conditional probability from `ψ` to the transported eigenstate `U|φ⟩⟨φ|U†` vanishes — together
with `unitary_no_jump`, the only ontic trajectory available under exact unitary evolution is
the one tracking the state vector. -/
theorem unitary_orthogonal_no_jump (U : Matrix.unitaryGroup d ℂ) (ψ φ : Ket d)
    (horth : Braket.dot φ ψ = 0) :
    onticConditionalProb (CPTPMap.ofUnitary U) (U ◃ MState.pure φ) ψ = 0 := by
  have h : onticConditionalProb (CPTPMap.ofUnitary U) (U ◃ MState.pure φ) ψ
      = (⟪(CPTPMap.ofUnitary U) (MState.pure ψ), U ◃ MState.pure φ⟫_Prob : ℝ) :=
    (MState.val_inner _ _).symm
  rw [h, CPTPMap.ofUnitary_eq_conj, MState.inner_U_conj, MState.pure_inner]
  have hsymm : Braket.dot ψ φ = 0 := by
    rw [Braket.dot_swap_conj, horth, map_zero]
  rw [hsymm]
  simp

/-- **Deterministic readout** (the Deutsch–Jozsa shape of §4.3): if a unitary circuit carries
the input ontic state *exactly onto* a pointer eigenstate `φ` of the readout basis, then the
quantum conditional probability of that outcome is `1` — the algorithm's answer is certain in
a single query because the ontic trajectory has no uncertainty, not because of collapse. This
is the abstract form of the Deutsch–Jozsa *constant* case (`dj_constant_output_all_zeros` in
the AFP Isabelle-Marries-Dirac port, `CATEPTMain/AFPBridge/IMD/Deutsch_Jozsa.lean`, where
`U = (H^{⊗n} ⊗ 1)·U_f·(H^{⊗n} ⊗ H)` lands on `|0…0⟩` exactly): that port is Phase-1
(statements typed, laws still `axiom`s), so per the no-axioms rule the link is established
here as a derived theorem awaiting instantiation, not by importing the port. -/
theorem deterministic_readout (U : Matrix.unitaryGroup d ℂ) (ψ φ : Ket d)
    (h : (CPTPMap.ofUnitary U) (MState.pure ψ) = MState.pure φ) :
    onticConditionalProb (CPTPMap.ofUnitary U) (MState.pure φ) ψ = 1 := by
  unfold onticConditionalProb
  rw [h]
  have hval : (MState.pure φ).exp_val (MState.pure φ).M
      = (⟪MState.pure φ, MState.pure φ⟫_Prob : ℝ) :=
    (MState.val_inner _ _).symm
  rw [hval, MState.pure_inner, Braket.dot_self_eq_one]
  simp

/-- **Excluded readout** (the Deutsch–Jozsa *balanced* case): if the circuit output is exactly
orthogonal to a pointer eigenstate, that outcome has conditional probability `0` — the
abstract form of `dj_balanced_output_not_all_zeros` in the AFP port (the all-zeros amplitude
of the balanced output vanishes). Together with `deterministic_readout`, this is why the
minimal modal interpretation reads a one-query quantum algorithm as revealing a *definite*
pre-existing ontic state rather than collapsing an indefinite one. -/
theorem excluded_readout (U : Matrix.unitaryGroup d ℂ) (ψ χ φ : Ket d)
    (h : (CPTPMap.ofUnitary U) (MState.pure ψ) = MState.pure χ)
    (horth : Braket.dot φ χ = 0) :
    onticConditionalProb (CPTPMap.ofUnitary U) (MState.pure φ) ψ = 0 := by
  unfold onticConditionalProb
  rw [h]
  have hval : (MState.pure χ).exp_val (MState.pure φ).M
      = (⟪MState.pure χ, MState.pure φ⟫_Prob : ℝ) :=
    (MState.val_inner _ _).symm
  have hsymm : Braket.dot χ φ = 0 := by
    rw [Braket.dot_swap_conj, horth, map_zero]
  rw [hval, MState.pure_inner, hsymm]
  simp

/-! ## §C — the correlation operator (Eq. 28) -/

/-- **The correlation operator** (Eq. 28): `σ̂_SE := ρ̂_W − ρ̂_S ⊗ ρ̂_E`, the part of the
parent density matrix not captured by the subsystem states; it encodes all classical and
quantum correlations between `S` and `E`, and its nonvanishing is what hides the actual ontic
state of the subsystem. -/
def correlationMatrix (ρ : MState (d₁ × d₂)) : Matrix (d₁ × d₂) (d₁ × d₂) ℂ :=
  ρ.m - (ρ.traceRight ⊗ᴹ ρ.traceLeft).m

/-- The partial trace of an `MState` at the matrix level. -/
theorem traceRight_m (ρ : MState (d₁ × d₂)) : ρ.m.traceRight = ρ.traceRight.m := rfl

/-- The partial trace of an `MState` at the matrix level. -/
theorem traceLeft_m (ρ : MState (d₁ × d₂)) : ρ.m.traceLeft = ρ.traceLeft.m := rfl

/-- **The correlation operator has no one-sided content** (Eq. 28): its partial trace over the
environment vanishes — by construction, `σ̂_SE` carries only correlations. -/
theorem correlationMatrix_traceRight (ρ : MState (d₁ × d₂)) :
    (correlationMatrix ρ).traceRight = 0 := by
  unfold correlationMatrix
  rw [Matrix.traceRight_sub, traceRight_m, traceRight_m,
    MState.traceRight_prod_eq ρ.traceRight ρ.traceLeft, sub_self]

/-- The partial trace over the subsystem also vanishes (Eq. 28). -/
theorem correlationMatrix_traceLeft (ρ : MState (d₁ × d₂)) :
    (correlationMatrix ρ).traceLeft = 0 := by
  unfold correlationMatrix
  rw [Matrix.traceLeft_sub, traceLeft_m, traceLeft_m,
    MState.traceLeft_prod_eq ρ.traceRight ρ.traceLeft, sub_self]

/-- The correlation operator is traceless: both terms are unit-trace states. -/
theorem correlationMatrix_trace (ρ : MState (d₁ × d₂)) :
    (correlationMatrix ρ).trace = 0 := by
  unfold correlationMatrix
  rw [Matrix.trace_sub, ρ.tr', (ρ.traceRight ⊗ᴹ ρ.traceLeft).tr', sub_self]

/-! ## §D — measurement as entangling correlation (Eqs. 13–19, Eq. 10) -/

/-- **The post-measurement state of the linear chain** (Eqs. 13–15): expanding the subject
system's initial state in measurement-outcome states, `|Ψ⟩ = Σ_m Ψ_m |m⟩`, the two-step linear
evolution produces `Σ_m Ψ_m |m⟩ |χ_m⟩` where `|χ_m⟩` collects the apparatus/environment record
states. Normalization holds because each record state is normalized. -/
def correlatedKet (Ψ : Ket dS) (χ : dS → Ket dE) : Ket (dS × dE) where
  vec p := Ψ p.1 * χ p.1 p.2
  normalized' := by
    rw [Fintype.sum_prod_type]
    calc ∑ m, ∑ e, ‖Ψ m * χ m e‖ ^ 2
        = ∑ m, ‖Ψ m‖ ^ 2 * ∑ e, ‖χ m e‖ ^ 2 := by
          simp [mul_pow, Finset.mul_sum]
      _ = ∑ m, ‖Ψ m‖ ^ 2 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          have hχ : ∑ e, ‖(χ m) e‖ ^ 2 = 1 := (χ m).normalized'
          rw [hχ, mul_one]
      _ = 1 := Ψ.normalized'

/-- **The reduced density matrix after measurement** (Eq. 16): tracing the records out of the
correlated pure state leaves the coefficient matrix `Ψ_{m₁} Ψ*_{m₂}` times the record overlap
`⟨χ_{m₂}|χ_{m₁}⟩` — the diagonal is the Born weight; every coherence is weighted by the
distinguishability of the records. -/
theorem traceRight_pure_correlatedKet (Ψ : Ket dS) (χ : dS → Ket dE) (m₁ m₂ : dS) :
    ((MState.pure (correlatedKet Ψ χ)).traceRight).m m₁ m₂
      = Ψ m₁ * conj (Ψ m₂) * ∑ e, χ m₁ e * conj (χ m₂ e) := by
  rw [← traceRight_m]
  simp only [Matrix.traceRight, Matrix.of_apply, MState.pure_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by
    simp only [correlatedKet, Ket.apply, map_mul]
    ring

/-- **Exact decoherence: the improper mixture is the Born mixture** (Eqs. 10 and 17–19 in the
ideal limit): when the records are perfectly distinguishable (orthogonal for distinct
outcomes), the subject system's reduced density matrix is *exactly* diagonal in the
measurement basis with Born-rule entries `|Ψ_m|²` — the minimal modal interpretation reads
these eigenstates as the possible ontic states and the eigenvalues as their objective
probabilities. This is also Eq. (10): the improper mixture arising from entanglement. -/
theorem traceRight_correlatedKet_orthonormal (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0) :
    ((MState.pure (correlatedKet Ψ χ)).traceRight).m
      = Matrix.diagonal fun m => (Complex.normSq (Ψ m) : ℂ) := by
  -- The repo's earlier Born derivation is entropic (`historyWeight_born`); the weld
  -- `born_diagonal_eq_historyWeight` below identifies the two routes exactly.
  ext m₁ m₂
  rw [traceRight_pure_correlatedKet]
  by_cases h : m₁ = m₂
  · subst h
    have hone : ∑ e, χ m₁ e * conj (χ m₁ e) = 1 := by
      have hnormalized := (χ m₁).normalized
      calc ∑ e, χ m₁ e * conj (χ m₁ e) = ∑ e, (Complex.normSq (χ m₁ e) : ℂ) := by
            exact Finset.sum_congr rfl fun e _ => Complex.mul_conj _
        _ = ((∑ e, Complex.normSq (χ m₁ e) : ℝ) : ℂ) := by push_cast; rfl
        _ = 1 := by rw [hnormalized]; norm_num
    rw [hone, mul_one, Matrix.diagonal_apply_eq, Complex.mul_conj]
  · rw [horth m₁ m₂ h, mul_zero, Matrix.diagonal_apply_ne _ h]

open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston in
/-- **The two Born derivations agree.** The Born rule was derived in this repository before
this module, by the entropic route: `historyWeight_born` gives `|w|² = e^{−S_ent}`, the Born
weight as exponentiated entanglement action. This theorem identifies the decoherence route
with it exactly: each outcome's diagonal Born weight from the traced-out correlated state *is*
the squared modulus of a history weight at branch entanglement action
`S_ent(m) = −log |Ψ_m|²`, for any real action `S_R` and any `ℏ ≠ 0` — the partial-trace Born
rule and the complex-action Born rule are the same number. -/
theorem born_diagonal_eq_historyWeight (Ψ : Ket dS) (χ : dS → Ket dE)
    (horth : ∀ m₁ m₂, m₁ ≠ m₂ → ∑ e, χ m₁ e * conj (χ m₂ e) = 0)
    (m : dS) (hm : Ψ m ≠ 0) (S_R ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ((MState.pure (correlatedKet Ψ χ)).traceRight).m m m
      = (Complex.normSq (historyWeight S_R (-Real.log (Complex.normSq (Ψ m))) ℏ) : ℂ) := by
  rw [traceRight_correlatedKet_orthonormal Ψ χ horth, Matrix.diagonal_apply_eq,
    historyWeight_born S_R _ ℏ hℏ, neg_neg, Real.exp_log (Complex.normSq_pos.mpr hm)]

/-- **The coherences carry the record overlap in norm** (Eq. 16, off-diagonal): the magnitude
of each residual coherence is exactly the product of the Born amplitudes and the record
overlap — imperfect records leave exponentially small but nonzero coherences, which is why the
possible ontic states differ from the measurement eigenstates only by exponentially small
redefinitions. -/
theorem traceRight_offdiagonal_norm (Ψ : Ket dS) (χ : dS → Ket dE) (m₁ m₂ : dS) :
    ‖((MState.pure (correlatedKet Ψ χ)).traceRight).m m₁ m₂‖
      = ‖Ψ m₁‖ * ‖Ψ m₂‖ * ‖∑ e, χ m₁ e * conj (χ m₂ e)‖ := by
  rw [traceRight_pure_correlatedKet]
  simp

/-- **Record overlaps factorize over degrees of freedom** (the display before Eq. 17): if the
record states are products over `N` degrees of freedom, the total overlap is the product of the
single-degree overlaps — `⟨E(m₂)|E(m₁)⟩ = Π_k ⟨e_k(m₂)|e_k(m₁)⟩`. -/
theorem recordOverlap_factorizes {N : ℕ} {dof : Type*} [Fintype dof]
    (a₁ a₂ : Fin N → dof → ℂ) :
    ∑ f : Fin N → dof, (∏ k, a₁ k (f k)) * conj (∏ k, a₂ k (f k))
      = ∏ k, ∑ x, a₁ k x * conj (a₂ k x) := by
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun f _ => by
    rw [map_prod, Finset.prod_mul_distrib]

/-- **Exponential suppression of coherences** (Eq. 16's `∼ e^{−N f(γΔt)}`): if every
single-degree-of-freedom overlap is bounded by `e^{−γ}`, the total record overlap is bounded by
`e^{−Nγ}` — decoherence is exponential in the number of degrees of freedom that register the
outcome, which is what renders measurements effectively indivisible and collapse-like. -/
theorem record_overlap_exponential_bound {N : ℕ} (g : Fin N → ℂ) (γ : ℝ)
    (hb : ∀ k, ‖g k‖ ≤ Real.exp (-γ)) :
    ‖∏ k, g k‖ ≤ Real.exp (-(N * γ)) := by
  calc ‖∏ k, g k‖ = ∏ k, ‖g k‖ := norm_prod _ _
    _ ≤ ∏ _k : Fin N, Real.exp (-γ) :=
        Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hb k)
    _ = Real.exp (-γ) ^ N := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = Real.exp (-(N * γ)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-! ## §E — the error–entropy bound (Eq. 23) -/

/-- **The minimum apparatus error is the exponential of minus the maximal entropy** (Eq. 23):
the accuracy of an apparatus is bounded by the number of possible ontic states available to
correlate with the subject system, so its minimum error `1/#` equals `e^{−S_max}` with `S_max`
the Shannon entropy of the uniform (maximal-ignorance) epistemic state — the corrections to
the Born rule sit exactly at this error–entropy floor. -/
theorem minimum_error_eq_exp_neg_maxEntropy (X : Type*) [Fintype X] [Nonempty X] :
    ((Fintype.card X : ℝ))⁻¹ = Real.exp (-Hₛ (ProbDistribution.uniform (α := X))) := by
  rw [Hₛ_uniform, Real.exp_neg, Real.exp_log, Finset.card_univ]
  · rw [Finset.card_univ]
    exact_mod_cast Fintype.card_pos

/-- **The maximal apparatus entropy is extensive** (Eq. 23's `#^{−N} ∼ e^{−S_max}`): an
apparatus of `N` degrees of freedom with `#` ontic states each has `S_max = N · log #` — the
number of possible ontic states is exponential in `N`, so the minimum error is exponentially
small. -/
theorem apparatus_maxEntropy (N : ℕ) (D : Type*) [Fintype D] [Nonempty D] :
    Hₛ (ProbDistribution.uniform (α := Fin N → D)) = N * Real.log (Fintype.card D) := by
  rw [Hₛ_uniform, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [Real.log_pow]

/-! ## §F — the environment-induced Kraus decomposition (Eqs. 30–32) -/

open scoped Kronecker

/-- **The Kraus operators of the environment-induced evolution** (Eq. 32):
`Ê_{ee′}(t) = √(p_e(0)) ⟨e′;0|Û_W(t)|e;0⟩` — the `dS × dS` blocks of the parent unitary
between environment eigenstates, weighted by the square root of the corresponding environment
eigenvalue. The explicit dependence on the environment's initial spectral data
`{p_e(0)}, {|e;0⟩}` is observation (a) of §4.4: the subsystem's evolution map is not intrinsic
to the subsystem. -/
noncomputable def environmentKraus (U : Matrix (dS × dE) (dS × dE) ℂ) (p : dE → ℝ)
    (e e' : dE) : Matrix dS dS ℂ :=
  ((Real.sqrt (p e) : ℝ) : ℂ) • Matrix.of fun i j => U (i, e') (j, e)

omit [DecidableEq dS] in
/-- **Unitary parent dynamics on an uncorrelated start is Kraus-form open dynamics**
(Eqs. 30–31): with the parent initially the product `ρ_S(0) ⊗ ρ_E(0)` and the environment
written in its eigenbasis `ρ_E(0) = Σ_e p_e |e⟩⟨e|` (Eq. 33, here the standard basis), tracing
the environment out of the unitarily conjugated state is exactly the Kraus sum
`Σ_{ee′} Ê_{ee′} ρ_S Ê_{ee′}†` — the paper's derivation that linear CPTP evolution of the
subsystem *emerges* from closed-system unitarity plus initial uncorrelation, rather than being
posited. Generic Kraus existence is `MatrixMap.exists_kraus`; this is the sharper statement
with the paper's explicit environment-indexed operators. -/
theorem environment_kraus_decomposition (U : Matrix (dS × dE) (dS × dE) ℂ)
    (ρS : Matrix dS dS ℂ) (p : dE → ℝ) (hp : ∀ e, 0 ≤ p e) :
    (U * (ρS ⊗ₖ Matrix.diagonal fun e => (p e : ℂ)) * Uᴴ).traceRight
      = ∑ q : dE × dE,
          environmentKraus U p q.1 q.2 * ρS * (environmentKraus U p q.1 q.2)ᴴ := by
  ext i j
  simp only [Matrix.traceRight, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply,
    environmentKraus, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hs : (Real.sqrt (p b) : ℂ) * (Real.sqrt (p b) : ℂ) = (p b : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp b)]
  have hstar : star ((Real.sqrt (p b) : ℝ) : ℂ) = ((Real.sqrt (p b) : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [star_mul', hstar]
  linear_combination (-(U (i, e') (a, b) * ρS a c * star (U (j, e') (c, b)))) * hs

/-! ## §G — subsystem conditionals and the no-entanglement factorization
(Eqs. 44–47, 49–56) -/

/-- **System-centric ontology is consistent** (Eqs. 49–56): the parent-level probability of a
subsystem eigenprojector padded with the identity (Eq. 54) equals the subsystem-level
probability computed from the partial trace — Axiom 3's partial-trace ontology assigns the
same numbers as the parent state, by derivation. Reuse of `Matrix.trace_mul_kron_one_right`. -/
theorem marginal_probability_consistency (ρW : MState (dS × dE)) (T : HermitianMat dS ℂ) :
    ρW.exp_val (T ⊗ₖ (1 : HermitianMat dE ℂ)) = ρW.traceRight.exp_val T := by
  have h1 := exp_val_coe_trace ρW (T ⊗ₖ (1 : HermitianMat dE ℂ))
  have h2 := exp_val_coe_trace ρW.traceRight T
  have key : (ρW.m * (T ⊗ₖ (1 : HermitianMat dE ℂ)).mat).trace
      = (ρW.traceRight.m * T.mat).trace := by
    rw [HermitianMat.kronecker_mat, HermitianMat.mat_one, ← traceRight_m]
    exact Matrix.trace_mul_kron_one_right ρW.m T.mat
  exact_mod_cast h1.trans (key.trans h2.symm)

/-- **The subsystem conditional probability through the parent** (Eq. 44):
`p_{S|W}(s′;t′|w;t) = Tr_W[(P̂_S(s′;t′) ⊗ 1̂_E) ℰ_W{P̂_W(w;t)}]` — when `S` may be entangled
with `E`, the conditional probabilities are defined only through the parent system `W`. -/
noncomputable def subsystemConditionalProb (Λ : CPTPMap (dS × dE) (dS × dE))
    (φ : Ket dS) (ψ : Ket (dS × dE)) : ℝ :=
  (Λ (MState.pure ψ)).exp_val ((MState.pure φ).M ⊗ₖ (1 : HermitianMat dE ℂ))

/-- Eq. 44 computes in the reduced state: `p_{S|W} = Tr_S[P̂_S(s′;t′) ρ̂_S(t′)]` — instance of
`marginal_probability_consistency`. -/
theorem subsystemConditionalProb_eq_reduced (Λ : CPTPMap (dS × dE) (dS × dE))
    (φ : Ket dS) (ψ : Ket (dS × dE)) :
    subsystemConditionalProb Λ φ ψ
      = ((Λ (MState.pure ψ)).traceRight).exp_val (MState.pure φ).M :=
  marginal_probability_consistency _ _

/-- **The no-entanglement factorization** (Eqs. 45–47): when the parent eigenprojector
factorizes, `P̂_W(w;t) = P̂_S(s;t) ⊗ P̂_E(e;t)` (no entanglement at the initial time), the
subsystem conditional probability is computed entirely by the environment-conditioned
evolution `ℰ_{S|E,e}{P̂_S} = Tr_E[ℰ_W{P̂_S ⊗ P̂_E}]` of Eq. 47 — the conditional-probability
formula becomes classical in form, conditioned on the joint initial ontic state `(s, e)`.
Quantum entanglement at the initial time is exactly what blocks this factorization (§4.6). -/
theorem subsystemConditionalProb_factorized (Λ : CPTPMap (dS × dE) (dS × dE))
    (φ φ₀ : Ket dS) (ψE : Ket dE) :
    subsystemConditionalProb Λ φ (φ₀ ⊗ᵠ ψE)
      = ((Λ (MState.pure φ₀ ⊗ᴹ MState.pure ψE)).traceRight).exp_val (MState.pure φ).M := by
  rw [subsystemConditionalProb, MState.pure_prod_pure φ₀ ψE]
  exact marginal_probability_consistency _ _

/-! ## §H — Kraus composition and the coarse-grained trajectory measure (Eqs. 38, 42) -/

/-- **Composed Kraus families are the multi-indexed product family** (Eq. 38): applying two
Kraus sums in succession is the single Kraus sum over operator products. The *semigroup
property* (Eq. 40) — that this composed family reproduce the direct single-interval family —
is an additional, generically false condition (§4.4 observations (b)–(c)); its generic
failure is what blocks an a priori probability measure on the space of *exact* ontic
trajectories. -/
theorem kraus_composition {D κ₁ κ₂ : Type*} [Fintype D] [Fintype κ₁] [Fintype κ₂]
    (E : κ₁ → Matrix D D ℂ) (F : κ₂ → Matrix D D ℂ) (ρ : Matrix D D ℂ) :
    ∑ β, F β * (∑ α, E α * ρ * (E α)ᴴ) * (F β)ᴴ
      = ∑ q : κ₂ × κ₁, F q.1 * E q.2 * ρ * (F q.1 * E q.2)ᴴ := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun α _ => by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Chaining conditional probabilities preserves normalization** (Eq. 42, one step): the
product of two row-normalized transition kernels is row-normalized. -/
theorem chained_conditionals_normalized {N : Type*} [Fintype N] (A B : Matrix N N ℝ)
    (hA : ∀ a, ∑ b, A a b = 1) (hB : ∀ a, ∑ b, B a b = 1) (a : N) :
    ∑ b, (A * B) a b = 1 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  calc ∑ k, ∑ b, A a k * B k b = ∑ k, A a k * ∑ b, B k b := by
        simp [Finset.mul_sum]
    _ = 1 := by simp [hB, hA a]

/-- **The coarse-grained trajectory measure is normalized** (Eq. 42): the probabilities
`p_{{i_n}} = Π_n p(i_n;t_n|i_{n-1};t_{n-1})` assigned to coarse-grained ontic trajectories
multiply into a row-normalized `M`-step kernel, so they sum to one over all trajectories with
a fixed start — a genuine probability measure exists on the *coarse-grained* trajectory
space, in contrast with the exact-trajectory space where the failure of the semigroup
property (Eq. 40) blocks the construction. -/
theorem trajectory_measure_normalized {N : Type*} [Fintype N] [DecidableEq N] :
    ∀ (M : ℕ) (P : Fin M → Matrix N N ℝ), (∀ n a, ∑ b, (P n) a b = 1) →
      ∀ a, ∑ b, (List.ofFn P).prod a b = 1 := by
  intro M
  induction M with
  | zero =>
      intro P _ a
      simp [Matrix.one_apply]
  | succ M ih =>
      intro P hP a
      rw [List.ofFn_succ, List.prod_cons]
      exact chained_conditionals_normalized (P 0) (List.ofFn fun i => P i.succ).prod (hP 0)
        (ih (fun i => P i.succ) (fun n b => hP n.succ b)) a

/-! ## §I — zero-time conditionals and a semigroup-failure witness (Eqs. 37–40)

The two most consequential remaining claims of §4.4. First, Eq. 37's exact core: at zero time
(the identity channel) the quantum conditional probabilities are Kronecker deltas — the anchor
of the §4.7 mechanism by which the conditional probabilities smooth out potential ontic
instabilities. Second, and central to the paper: the semigroup property (Eq. 40) for reduced
dynamics is *generically false*, and here a concrete witness is constructed — partial-swap
dynamics on a pair of qubits. The environment-induced map of the doubled evolution
(`U² = i·SWAP`, a perfect swap, hence the replacement channel) differs from the composition of
the two single-step induced maps, because correlations built up in the first step invalidate
the uncorrelated-start construction of the second. This failure is the paper's stated
obstruction to an a priori probability measure on *exact* ontic trajectories — the source of
the non-probabilistic (Knightian) uncertainty of §4.4–§4.6. -/

/-- **Zero-time conditionals are Kronecker deltas, diagonal case** (Eq. 37, exact core): under
the identity channel the conditional probability from an ontic state to itself is `1`. -/
theorem instantaneous_self (ψ : Ket d) :
    onticConditionalProb CPTPMap.id (MState.pure ψ) ψ = 1 := by
  unfold onticConditionalProb
  rw [CPTPMap.id_MState]
  have h : (MState.pure ψ).exp_val (MState.pure ψ).M
      = (⟪MState.pure ψ, MState.pure ψ⟫_Prob : ℝ) :=
    (MState.val_inner _ _).symm
  rw [h, MState.pure_inner, Braket.dot_self_eq_one]
  simp

/-- **Zero-time conditionals are Kronecker deltas, off-diagonal case** (Eq. 37, exact core):
under the identity channel the conditional probability to any orthogonal ontic state is `0` —
for smooth parent evolution, ontic jumps between orthogonal possibilities are suppressed at
short times. -/
theorem instantaneous_orthogonal (ψ φ : Ket d) (horth : Braket.dot φ ψ = 0) :
    onticConditionalProb CPTPMap.id (MState.pure φ) ψ = 0 := by
  unfold onticConditionalProb
  rw [CPTPMap.id_MState]
  have h : (MState.pure ψ).exp_val (MState.pure φ).M
      = (⟪MState.pure ψ, MState.pure φ⟫_Prob : ℝ) :=
    (MState.val_inner _ _).symm
  have hsymm : Braket.dot ψ φ = 0 := by
    rw [Braket.dot_swap_conj, horth, map_zero]
  rw [h, MState.pure_inner, hsymm]
  simp

section SemigroupFailure

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The swap unitary on `D × D`: `S|a,b⟩ = |b,a⟩`. -/
def swapMatrix (D : Type*) [DecidableEq D] : Matrix (D × D) (D × D) ℂ :=
  Matrix.of fun p q => if Prod.swap p = q then 1 else 0

theorem swapMatrix_mul (M : Matrix (D × D) (D × D) ℂ) :
    swapMatrix D * M = Matrix.of fun p q => M (Prod.swap p) q := by
  ext p q
  simp only [swapMatrix, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq]

theorem mul_swapMatrix (M : Matrix (D × D) (D × D) ℂ) :
    M * swapMatrix D = Matrix.of fun p q => M p (Prod.swap q) := by
  ext p q
  simp only [swapMatrix, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Prod.swap q)]
  · simp
  · intro r _ hr
    have hswap : Prod.swap r ≠ q := fun hc => hr (by rw [← hc, Prod.swap_swap])
    simp [hswap]
  · simp

omit [Fintype D] in
theorem swapMatrix_conjTranspose : (swapMatrix D)ᴴ = swapMatrix D := by
  ext p q
  simp only [Matrix.conjTranspose_apply, swapMatrix, Matrix.of_apply]
  have hiff : Prod.swap q = p ↔ Prod.swap p = q :=
    ⟨fun h => by rw [← h, Prod.swap_swap], fun h => by rw [← h, Prod.swap_swap]⟩
  rw [if_congr hiff rfl rfl]
  split <;> simp

theorem swapMatrix_mul_self : swapMatrix D * swapMatrix D = 1 := by
  rw [swapMatrix_mul]
  ext p q
  simp [swapMatrix, Matrix.one_apply, Prod.swap_swap]

open scoped Kronecker in
/-- Conjugating a Kronecker product by the swap exchanges the tensor factors. -/
theorem swap_conj_kron (A B : Matrix D D ℂ) :
    swapMatrix D * (A ⊗ₖ B) * swapMatrix D = B ⊗ₖ A := by
  rw [swapMatrix_mul, mul_swapMatrix]
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMap_apply, Prod.swap, mul_comm]

open scoped Kronecker in
omit [DecidableEq D] in
/-- The Matrix-level partial trace of a Kronecker product (the `HermitianMat` analogue is
`HermitianMat.traceRight_kron`). -/
theorem traceRight_kronecker (A B : Matrix D D ℂ) :
    (A ⊗ₖ B).traceRight = B.trace • A := by
  ext i j
  simp only [Matrix.traceRight, Matrix.of_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

open scoped Kronecker in
/-- `Tr_E[(A ⊗ B)·S] = A·B` — the swap turns the partial trace into an operator product. -/
theorem traceRight_kron_mul_swap (A B : Matrix D D ℂ) :
    ((A ⊗ₖ B) * swapMatrix D).traceRight = A * B := by
  rw [mul_swapMatrix]
  ext i j
  simp [Matrix.traceRight, Matrix.kroneckerMap_apply, Matrix.mul_apply, Prod.swap]

open scoped Kronecker in
/-- `Tr_E[S·(A ⊗ B)] = B·A`. -/
theorem traceRight_swap_mul_kron (A B : Matrix D D ℂ) :
    (swapMatrix D * (A ⊗ₖ B)).traceRight = B * A := by
  rw [swapMatrix_mul]
  ext i j
  simp [Matrix.traceRight, Matrix.kroneckerMap_apply, Matrix.mul_apply, Prod.swap, mul_comm]

open scoped Kronecker in
/-- **The environment-induced reduced dynamics** (Eq. 43's construction at a pure environment
start `|g⟩⟨g|`): evolve the uncorrelated product by the parent matrix `V`, trace the
environment out — the concrete carrier of `ℰ_S^{t←0}`, matching §F's
`environment_kraus_decomposition` at `p = δ_g`. -/
noncomputable def reducedDynamics (g : D) (V : Matrix (D × D) (D × D) ℂ)
    (ρ : Matrix D D ℂ) : Matrix D D ℂ :=
  (V * (ρ ⊗ₖ Matrix.single g g 1) * Vᴴ).traceRight

/-- The unnormalized partial-swap generator `1 + i·SWAP` (of norm `√2`). -/
def swapUnit (D : Type*) [DecidableEq D] : Matrix (D × D) (D × D) ℂ :=
  1 + Complex.I • swapMatrix D

/-- **The partial-swap parent unitary** `U = (1 + i·SWAP)/√2` — the closed two-qubit dynamics
whose reduced evolution witnesses the failure of the semigroup property. -/
noncomputable def partialSwap (D : Type*) [DecidableEq D] : Matrix (D × D) (D × D) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • swapUnit D

theorem partialSwap_scalar_sq :
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) = 2⁻¹ := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem swapUnit_sq : swapUnit D * swapUnit D = (2 * Complex.I) • swapMatrix D := by
  unfold swapUnit
  simp only [Matrix.add_mul, Matrix.mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
    Matrix.mul_one, swapMatrix_mul_self]
  match_scalars
  · linear_combination Complex.I_sq
  · ring1

/-- The doubled partial swap is the perfect swap: `U² = i·SWAP`. -/
theorem partialSwap_sq : partialSwap D * partialSwap D = Complex.I • swapMatrix D := by
  unfold partialSwap
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, swapUnit_sq, smul_smul,
    partialSwap_scalar_sq, show ((2⁻¹ : ℂ) * (2 * Complex.I)) = Complex.I by ring]

omit [Fintype D] in
theorem swapUnit_conjTranspose : (swapUnit D)ᴴ = 1 - Complex.I • swapMatrix D := by
  unfold swapUnit
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    swapMatrix_conjTranspose, Complex.star_def, Complex.conj_I]
  module

open scoped Kronecker in
/-- **The reduced partial-swap dynamics in closed form**:
`ℰ{ρ} = ½(ρ + Tr(ρ)·P_g + i[P_g, ρ])` — the exact single-step environment-induced map of the
partial swap. -/
theorem reducedDynamics_partialSwap (g : D) (ρ : Matrix D D ℂ) :
    reducedDynamics g (partialSwap D) ρ
      = (2⁻¹ : ℂ) • ρ + ((2⁻¹ : ℂ) * ρ.trace) • Matrix.single g g 1
        + ((2⁻¹ : ℂ) * Complex.I) • (Matrix.single g g 1 * ρ)
        - ((2⁻¹ : ℂ) * Complex.I) • (ρ * Matrix.single g g 1) := by
  have hexp : swapUnit D * (ρ ⊗ₖ Matrix.single g g 1) * (swapUnit D)ᴴ
      = (ρ ⊗ₖ Matrix.single g g 1)
        + Complex.I • (swapMatrix D * (ρ ⊗ₖ Matrix.single g g 1))
        - Complex.I • ((ρ ⊗ₖ Matrix.single g g 1) * swapMatrix D)
        + swapMatrix D * (ρ ⊗ₖ Matrix.single g g 1) * swapMatrix D := by
    rw [swapUnit_conjTranspose]
    unfold swapUnit
    simp only [Matrix.add_mul, Matrix.mul_sub,
      smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
    match_scalars <;> (first | ring1 | linear_combination -Complex.I_sq)
  unfold reducedDynamics partialSwap
  rw [Matrix.conjTranspose_smul, show star ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ))
      = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) from Complex.conj_ofReal _,
    smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
    partialSwap_scalar_sq, hexp, swap_conj_kron,
    Matrix.traceRight_smul, Matrix.traceRight_add, Matrix.traceRight_sub,
    Matrix.traceRight_add, Matrix.traceRight_smul, Matrix.traceRight_smul,
    traceRight_kronecker, traceRight_kronecker, traceRight_swap_mul_kron,
    traceRight_kron_mul_swap, Matrix.trace_single_eq_same, one_smul]
  module

/-- **The semigroup property fails: a concrete witness** (Eqs. 38–40). For the partial-swap
dynamics of a qubit pair with the environment starting in `|0⟩⟨0|` and the system in
`|1⟩⟨1|`, composing the two single-step reduced maps gives `¼|1⟩⟨1| + ¾|0⟩⟨0|`, while the
directly-induced map of the doubled unitary (a perfect swap, hence the replacement channel)
gives `|0⟩⟨0|` — Eq. 40 is violated. The correlations built up in the first step invalidate
the uncorrelated-start construction of the second, which is the paper's stated obstruction to
an a priori probability measure on exact ontic trajectories (§4.4 observations (b)–(c)) and
the origin of the non-probabilistic uncertainty over them. -/
theorem semigroup_property_fails :
    reducedDynamics (0 : Fin 2) (partialSwap (Fin 2))
        (reducedDynamics 0 (partialSwap (Fin 2)) (Matrix.single 1 1 1))
      ≠ reducedDynamics 0 (partialSwap (Fin 2) * partialSwap (Fin 2))
          (Matrix.single 1 1 1) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hP10 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
      * Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := h01.symm)]
  have hP01 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := h01)]
  have hP00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      * Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      = Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) := by
    rw [Matrix.single_mul_single_same, one_mul]
  -- the first step: ℰ{|1⟩⟨1|} = ½|1⟩⟨1| + ½|0⟩⟨0|
  have step1 : reducedDynamics (0 : Fin 2) (partialSwap (Fin 2)) (Matrix.single 1 1 1)
      = (2⁻¹ : ℂ) • Matrix.single 1 1 1 + (2⁻¹ : ℂ) • Matrix.single 0 0 1 := by
    rw [reducedDynamics_partialSwap, Matrix.trace_single_eq_same, hP10, hP01]
    module
  -- the fixed point: ℰ{|0⟩⟨0|} = |0⟩⟨0|
  have step0 : reducedDynamics (0 : Fin 2) (partialSwap (Fin 2)) (Matrix.single 0 0 1)
      = Matrix.single 0 0 1 := by
    rw [reducedDynamics_partialSwap, Matrix.trace_single_eq_same, hP00]
    module
  -- linearity of the reduced dynamics in the state
  have hsmul : ∀ (a : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ),
      reducedDynamics (0 : Fin 2) (partialSwap (Fin 2)) (a • M)
        = a • reducedDynamics 0 (partialSwap (Fin 2)) M := by
    intro a M
    unfold reducedDynamics
    rw [Matrix.smul_kronecker, mul_smul_comm, smul_mul_assoc, Matrix.traceRight_smul]
  have hadd : ∀ M N : Matrix (Fin 2) (Fin 2) ℂ,
      reducedDynamics (0 : Fin 2) (partialSwap (Fin 2)) (M + N)
        = reducedDynamics 0 (partialSwap (Fin 2)) M
          + reducedDynamics 0 (partialSwap (Fin 2)) N := by
    intro M N
    unfold reducedDynamics
    rw [Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul, Matrix.traceRight_add]
  -- the direct doubled map: perfect swap = replacement channel onto |0⟩⟨0|
  have direct : reducedDynamics (0 : Fin 2) (partialSwap (Fin 2) * partialSwap (Fin 2))
      (Matrix.single 1 1 1) = Matrix.single 0 0 1 := by
    unfold reducedDynamics
    rw [partialSwap_sq, Matrix.conjTranspose_smul, swapMatrix_conjTranspose,
      Complex.star_def, Complex.conj_I, smul_mul_assoc, mul_smul_comm,
      smul_mul_assoc, smul_smul,
      show -Complex.I * Complex.I = 1 by
        rw [neg_mul, Complex.I_mul_I, neg_neg],
      one_smul, swap_conj_kron, traceRight_kronecker, Matrix.trace_single_eq_same,
      one_smul]
  intro h
  rw [step1, hadd, hsmul, hsmul, step1, step0, direct] at h
  have h11 := congrFun (congrFun h 1) 1
  simp [h01] at h11

/-! ## §J — the subsystem state does not determine subsystem dynamics (§4.6, Eqs. 43, 48)

The paper's remaining central claim: in the presence of initial system–environment
correlations, the evolved reduced state `ρ_S(t′) = Tr_E[ℰ_W{ρ̂_W(t)}]` is "not generically a
linear (or even an analytic) function of the density matrix of the subsystem" (Eq. 43) — in
fact it is not a *function* of `ρ_S(t)` at all. Witness: two parent states with *identical*
reduced states — one uncorrelated, one correlated — evolve under the *same* parent unitary
(the swap) to *different* reduced states. Notably the correlated witness is only classically
correlated (separable), so the obstruction to well-defined subsystem dynamics already appears
for classical correlations; entanglement makes it uniquely quantum and, per §4.6, obstructs
even the definition of the quantum conditional probabilities. This is why subsystem ontic
dynamics can be completely hidden (Eq. 48's discussion and footnote 15). -/

open scoped Kronecker in
/-- The uncorrelated parent state `½·1_S ⊗ |0⟩⟨0|_E`: system maximally mixed, environment in
its ground state. Positive-semidefinite by construction (projectors and the identity with
nonnegative weights); unit trace by `witness_traces`. -/
noncomputable def uncorrelatedWitness : Matrix ((Fin 2) × (Fin 2)) ((Fin 2) × (Fin 2)) ℂ :=
  (2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Matrix.single 0 0 1)

open scoped Kronecker in
/-- The classically correlated parent state `½(|00⟩⟨00| + |11⟩⟨11|)` — separable, with the
same maximally mixed system marginal as `uncorrelatedWitness`. -/
noncomputable def correlatedWitness : Matrix ((Fin 2) × (Fin 2)) ((Fin 2) × (Fin 2)) ℂ :=
  (2⁻¹ : ℂ) • (Matrix.single 0 0 1 ⊗ₖ Matrix.single 0 0 1
    + Matrix.single 1 1 1 ⊗ₖ Matrix.single 1 1 1)

/-- The two qubit basis projectors resolve the identity. -/
theorem single_add_single_eq_one :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      + Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Both witnesses are unit-trace (they are genuine density matrices). -/
theorem witness_traces :
    uncorrelatedWitness.trace = 1 ∧ correlatedWitness.trace = 1 := by
  constructor
  · rw [uncorrelatedWitness, Matrix.trace_smul, Matrix.trace_kronecker,
      Matrix.trace_single_eq_same, Matrix.trace_one]
    simp
  · rw [correlatedWitness, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_kronecker,
      Matrix.trace_kronecker, Matrix.trace_single_eq_same]
    norm_num

/-- **The subsystem state does not determine the evolved subsystem state** (§4.6, Eq. 43):
the uncorrelated and the classically correlated parent states have *identical* reduced
states (the maximally mixed qubit), yet conjugating both by the *same* parent unitary — the
swap — yields *different* reduced states (`|0⟩⟨0|` versus maximally mixed). Hence no map on
subsystem density matrices, linear or otherwise, describes open-subsystem dynamics in the
presence of initial correlations: the parent's correlation operator (§C) carries dynamical
information invisible to the subsystem, which is exactly why the actual ontic trajectory of a
correlated subsystem is hidden. -/
theorem reduced_state_does_not_determine_dynamics :
    uncorrelatedWitness.traceRight = correlatedWitness.traceRight
      ∧ (swapMatrix (Fin 2) * uncorrelatedWitness * swapMatrix (Fin 2)).traceRight
        ≠ (swapMatrix (Fin 2) * correlatedWitness * swapMatrix (Fin 2)).traceRight := by
  have hmarg1 : uncorrelatedWitness.traceRight
      = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [uncorrelatedWitness, Matrix.traceRight_smul, traceRight_kronecker,
      Matrix.trace_single_eq_same, one_smul]
  have hmarg2 : correlatedWitness.traceRight
      = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [correlatedWitness, Matrix.traceRight_smul, Matrix.traceRight_add,
      traceRight_kronecker, traceRight_kronecker, Matrix.trace_single_eq_same,
      Matrix.trace_single_eq_same, one_smul, one_smul, single_add_single_eq_one]
  refine ⟨hmarg1.trans hmarg2.symm, ?_⟩
  have hev1 : (swapMatrix (Fin 2) * uncorrelatedWitness * swapMatrix (Fin 2)).traceRight
      = Matrix.single (0 : Fin 2) 0 (1 : ℂ) := by
    rw [uncorrelatedWitness, mul_smul_comm, smul_mul_assoc, swap_conj_kron,
      Matrix.traceRight_smul, traceRight_kronecker, Matrix.trace_one, smul_smul,
      show ((2⁻¹ : ℂ) * (Fintype.card (Fin 2) : ℂ)) = 1 by
        norm_num [Fintype.card_fin],
      one_smul]
  have hev2 : (swapMatrix (Fin 2) * correlatedWitness * swapMatrix (Fin 2)).traceRight
      = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [correlatedWitness, mul_smul_comm, smul_mul_assoc,
      Matrix.mul_add, Matrix.add_mul, swap_conj_kron, swap_conj_kron,
      Matrix.traceRight_smul, Matrix.traceRight_add, traceRight_kronecker,
      traceRight_kronecker, Matrix.trace_single_eq_same, Matrix.trace_single_eq_same,
      one_smul, one_smul, single_add_single_eq_one]
  rw [hev1, hev2]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00

end SemigroupFailure

end Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics
