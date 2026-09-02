/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.BornCompositionCorrelation
public import QuantumInfo.States.Pure.Braket
public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.ClassicalInfo.Distribution
meta import Zil

/-!
# Normalized Ket adapter

A thin bridge, not a structural merger: a unit-norm finite ℓ² state
(`lp (fun _ : Fin m => ℂ) 2`, the arbitrary-index `ℓ²` carrier restricted to a finite
index) is carried to a QuantumInfo `Ket m`, the normalized-vector carrier the
finite quantum-information layer already reasons on.  The adapter keeps the two
carriers distinct — it does not identify `ℓ²` with the `Ket`/`MState` formalism —
and it is Born-faithful: the Born boundary `bornDist` equals the Ket's
Born weights.  Any Ket-level property (entanglement, no-signalling, cloning
bounds) therefore transfers to the adapted ℓ² state without rewriting the
ℓ² state through the Ket type.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.L2KetAdapter

open Physlib.QuantumMechanics.KoopmanQuantization
open Physlib.QuantumMechanics.BornCompositionCorrelation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock

/-- **The normalized Ket adapter**: a unit-norm finite ℓ² state is a
QuantumInfo `Ket`, carrying the same amplitudes.  The normalization condition is
the Born boundary summing to one. -/
def ketOfL2State {m : Type*} [Fintype m] (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) : Ket m where
  vec := (ψ : m → ℂ)
  normalized' := by
    have hb := bornDist_sum_one_of_norm_one ψ h
    unfold bornDist at hb
    exact hb

@[simp, zil_level structural] theorem ketOfL2State_apply {m : Type*} [Fintype m] (ψ : lp (fun _ : m => ℂ) 2)
    (h : ‖ψ‖ = 1) (i : m) :
    (ketOfL2State ψ h) i = (ψ : m → ℂ) i :=
  rfl

/-- **The adapter is Born-faithful**: the Ket's Born weights are exactly the
ℓ² state's Born boundary. -/
@[zil_level structural]
theorem bornDist_eq_ketBorn {m : Type*} [Fintype m] (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) :
    bornDist ψ = fun i => ‖(ketOfL2State ψ h) i‖ ^ 2 :=
  rfl

/-! ## The bridge is an equivalence: Ket → normalized ℓ² state

The adapter has an inverse, so on a finite index the normalized ℓ² states
and the Kets are the same objects up to the presentation map — a proved
equivalence, not an analogy. -/

/-- Ket → ℓ² state: the inverse presentation map. -/
def l2OfKet {m : Type*} [Fintype m] [DecidableEq m] (k : Ket m) : lp (fun _ : m => ℂ) 2 :=
  l2OfFun k.vec

theorem l2OfKet_coe {m : Type*} [Fintype m] [DecidableEq m] (k : Ket m) (j : m) :
    ((l2OfKet k : lp (fun _ : m => ℂ) 2) : m → ℂ) j = k.vec j :=
  l2OfFun_coe k.vec j

theorem l2OfKet_norm_one {m : Type*} [Fintype m] [DecidableEq m] (k : Ket m) :
    ‖l2OfKet k‖ = 1 := by
  have hsq : ‖l2OfKet k‖ ^ 2 = 1 := by
    rw [← bornDist_sum_eq_normSq]
    have hb : ∀ i, bornDist (l2OfKet k) i = ‖k.vec i‖ ^ 2 := by
      intro i; unfold bornDist; rw [l2OfKet_coe]
    rw [Finset.sum_congr rfl fun i _ => hb i]
    exact k.normalized'
  nlinarith [norm_nonneg (l2OfKet k), hsq]

/-- **Round trip Ket → state → Ket** is the identity. -/
@[zil_level bridge_theorem]
theorem ketOfL2State_l2OfKet {m : Type*} [Fintype m] [DecidableEq m] (k : Ket m) :
    ketOfL2State (l2OfKet k) (l2OfKet_norm_one k) = k := by
  apply Ket.ext
  intro i
  rw [ketOfL2State_apply, l2OfKet_coe, Ket.apply]

/-- **Round trip state → Ket → state** is the identity. -/
@[zil_level bridge_theorem]
theorem l2OfKet_ketOfL2State {m : Type*} [Fintype m] [DecidableEq m] (ψ : lp (fun _ : m => ℂ) 2)
    (h : ‖ψ‖ = 1) : l2OfKet (ketOfL2State ψ h) = ψ := by
  apply lp.ext
  funext i
  rw [l2OfKet_coe]
  rfl

/-! ## The density-operator presentation and three-way Born agreement -/

/-- The density-operator presentation of a normalized ℓ² state. -/
noncomputable def pureOfL2State {m : Type*} [Fintype m] [DecidableEq m]
    (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) : MState m :=
  MState.pure (ketOfL2State ψ h)

/-- **Three-way Born agreement**: the Born boundary equals both the Ket
Born weights (`bornDist_eq_ketBorn`) and the density-operator diagonal.  The three
presentations carry the same probabilities. -/
@[zil_level bridge_theorem]
theorem bornDist_eq_pure_diagonal {m : Type*} [Fintype m] [DecidableEq m]
    (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) (i : m) :
    bornDist ψ i = ((pureOfL2State ψ h).m i i).re := by
  unfold pureOfL2State bornDist
  rw [MState.pure_apply, ketOfL2State_apply, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-! ## Classical correlation is not entanglement

Classical total correlation of a Born distribution and quantum entanglement are
distinct.  They meet only through purity: a *product* (unentangled) pure state
has zero classical Born-correlation, so positive total correlation of a pure
state's Born boundary implies the state is entangled — the implication holds
because the state is pure, and does not identify the two notions. -/

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock in
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality in
/-- **A product pure state has zero classical Born-correlation.** -/
@[zil_level bridge_theorem]
theorem ket_isProd_totalCorrelation_zero {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    (k : Ket (d₁ × d₂)) (hp : k.IsProd) :
    totalCorrelation (fun z => ‖(k : d₁ × d₂ → ℂ) z‖ ^ 2) = 0 := by
  obtain ⟨ξ, φ, rfl⟩ := hp
  have hfun : (fun z : d₁ × d₂ => ‖((ξ ⊗ᵠ φ) : d₁ × d₂ → ℂ) z‖ ^ 2)
            = (fun z => ‖ξ.vec z.1‖ ^ 2 * ‖φ.vec z.2‖ ^ 2) := by
    funext z
    obtain ⟨i, j⟩ := z
    show ‖((ξ ⊗ᵠ φ) : d₁ × d₂ → ℂ) (i, j)‖ ^ 2 = ‖ξ.vec i‖ ^ 2 * ‖φ.vec j‖ ^ 2
    rw [show ((ξ ⊗ᵠ φ) : d₁ × d₂ → ℂ) (i, j) = ξ.vec i * φ.vec j from rfl, norm_mul, mul_pow]
  rw [hfun]
  apply totalCorrelation_eq_zero_of_independent
  intro z
  have hmF : marginalFst (fun z : d₁ × d₂ => ‖ξ.vec z.1‖ ^ 2 * ‖φ.vec z.2‖ ^ 2) z.1
           = ‖ξ.vec z.1‖ ^ 2 := by
    unfold marginalFst
    simp only []
    rw [← Finset.mul_sum, φ.normalized', mul_one]
  have hmS : marginalSnd (fun z : d₁ × d₂ => ‖ξ.vec z.1‖ ^ 2 * ‖φ.vec z.2‖ ^ 2) z.2
           = ‖φ.vec z.2‖ ^ 2 := by
    unfold marginalSnd
    simp only []
    rw [← Finset.sum_mul, ξ.normalized', one_mul]
  rw [hmF, hmS]

theorem demoJoint_sum_one : ∑ z : ZMod 2 × ZMod 2, demoJoint z = 1 := by
  rw [Fintype.sum_prod_type, sum_zmod_two (fun i => ∑ j : ZMod 2, demoJoint (i, j)),
    sum_zmod_two (fun j => demoJoint (0, j)), sum_zmod_two (fun j => demoJoint (1, j))]
  simp only [demoJoint, demoF_val, demoG_zero, demoG_one]
  norm_num

theorem stateOfDemo_norm_one : ‖stateOfDist demoJoint‖ = 1 := by
  have hsq : ‖stateOfDist demoJoint‖ ^ 2 = 1 := by
    rw [← bornDist_sum_eq_normSq, stateOfDemo_bornDist, demoJoint_sum_one]
  nlinarith [norm_nonneg (stateOfDist demoJoint), hsq]

theorem coupledOutput_norm_one :
    ‖koopmanStateStep (coupleShear 2) (stateOfDist demoJoint)‖ = 1 := by
  rw [(koopmanStateStep (coupleShear 2)).norm_map, stateOfDemo_norm_one]

/-- **The coupled output is genuinely quantum-entangled** — separately proved, not
identified with the classical correlation.  Because the state is pure and its
classical Born-correlation is positive (`coupling_generates_correlation`), it
cannot be a product Ket, so it is entangled. -/
@[zil_level bridge_theorem]
theorem coupledOutput_ketEntangled :
    (ketOfL2State (koopmanStateStep (coupleShear 2) (stateOfDist demoJoint))
      coupledOutput_norm_one).IsEntangled := by
  intro hp
  have hz := ket_isProd_totalCorrelation_zero _ hp
  rw [← bornDist_eq_ketBorn (koopmanStateStep (coupleShear 2) (stateOfDist demoJoint))
    coupledOutput_norm_one, coupled_bornDist] at hz
  linarith [totalCorrelation_shearDemo_pos, hz]

zil attach ketOfL2State_apply where
  formalizes @ "claim:the-normalized-ket-adapter-carries-a-unit-norm-finite-l2-state-to-a-ket-with-the-same-amplitudes",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.bornDist_sum_one_of_norm_one",
  epistemic_status @ "consistency-identity"

zil attach bornDist_eq_ketBorn where
  formalizes @ "claim:the-ket-adapter-is-born-faithful-the-ket-born-weights-are-the-born-boundary",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.bornDist",
  epistemic_status @ "consistency-identity"

zil attach ketOfL2State_l2OfKet where
  formalizes @ "claim:the-ket-to-l2-state-map-is-a-right-inverse-of-the-adapter-the-two-carriers-represent-the-same-normalized-states",
  represents @ "lean:Physlib.QuantumMechanics.L2KetAdapter.l2OfKet",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.l2OfKet"

zil attach l2OfKet_ketOfL2State where
  formalizes @ "claim:the-adapter-is-a-left-inverse-completing-the-finite-normalized-l2-ket-equivalence",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State"

zil attach bornDist_eq_pure_diagonal where
  formalizes @ "claim:the-three-presentations-preserve-probability-the-born-boundary-equals-the-density-operator-diagonal",
  preserves_probability @ "lean:Physlib.QuantumMechanics.L2KetAdapter.pureOfL2State",
  supported_by @ "lean:MState.pure_apply"

/-! ## Step 5: the evolution intertwines the presentations

The Koopman step, the Ket relabeling, and the density-operator
conjugation are the same evolution seen through the three presentations: the
bridges commute with the dynamics. -/

/-- The Ket relabeling induced by an index bijection — the Koopman step seen on
the Ket presentation. -/
def ketRelabel {m : Type*} [Fintype m] (σ : m ≃ m) (k : Ket m) : Ket m where
  vec := fun i => k.vec (σ.symm i)
  normalized' := by
    rw [Equiv.sum_comp σ.symm (fun i => ‖k.vec i‖ ^ 2)]
    exact k.normalized'

/-- **The adapter intertwines the Koopman step with the Ket relabeling**: the
ℓ² evolution and the Ket evolution are one map through the bridge. -/
@[zil_level bridge_theorem]
theorem ketOfL2State_koopman {m : Type*} [Fintype m] [DecidableEq m] (σ : m ≃ m)
    (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) :
    ketOfL2State (koopmanStateStep σ ψ)
        (by rw [(koopmanStateStep σ).norm_map]; exact h)
      = ketRelabel σ (ketOfL2State ψ h) := by
  apply Ket.ext
  intro i
  rw [ketOfL2State_apply, koopmanStateStep_apply]
  rfl

/-- **The evolution also intertwines the density-operator presentation**. -/
@[zil_level bridge_theorem]
theorem pureOfL2State_koopman {m : Type*} [Fintype m] [DecidableEq m] (σ : m ≃ m)
    (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) :
    pureOfL2State (koopmanStateStep σ ψ)
        (by rw [(koopmanStateStep σ).norm_map]; exact h)
      = MState.pure (ketRelabel σ (ketOfL2State ψ h)) := by
  unfold pureOfL2State
  rw [ketOfL2State_koopman]

/-! ## Step 6: the classical correlation is the diagonal measurement

The classical total correlation is not a separate object bolted onto the state:
it is the total correlation of the density operator's diagonal (computational-basis)
measurement. -/

/-- The diagonal (computational-basis) measurement of a density operator — the
classical distribution it induces. -/
def diagonalMeasurement {m : Type*} [Fintype m] [DecidableEq m] (ρ : MState m) : m → ℝ :=
  fun i => (ρ.m i i).re

/-- **The Born boundary is the diagonal measurement of the density
operator.** -/
theorem diagonalMeasurement_pureOfL2State {m : Type*} [Fintype m] [DecidableEq m]
    (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) :
    diagonalMeasurement (pureOfL2State ψ h) = bornDist ψ := by
  funext i
  exact (bornDist_eq_pure_diagonal ψ h i).symm

/-- **The generated classical correlation is the diagonal measurement of the
quantum state**: for the coupled output the positive total correlation is exactly
the total correlation of the density operator's diagonal measurement. -/
@[zil_level bridge_theorem]
theorem coupling_correlation_is_diagonalMeasurement :
    0 < totalCorrelation (diagonalMeasurement (pureOfL2State
      (koopmanStateStep (coupleShear 2) (stateOfDist demoJoint))
      coupledOutput_norm_one)) := by
  rw [diagonalMeasurement_pureOfL2State]
  exact coupling_generates_correlation

/-! ## The Born output as a probability distribution

The normalized state's Born output is packaged as an actual `ProbDistribution`,
carrying nonnegativity and normalization internally, rather than a raw function
with external proofs. -/

/-- **The Born distribution of a normalized state as a `ProbDistribution`.** -/
def bornProbDistribution {ι : Type*} [Fintype ι] (ψ : lp (fun _ : ι => ℂ) 2) (h : ‖ψ‖ = 1) :
    ProbDistribution ι :=
  ProbDistribution.mk' (bornDist ψ) (bornDist_nonneg ψ) (bornDist_sum_one_of_norm_one ψ h)

@[simp] theorem bornProbDistribution_apply {ι : Type*} [Fintype ι] (ψ : lp (fun _ : ι => ℂ) 2)
    (h : ‖ψ‖ = 1) (i : ι) :
    ((bornProbDistribution ψ h i : Prob) : ℝ) = bornDist ψ i :=
  rfl

/-- **The density operator's diagonal measurement as a `ProbDistribution`.** -/
def diagonalProbDistribution {m : Type*} [Fintype m] [DecidableEq m]
    (ψ : lp (fun _ : m => ℂ) 2) (h : ‖ψ‖ = 1) : ProbDistribution m :=
  ProbDistribution.mk' (diagonalMeasurement (pureOfL2State ψ h))
    (fun i => (diagonalMeasurement_pureOfL2State ψ h ▸ bornDist_nonneg ψ) i)
    (by rw [diagonalMeasurement_pureOfL2State]; exact bornDist_sum_one_of_norm_one ψ h)

zil attach ket_isProd_totalCorrelation_zero where
  formalizes @ "claim:a-product-pure-state-has-zero-classical-born-correlation-so-classical-correlation-is-not-entanglement",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.bornDist_eq_ketBorn"

zil attach coupledOutput_ketEntangled where
  formalizes @ "claim:the-coupled-output-is-separately-proved-quantum-entangled-derived-from-positive-classical-correlation-of-a-pure-state",
  supported_by @ "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.coupling_generates_correlation",
  caveat @ "claim:the-implication-classical-correlation-to-entanglement-holds-only-because-the-state-is-pure-not-in-general"

zil attach ketOfL2State_koopman where
  formalizes @ "claim:the-adapter-intertwines-the-koopman-step-with-the-ket-relabeling-so-the-evolution-is-one-map-across-presentations",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.ketRelabel"

zil attach coupling_correlation_is_diagonalMeasurement where
  formalizes @ "claim:the-generated-classical-total-correlation-is-the-diagonal-measurement-of-the-quantum-density-operator",
  supported_by @ "lean:Physlib.QuantumMechanics.L2KetAdapter.diagonalMeasurement_pureOfL2State"

zil_file_contract physlib.l2KetAdapter where
  promises "A thin bridge from the finite ℓ² carrier to the QuantumInfo Ket carrier: a unit-norm state is carried to a Ket with the same amplitudes, and the adapter is Born-faithful so the Born boundary equals the Ket Born weights. The bridge keeps the two carriers distinct and does not rewrite the ℓ² state through the Ket or MState formalism. The bridge is a proved equivalence with both round trips, and it extends to the density-operator presentation MState.pure with three-way Born-probability agreement, so the l2, Ket, and density-operator carriers demonstrably represent the same normalized states."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.bornDist",
    "lean:Physlib.QuantumMechanics.BornCompositionCorrelation.bornDist_sum_one_of_norm_one"
  ]
  forbids_substitutes [
    "identifying the ℓ² carrier with the Ket or MState formalism",
    "claiming a general nonfinite or unnormalized adapter",
    "promoting the Born-faithful bridge to a full density-operator functor"
  ]
  witnessed_by [
    ketOfL2State_apply,
    bornDist_eq_ketBorn,
    ketOfL2State_l2OfKet,
    l2OfKet_ketOfL2State,
    bornDist_eq_pure_diagonal,
    ket_isProd_totalCorrelation_zero,
    coupledOutput_ketEntangled,
    ketOfL2State_koopman,
    pureOfL2State_koopman,
    coupling_correlation_is_diagonalMeasurement
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.l2KetAdapter

end Physlib.QuantumMechanics.L2KetAdapter
