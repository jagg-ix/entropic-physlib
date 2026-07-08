/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.BoltzmannHTheorem
public import Physlib.Thermodynamics.Landauer
public import Mathlib.Computability.PartrecCode
public import QuantumInfo.States.Pure.Qubit

/-!
# Thermodynamics of computation: Landauer cost of partial recursive functions

This module connects the reversible / coarse-graining dichotomy of
`Physlib.Thermodynamics.BoltzmannHTheorem` to the formalisation of computability
via partial recursive functions (Mathlib's `Computability.PartrecCode`, after
M. Carneiro, *Formalizing computability theory via partial recursive
functions*, ITP 2019).

## The basis splits along the reversible / irreversible line

Carneiro's `Nat.Partrec.Code` has eight primitives, and their `eval` semantics
fall cleanly into two classes:

* **Information-preserving** (injective `eval`):
  `succ` (`Nat.succ`), `pair` (the bijection `Nat.pairEquiv : ℕ × ℕ ≃ ℕ`),
  and `id = pair left right` (`n ↦ n`).
* **Information-discarding** (non-injective `eval`):
  `zero` (the constant `0`), `left` (`n ↦ (unpair n).1`), `right`
  (`n ↦ (unpair n).2`) — each projection erases the half the other keeps.

`succ_injective`, `pair_injective`, `left_not_injective`, `const_not_injective`
record this split as theorems.

## Reversible computation produces no entropy (Bennett)

The physically correct statement is Bennett's: *any* computation is reversible
if it retains its input. The joint `(input, output)` measure is
`μ ⊗ₘ Kernel.deterministic (eval c)`, supported on the graph `{(x, f x)}` — an
injective image of the input — so its relative entropy equals that of the input:

  `klDiv (μ ⊗ₘ κ_f) (ν ⊗ₘ κ_f) = klDiv μ ν`   (`computation_keeps_kl`),

a direct instance of `klDiv_reversible_invariant`. Retaining the input is the
same channel on both sides; there is nothing to dissipate.

## Irreversibility is the erasure of the input register (Landauer)

The cost appears only when the input register is discarded. Discarding the
input and resetting it to a fixed reference is a `CoarseGrainingStep` whose
reversible channel is the computation `κ_f` and whose equilibrium channel `η`
resets to a constant. The dissipated relative entropy
(`CoarseGrainingStep.tauEnt`) is then exactly the conditional KL — the erased
information — and is non-negative by the H-theorem (`tauEnt_nonneg`), with the
numeric floor `k_B · log 2` per erased bit supplied by
`Physlib.Thermodynamics.Landauer.reservoir_entropy_advance_ge_one_bit`.

## The three layers, kept separate

1. **Pure math (Lean-provable):** injective `eval c` ⇒ KL preserved; the
   erasure step is a coarse-graining with non-negative dissipation. No physics.
2. **Operational identification:** erased bits ↔ heat to the bath — the Landauer
   erasure model (already a theorem in `Landauer.lean`, not re-assumed here).
3. **Physical claim:** irreversible computation costs ≥ `k_B · T · log 2` per
   erased bit (Landauer's principle).

Refuting the (1)↔(3) identification leaves the layer-1 theorems untouched.

## Origin and references

* R. Landauer, *Irreversibility and heat generation in the computing process*,
  IBM J. Res. Dev. **5** (1961) 183.
* C. H. Bennett, *Logical reversibility of computation*, IBM J. Res. Dev.
  **17** (1973) 525.
* M. Carneiro, *Formalizing computability theory via partial recursive
  functions*, ITP 2019 (the basis for `Mathlib.Computability.PartrecCode`).

This is an independent Lean formalisation; it does not depend on any external
project.
-/

set_option autoImplicit false

namespace Physlib.Thermodynamics.ComputationLandauer

open MeasureTheory ProbabilityTheory InformationTheory
open Physlib.Thermodynamics.BoltzmannHTheorem
open scoped ENNReal

@[expose] public section

/-! ## §1 — Codes as measurable functions

`ℕ` includes the discrete σ-algebra, so every `ℕ → ℕ` — in particular every total
`Nat.Partrec.Code.eval` — is measurable, and lifts to a Markov kernel via
`Kernel.deterministic`. -/

/-- Every function on the discrete space `ℕ` is measurable. -/
theorem measurable_natFun (f : ℕ → ℕ) : Measurable f := measurable_of_countable f

/-- The deterministic kernel of a computable function: the computation viewed as
a (degenerate) Markov channel `x ↦ δ_{f x}`. -/
noncomputable def computationKernel (f : ℕ → ℕ) : Kernel ℕ ℕ :=
  Kernel.deterministic f (measurable_natFun f)

instance (f : ℕ → ℕ) : IsMarkovKernel (computationKernel f) := by
  unfold computationKernel; infer_instance

/-! ## §2 — The reversible / irreversible split of the primitive basis -/

/-- `succ` is information-preserving: `eval succ = Nat.succ` is injective. -/
theorem succ_injective : Function.Injective Nat.succ := Nat.succ_injective

/-- `pair` is information-preserving: it is the bijection `Nat.pairEquiv`. -/
theorem pair_injective : Function.Injective (Function.uncurry Nat.pair) :=
  Nat.pairEquiv.injective

/-- `left` is information-discarding: `eval left = fun n ↦ (unpair n).1` is **not**
injective (it forgets the second component). -/
theorem left_not_injective : ¬ Function.Injective (fun n => (Nat.unpair n).1) := by
  intro h
  have h2 : Nat.pair 0 0 = Nat.pair 0 1 := h (by simp [Nat.unpair_pair])
  have h3 := congrArg Nat.unpair h2
  simp [Nat.unpair_pair] at h3

/-- `right` is information-discarding: `eval right = fun n ↦ (unpair n).2` is **not**
injective. -/
theorem right_not_injective : ¬ Function.Injective (fun n => (Nat.unpair n).2) := by
  intro h
  have h2 : Nat.pair 0 0 = Nat.pair 1 0 := h (by simp [Nat.unpair_pair])
  have h3 := congrArg Nat.unpair h2
  simp [Nat.unpair_pair] at h3

/-- `zero` is maximally information-discarding: `eval zero` is the constant `0`,
not injective. -/
theorem const_not_injective : ¬ Function.Injective (fun _ : ℕ => (0 : ℕ)) := by
  intro h
  exact absurd (h rfl : (0 : ℕ) = 1) (by norm_num)

/-! ## §3 — Reversible computation preserves relative entropy (Bennett)

Retaining the input alongside the output is the *same* channel applied to both
the state and the reference, so the joint relative entropy is unchanged: the
history-keeping computation produces no entropy. -/

/-- **Reversible computation preserves KL.** For any computable `f` and finite
measures `μ ν`, the `(input, output)` joint relative entropy equals the input
relative entropy. Zero entropy production — Bennett's reversible embedding. -/
theorem computation_keeps_kl (f : ℕ → ℕ) (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ ⊗ₘ computationKernel f) (ν ⊗ₘ computationKernel f) = klDiv μ ν :=
  klDiv_reversible_invariant

/-- The entropy produced by a history-keeping (reversible) computation is zero. -/
theorem reversible_entropy_production_zero (f : ℕ → ℕ) (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (klDiv (μ ⊗ₘ computationKernel f) (ν ⊗ₘ computationKernel f)).toReal
      - (klDiv μ ν).toReal = 0 := by
  rw [computation_keeps_kl]; ring

/-! ## §4 — Erasing the input register is a coarse-graining step (Landauer)

The irreversible act is discarding the input. Resetting the input register to a
fixed reference while keeping the computed output makes the step a
`CoarseGrainingStep`: the reversible channel is the computation `κ_f`, the
equilibrium channel `η` resets to the constant `0`. The dissipated relative
entropy is the erased information, non-negative by the H-theorem. -/

/-- **The erasure step.** A computation `f` together with the reset-to-`0`
equilibrium channel forms a coarse-graining step, given finiteness of the fine
relative entropy. Its `tauEnt` (derived, `≥ 0`) is the erased information. -/
noncomputable def erasureStep (f : ℕ → ℕ) (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv (μ ⊗ₘ computationKernel f) (ν ⊗ₘ computationKernel (fun _ => 0)) ≠ ∞) :
    CoarseGrainingStep where
  α := ℕ
  β := ℕ
  μ := μ
  ν := ν
  κ := computationKernel f
  η := computationKernel (fun _ => 0)
  fine_kl_finite := hfin

/-- The erased information of a computation step is non-negative — the H-theorem
applied to computation: erasing the input register never decreases the entropy
sent to the environment. -/
theorem erasureStep_tauEnt_nonneg (f : ℕ → ℕ) (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv (μ ⊗ₘ computationKernel f) (ν ⊗ₘ computationKernel (fun _ => 0)) ≠ ∞) :
    0 ≤ (erasureStep f μ ν hfin).tauEnt :=
  (erasureStep f μ ν hfin).tauEnt_nonneg

/-- The erased information equals the coarse-graining conditional KL — the single
genuine physical input, exactly as in the H-theorem. -/
theorem erasureStep_tauEnt_eq_entropyProduced (f : ℕ → ℕ) (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv (μ ⊗ₘ computationKernel f) (ν ⊗ₘ computationKernel (fun _ => 0)) ≠ ∞) :
    (erasureStep f μ ν hfin).tauEnt = (erasureStep f μ ν hfin).entropyProduced :=
  (erasureStep f μ ν hfin).tauEnt_eq_entropyProduced

/-! ## §5 — A concrete, non-vacuous step

`f = fun _ ↦ 0` (the `zero` primitive), `μ = ν = δ₀`: the computation already
agrees with the reset channel, so the fine relative entropy is `0`, witnessing
inhabitation. -/

/-- A concrete erasure step witnessing non-vacuity. -/
noncomputable def trivialErasureStep : CoarseGrainingStep :=
  erasureStep (fun _ => 0) (Measure.dirac 0) (Measure.dirac 0) <| by
    rw [klDiv_self]; exact ENNReal.zero_ne_top

end

end Physlib.Thermodynamics.ComputationLandauer

@[expose] public section

namespace Physlib.Thermodynamics.Landauer

/-! ## L4: Computation traces and QTM lift

Adds the computational layer to the existing Landauer infrastructure.
A computation is a sequence of steps, each either *reversible* (no
bit erased) or *irreversible* (one bit committed to the classical
record).  The count of irreversible steps in a trace then plugs
directly into the existing `landauerEnergyForBits` to give the
trace's Landauer-floor heat dissipation.

This section integrates three lines:

* **Classical computation traces** over Mathlib's `Nat.Partrec.Code`
  (Carneiro 2018, arXiv 1810.08380).  Each step is a Gödel code
  plus a reversibility flag.

* **Qubit (QTM) lift** over `QuantumInfo.States.Pure.Qubit`'s
  `𝐔[Qubit]` unitary group.  Each step is either a unitary gate
  (reversible) or a measurement (irreversible).  By Bennett 1973 /
  1982 the per-step Landauer cost is identical to the classical
  case — a QTM is "a Turing machine that uses qubits instead of
  bits".

* **Connection to existing Landauer machinery**.  The trace's
  irreversibility count, cast to ℝ, feeds `landauerEnergyForBits`
  directly — no new heat formula is introduced.  Quantum
  coherence, superposition, entanglement live in `QuantumInfo`
  (see also `PageWoottersBipartite` in
  `Physlib.QuantumMechanics.RelationalTime.PageWootters` for the
  bipartite quantum-clock side); measurement back-action and
  decoherence rates live in physlib's Lindblad / QIF
  infrastructure; this layer captures only the irreversibility-
  *cost* dimension.

## External-origin disclaimer

A separate Lean codebase formalises a quantum version of this
content with a custom Quantum Turing Machine structure.  That work
informed this section conceptually but is not imported here —
physlib's lakefile depends only on Mathlib and doc-gen4 (plus
QuantumInfo, which is part of the same physlib lake-workspace).

## References

* Carneiro, M. (2018), *Formalizing Computability Theory via
  Partial Recursive Functions*, arXiv
  [1810.08380](https://arxiv.org/abs/1810.08380), ITP 2019.
* Deutsch, D. (1985), *Quantum theory, the Church-Turing principle
  and the universal quantum computer*, Proc. Roy. Soc. A **400**,
  97-117.
* Bennett, C. H. (1973), *Logical Reversibility of Computation*,
  IBM J. Res. Dev. **17**, 525-532.
-/

/-! ### L4.A — Reversibility flag and Landauer count -/

/-- **Reversibility flag** on a computation step.

* `true`  = reversible step (no information erased; no Landauer cost).
* `false` = irreversible step (one bit erased; Landauer cost
  `landauerCost T = kB · T · log 2`).

Plain alias of `Bool`; constructors named below. -/
abbrev Reversibility := Bool

/-- A reversible step.  No Landauer cost. -/
abbrev reversibleStep : Reversibility := true

/-- An irreversible step.  One Landauer-bit cost
`landauerCost T`. -/
abbrev irreversibleStep : Reversibility := false

/-- **Landauer count** on a list of computation steps: the number
of `irreversibleStep`s in the list. -/
def landauerCount (steps : List Reversibility) : ℕ :=
  steps.count irreversibleStep

@[simp] theorem landauerCount_nil :
    landauerCount [] = 0 := by
  unfold landauerCount; simp

@[simp] theorem landauerCount_singleton_reversible :
    landauerCount [reversibleStep] = 0 := by
  unfold landauerCount reversibleStep irreversibleStep; simp

@[simp] theorem landauerCount_singleton_irreversible :
    landauerCount [irreversibleStep] = 1 := by
  unfold landauerCount irreversibleStep; simp

theorem landauerCount_append (s₁ s₂ : List Reversibility) :
    landauerCount (s₁ ++ s₂) =
      landauerCount s₁ + landauerCount s₂ := by
  unfold landauerCount; simp [List.count_append]

/-- **Bridge to `landauerEnergyForBits`**: the Landauer heat floor
of a trace at temperature `T` is `landauerEnergyForBits T N`
where `N` is the trace's `landauerCount`. -/
noncomputable def traceLandauerEnergy
    (steps : List Reversibility) (T : ℝ) : ℝ :=
  landauerEnergyForBits T (landauerCount steps : ℝ)

/-- The trace Landauer energy equals
`(landauerCount steps : ℝ) · landauerCost T`. -/
theorem traceLandauerEnergy_eq_count_mul_landauerCost
    (steps : List Reversibility) (T : ℝ) :
    traceLandauerEnergy steps T =
      (landauerCount steps : ℝ) * landauerCost T := by
  unfold traceLandauerEnergy landauerEnergyForBits
  rfl

/-- The trace Landauer energy is non-negative at `T ≥ 0`. -/
theorem traceLandauerEnergy_nonneg
    (steps : List Reversibility) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ traceLandauerEnergy steps T := by
  rw [traceLandauerEnergy_eq_count_mul_landauerCost]
  exact mul_nonneg (Nat.cast_nonneg _) (landauerCost_nonneg T hT)

/-! ### L4.B — Computation steps over Mathlib `Nat.Partrec.Code`

Each step has a Gödel code (from Carneiro 2018) plus a
reversibility flag.  Mathlib's `halting_problem` (undecidability
of halting) is what forces the flag to be *declared* per step,
not derived from the code structure — a sound substrate without
requiring us to solve undecidable problems. -/

/-- **Computation step**: a Gödel code plus an irreversibility flag. -/
structure ComputationStep where
  /-- Gödel code of the partial recursive function (Mathlib /
  Carneiro 2018). -/
  code : Nat.Partrec.Code
  /-- Reversibility flag for this step. -/
  reversibility : Reversibility

/-- A **computation trace** is a list of computation steps. -/
abbrev ComputationTrace := List ComputationStep

/-- **Landauer count of a computation trace**: count of steps
marked `irreversibleStep`. -/
def traceLandauerCount (trace : ComputationTrace) : ℕ :=
  landauerCount (trace.map (·.reversibility))

@[simp] theorem traceLandauerCount_nil :
    traceLandauerCount [] = 0 := by
  unfold traceLandauerCount; simp

/-- **Computation trace Landauer-floor heat**.  Delegates to the
existing `landauerEnergyForBits`. -/
noncomputable def computationTraceLandauerEnergy
    (trace : ComputationTrace) (T : ℝ) : ℝ :=
  landauerEnergyForBits T (traceLandauerCount trace : ℝ)

/-- The computation-trace Landauer floor equals
`(traceLandauerCount trace : ℝ) · landauerCost T`. -/
theorem computationTraceLandauerEnergy_eq
    (trace : ComputationTrace) (T : ℝ) :
    computationTraceLandauerEnergy trace T =
      (traceLandauerCount trace : ℝ) * landauerCost T := by
  unfold computationTraceLandauerEnergy landauerEnergyForBits
  rfl

/-! ### L4.C — Qubit lift (QTM model)

The QTM lift: each step is either a unitary gate from `𝐔[Qubit]`
(reversible) or a measurement (irreversible).  Multi-qubit
extensions follow via `𝐔[Qubit × Qubit]`; the single-qubit case
below is the minimal substantive lift.

The qubit content is what is manipulated; the Landauer cost
depends only on the count of measurement steps.  Standard gates
(X, Y, Z, H, S, T) all reduce to zero Landauer cost on a single-
step trace. -/

/-- **QTM computation step**: a single-qubit unitary gate
(reversible) or a measurement (irreversible). -/
inductive QubitStep
  /-- Apply a unitary single-qubit gate `U`.  Reversible. -/
  | unitary (U : 𝐔[Qubit]) : QubitStep
  /-- Measure the qubit.  Irreversible (one bit committed). -/
  | measurement : QubitStep

/-- Reversibility of a `QubitStep`. -/
def QubitStep.reversibility : QubitStep → Reversibility
  | .unitary _   => reversibleStep
  | .measurement => irreversibleStep

@[simp] theorem QubitStep.reversibility_unitary (U : 𝐔[Qubit]) :
    (QubitStep.unitary U).reversibility = reversibleStep := rfl

@[simp] theorem QubitStep.reversibility_measurement :
    QubitStep.measurement.reversibility = irreversibleStep := rfl

/-- A **QTM trace**: a list of `QubitStep`s. -/
abbrev QTMTrace := List QubitStep

/-- **QTM Landauer count**: count of measurement steps in the
trace.  Computed via projection to `Reversibility`. -/
def qtmLandauerCount (trace : QTMTrace) : ℕ :=
  landauerCount (trace.map QubitStep.reversibility)

@[simp] theorem qtmLandauerCount_nil :
    qtmLandauerCount [] = 0 := by
  unfold qtmLandauerCount; simp

@[simp] theorem qtmLandauerCount_singleton_unitary (U : 𝐔[Qubit]) :
    qtmLandauerCount [QubitStep.unitary U] = 0 := by
  unfold qtmLandauerCount landauerCount
  simp [QubitStep.reversibility, reversibleStep, irreversibleStep]

@[simp] theorem qtmLandauerCount_singleton_measurement :
    qtmLandauerCount [QubitStep.measurement] = 1 := by
  unfold qtmLandauerCount landauerCount
  simp [QubitStep.reversibility, irreversibleStep]

/-- Pauli-X gate is reversible. -/
@[simp] theorem qtmLandauerCount_X :
    qtmLandauerCount [QubitStep.unitary Qubit.X] = 0 :=
  qtmLandauerCount_singleton_unitary _

/-- Pauli-Y gate is reversible. -/
@[simp] theorem qtmLandauerCount_Y :
    qtmLandauerCount [QubitStep.unitary Qubit.Y] = 0 :=
  qtmLandauerCount_singleton_unitary _

/-- Pauli-Z gate is reversible. -/
@[simp] theorem qtmLandauerCount_Z :
    qtmLandauerCount [QubitStep.unitary Qubit.Z] = 0 :=
  qtmLandauerCount_singleton_unitary _

/-- Hadamard gate is reversible. -/
@[simp] theorem qtmLandauerCount_H :
    qtmLandauerCount [QubitStep.unitary Qubit.H] = 0 :=
  qtmLandauerCount_singleton_unitary _

/-- S gate is reversible. -/
@[simp] theorem qtmLandauerCount_S :
    qtmLandauerCount [QubitStep.unitary Qubit.S] = 0 :=
  qtmLandauerCount_singleton_unitary _

/-- T gate is reversible. -/
@[simp] theorem qtmLandauerCount_T :
    qtmLandauerCount [QubitStep.unitary Qubit.T] = 0 :=
  qtmLandauerCount_singleton_unitary _

/-- **Bennett reversibility (abstract form)**: any list of unitary
single-qubit gates produces a trace with zero Landauer count. -/
theorem qtmLandauerCount_unitary_only (Us : List 𝐔[Qubit]) :
    qtmLandauerCount (Us.map QubitStep.unitary) = 0 := by
  induction Us with
  | nil => exact qtmLandauerCount_nil
  | cons U rest ih =>
    unfold qtmLandauerCount landauerCount
    unfold qtmLandauerCount landauerCount at ih
    simp [QubitStep.reversibility, reversibleStep,
          irreversibleStep] at *
    exact ih

/-- **QTM Landauer-floor heat**.  Delegates to the existing
`landauerEnergyForBits`. -/
noncomputable def qtmLandauerEnergy
    (trace : QTMTrace) (T : ℝ) : ℝ :=
  landauerEnergyForBits T (qtmLandauerCount trace : ℝ)

/-- The QTM Landauer floor equals
`(qtmLandauerCount trace : ℝ) · landauerCost T`. -/
theorem qtmLandauerEnergy_eq
    (trace : QTMTrace) (T : ℝ) :
    qtmLandauerEnergy trace T =
      (qtmLandauerCount trace : ℝ) * landauerCost T := by
  unfold qtmLandauerEnergy landauerEnergyForBits
  rfl

/-- The QTM Landauer floor is non-negative at `T ≥ 0`. -/
theorem qtmLandauerEnergy_nonneg
    (trace : QTMTrace) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ qtmLandauerEnergy trace T := by
  rw [qtmLandauerEnergy_eq]
  exact mul_nonneg (Nat.cast_nonneg _) (landauerCost_nonneg T hT)

/-! ### L4.D — Headline: QTM is a TM with qubits -/

/-- **QTM-is-a-TM-with-qubits headline**.  For any QTM trace, the
Landauer-floor heat equals the existing `landauerEnergyForBits`
applied to the count of measurement steps.  This is the formal
content of "a QTM is a Turing machine using qubits instead of
bits" — the qubit content is what is manipulated, but the
irreversibility cost is identical to the classical Landauer
floor. -/
theorem qtm_landauer_headline
    (trace : QTMTrace) (T : ℝ) :
    qtmLandauerEnergy trace T =
      landauerEnergyForBits T (qtmLandauerCount trace : ℝ) := rfl

end Physlib.Thermodynamics.Landauer

end
