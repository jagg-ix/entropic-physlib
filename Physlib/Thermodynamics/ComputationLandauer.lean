/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Thermodynamics of computation: the reversible/irreversible split and the Landauer floor

The computational face of the arrow of time, built on Mathlib's formalization of classical computability via
partial recursive functions (`Nat.Partrec.Code`, after M. Carneiro, *Formalizing Computability Theory via Partial
Recursive Functions*, ITP 2019). Carneiro's primitive basis splits cleanly along the **reversible/irreversible**
line by the injectivity of its `eval` semantics:

* **information-preserving** (injective): `succ` (`Nat.succ`), `pair` (the bijection `ℕ × ℕ ≃ ℕ`);
* **information-discarding** (non-injective): `zero` (constant), `left` and `right` (each projection erases the
  half the other keeps).

Only the irreversible (erasing) steps carry a thermodynamic cost — **Landauer's floor** `k_B T log 2` per erased
bit (Landauer 1961; Bennett 1973: a computation that retains its input is reversible and free). The Landauer heat
of a computation trace is `(#irreversible steps)·k_B T log 2`.

References: R. Landauer 1961; C.H. Bennett 1973; M. Carneiro, ITP 2019 (arXiv:1810.08380). No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Thermodynamics.ComputationLandauer

/-! ## The reversible / irreversible split of the primitive basis -/

/-- **`succ` is information-preserving**: `Nat.succ` is injective. -/
theorem succ_injective : Function.Injective Nat.succ := Nat.succ_injective

/-- **`pair` is information-preserving**: it is the bijection `Nat.pairEquiv : ℕ × ℕ ≃ ℕ`. -/
theorem pair_injective : Function.Injective (Function.uncurry Nat.pair) := Nat.pairEquiv.injective

/-- **`left` is information-discarding**: `n ↦ (unpair n).1` forgets the second component, hence is not injective. -/
theorem left_not_injective : ¬ Function.Injective (fun n => (Nat.unpair n).1) := by
  intro h
  have h2 : Nat.pair 0 0 = Nat.pair 0 1 := h (by simp [Nat.unpair_pair])
  have h3 := congrArg Nat.unpair h2
  simp [Nat.unpair_pair] at h3

/-- **`right` is information-discarding**: `n ↦ (unpair n).2` is not injective. -/
theorem right_not_injective : ¬ Function.Injective (fun n => (Nat.unpair n).2) := by
  intro h
  have h2 : Nat.pair 0 0 = Nat.pair 1 0 := h (by simp [Nat.unpair_pair])
  have h3 := congrArg Nat.unpair h2
  simp [Nat.unpair_pair] at h3

/-- **`zero` is maximally information-discarding**: the constant `0` is not injective. -/
theorem const_not_injective : ¬ Function.Injective (fun _ : ℕ => (0 : ℕ)) := by
  intro h
  exact absurd (h rfl : (0 : ℕ) = 1) (by norm_num)

/-! ## The Landauer floor and the cost of a computation trace -/

/-- **The Landauer cost per erased bit** `k_B T log 2` (Landauer 1961). -/
noncomputable def landauerCost (kB T : ℝ) : ℝ := kB * T * Real.log 2

/-- **The Landauer cost is non-negative** for `k_B, T ≥ 0`. -/
theorem landauerCost_nonneg {kB T : ℝ} (hkB : 0 ≤ kB) (hT : 0 ≤ T) : 0 ≤ landauerCost kB T :=
  mul_nonneg (mul_nonneg hkB hT) (Real.log_nonneg (by norm_num))

/-- **A reversibility flag**: `true` = reversible (no bit erased), `false` = irreversible (one bit erased). -/
abbrev Reversibility := Bool

/-- A reversible step (no Landauer cost). -/
abbrev reversibleStep : Reversibility := true

/-- An irreversible step (one Landauer-bit cost). -/
abbrev irreversibleStep : Reversibility := false

/-- **The Landauer count** of a step list: the number of irreversible (erasing) steps. -/
def landauerCount (steps : List Reversibility) : ℕ := steps.count irreversibleStep

/-- **A reversible computation has zero Landauer cost** (Bennett): a run of purely reversible steps erases no
bits. -/
theorem landauerCount_reversible (n : ℕ) : landauerCount (List.replicate n reversibleStep) = 0 := by
  simp [landauerCount, reversibleStep, irreversibleStep, List.count_replicate]

/-- **The Landauer count is additive over concatenation** — the erased bits of a composite computation are the sum
of those of its parts. -/
theorem landauerCount_append (s₁ s₂ : List Reversibility) :
    landauerCount (s₁ ++ s₂) = landauerCount s₁ + landauerCount s₂ := by
  unfold landauerCount
  rw [List.count_append]

/-- **A computation step**: a Gödel code (Carneiro's `Nat.Partrec.Code`) plus a reversibility flag. -/
structure ComputationStep where
  /-- Gödel code of the partial recursive function. -/
  code : Nat.Partrec.Code
  /-- Reversibility flag for this step. -/
  reversibility : Reversibility

/-- **A computation trace** is a list of computation steps. -/
abbrev ComputationTrace := List ComputationStep

/-- **The Landauer count of a trace**: the number of irreversible steps. -/
def traceLandauerCount (trace : ComputationTrace) : ℕ :=
  landauerCount (trace.map (·.reversibility))

/-- **The Landauer-floor heat of a trace** `(#irreversible steps)·k_B T log 2`. -/
noncomputable def traceLandauerEnergy (trace : ComputationTrace) (kB T : ℝ) : ℝ :=
  (traceLandauerCount trace : ℝ) * landauerCost kB T

/-- **The trace Landauer floor is non-negative** for `k_B, T ≥ 0`. -/
theorem traceLandauerEnergy_nonneg (trace : ComputationTrace) {kB T : ℝ}
    (hkB : 0 ≤ kB) (hT : 0 ≤ T) : 0 ≤ traceLandauerEnergy trace kB T :=
  mul_nonneg (Nat.cast_nonneg _) (landauerCost_nonneg hkB hT)

end Physlib.Thermodynamics.ComputationLandauer

end
