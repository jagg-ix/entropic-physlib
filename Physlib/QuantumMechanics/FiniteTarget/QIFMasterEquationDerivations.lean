/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Master equation derivations (Eqs 75, 77, 78)

Port of Wolfram derivations from
`entropic-time/.../CAT_EPT_Extended_Part3.wl`, equations (75)-(80).

## Equations ported

* **Eq (75)**: Dissipative von Neumann equation
  `dρ/dt = -(i/ℏ)·[H_R, ρ] - (1/ℏ)·{H_I, ρ}`,
  derived in the Wolfram source from the non-Hermitian Schrödinger
  evolution `iℏ ∂_t|ψ⟩ = (H_R - iH_I)|ψ⟩` for `ρ = |ψ⟩⟨ψ|`.
* **Eq (77)**: Entropic rate as mixed-state functional
  `λ(t) := (2/ℏ)·Tr(ρ·H_I)`.
* **Eq (78)**: Master equation in entropic time (chain-rule
  reparametrisation `d_t = λ·d_τ`).

## What's algebraically formalised vs the Wolfram derivation

The Wolfram derivation runs through `dρ/dt = ...` derivative
machinery on density matrices.  The Lean port stays at the
**algebraic-identity level** by treating the right-hand side as a
function `vonNeumannRate H_R H_I ℏ ρ : Matrix d d ℂ` and proving
its structural properties (trace identity, sign conventions,
chain-rule rescaling).  The derivative-machinery aspect is
implicit in the structure name (`rate`) and explicit in
documentation — actually proving the time-derivative identity
would require differentiable trajectories `ρ : ℝ → Matrix d d ℂ`,
which is heavier and orthogonal to the algebra.

## Main definitions and theorems

* `commutator A B := A·B - B·A`, `anticommutator A B := A·B + B·A`.
* `trace_commutator` — `Tr[A,B] = 0` (cyclicity).
* `trace_anticommutator` — `Tr{A,B} = 2·Tr(A·B)`.
* `vonNeumannRate H_R H_I ℏ ρ` — Eq (75) right-hand side as a
  matrix function.
* **`trace_vonNeumannRate`** — Eq (75) → Eq (77) reduction:
  `Tr(rate) = -(2/ℏ)·Tr(ρ·H_I) = -λ`.
* `entropicRateOfDensity H_I ℏ ρ := (2/ℏ)·Tr(ρ·H_I)` — Eq (77).
* `trace_vonNeumannRate_eq_neg_entropicRate` — connects the two.
* `vonNeumannRateInEntropicTime H_R H_I ℏ lam ρ := rate / lam` —
  Eq (78) reparametrisation.

## What's NOT in this file

* Eq (76) **second law `dS/dt ≥ 0`**: requires von Neumann entropy
  `S = -Tr(ρ·ln ρ)` and Klein's inequality.  The trace machinery
  exists in physlib's `QuantumInfo.Entropy`; consumers can lift
  the von-Neumann rate from this file there.
* Eqs (79-80) **Thermal Hamiltonian bridge `H_th = -ln ρ = τ_ent`**:
  the `modularHamiltonianMat ρ := -ρ.M.log` structure already exists
  in `Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularFromState`
  (commit `94661435`).  Eq (79) is therefore a *definition*, not
  a theorem to port; the conceptual identification with `τ_ent` is
  the physical meaning of `connesRovelliThermalTime`
  (`QuantumInertialFrameKMS.lean`).


## References

* `entropic-time/.../CAT_EPT_Extended_Part3.wl` Eqs (75)-(80).
* Sergi & Giaquinta 2016 *Entropy* — non-Hermitian von Neumann
  equation in the convention used here (no factor of 1/2).
* Lindblad 1976 / GKLS 1976 — full CPTP master equation; the
  present file's version is the *non-Hermitian* simplification.
* Connes-Rovelli 1994 — thermal time hypothesis underpinning
  Eqs (79-80).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §1 — Commutator and anticommutator -/

/-- **Commutator** `[A, B] := A·B - B·A`. -/
def commutator (A B : Matrix d d ℂ) : Matrix d d ℂ := A * B - B * A

@[simp] theorem commutator_def (A B : Matrix d d ℂ) :
    commutator A B = A * B - B * A := rfl

/-- **Anticommutator** `{A, B} := A·B + B·A`. -/
def anticommutator (A B : Matrix d d ℂ) : Matrix d d ℂ := A * B + B * A

@[simp] theorem anticommutator_def (A B : Matrix d d ℂ) :
    anticommutator A B = A * B + B * A := rfl

/-- **Trace of commutator vanishes** (cyclicity):
`Tr[A, B] = Tr(A·B) - Tr(B·A) = 0`. -/
@[simp] theorem trace_commutator (A B : Matrix d d ℂ) :
    (commutator A B).trace = 0 := by
  unfold commutator
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  ring

/-- **Trace of anticommutator**: `Tr{A, B} = 2·Tr(A·B)` (using
cyclicity `Tr(B·A) = Tr(A·B)`). -/
theorem trace_anticommutator (A B : Matrix d d ℂ) :
    (anticommutator A B).trace = 2 * (A * B).trace := by
  unfold anticommutator
  rw [Matrix.trace_add, Matrix.trace_mul_comm B A]
  ring

/-! ## §2 — Von Neumann rate (Eq 75 right-hand side) -/

/-- **Dissipative von Neumann rate** (Eq 75 RHS):

  `vonNeumannRate H_R H_I ℏ ρ
   := -(i/ℏ)·[H_R, ρ] - (1/ℏ)·{H_I, ρ}`.

Physically: this is the *rate of change of `ρ`* in the
non-Hermitian Schrödinger picture, with `H_R` driving unitary
rotation (via the commutator) and `H_I` driving dissipative decay
(via the anticommutator).  No factor of `1/2` on the dissipator
(Sergi-Giaquinta convention; matches Eq 75 of the Wolfram source). -/
def vonNeumannRate (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (ρ : Matrix d d ℂ) :
    Matrix d d ℂ :=
  -(Complex.I / (ℏ : ℂ)) • commutator H_R ρ -
    ((1 : ℂ) / (ℏ : ℂ)) • anticommutator H_I ρ

/-! ## §3 — Trace of the rate = −(2/ℏ)·Tr(ρ·H_I) (Eq 75 → Eq 77) -/

/-- **Trace of the von Neumann rate equals the negative entropic
rate** — the algebraic content of Eqs (75)→(77):

  `Tr(vonNeumannRate) = -(2/ℏ) · Tr(ρ · H_I)`.

Derivation:
* `Tr[H_R, ρ] = 0` (commutator trace vanishes).
* `Tr{H_I, ρ} = 2·Tr(H_I·ρ) = 2·Tr(ρ·H_I)` (cyclicity).
* Combining with the `-(1/ℏ)` coefficient gives the final form.

Physically: the trace of the density matrix decreases at
rate `λ(t) = (2/ℏ)·Tr(ρ·H_I)` — i.e., the **entropic rate**
governs the norm-squared decay in the non-Hermitian formulation. -/
theorem trace_vonNeumannRate
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (ρ : Matrix d d ℂ) :
    (vonNeumannRate H_R H_I ℏ ρ).trace =
      -(2 / (ℏ : ℂ)) * (ρ * H_I).trace := by
  unfold vonNeumannRate
  rw [Matrix.trace_sub, Matrix.trace_smul, trace_commutator,
      smul_zero, zero_sub, Matrix.trace_smul, trace_anticommutator]
  rw [Matrix.trace_mul_comm H_I ρ]
  rw [smul_eq_mul]
  have hℏ_c : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  field_simp

/-! ## §4 — Entropic rate of a density matrix (Eq 77 definition) -/

/-- **Entropic rate of a density matrix** (Eq 77):

  `λ(t) := (2/ℏ) · Tr(ρ · H_I)`.

This is the mixed-state generalisation of the pure-state QIF
entropic rate `λ(ψ) := (2/ℏ)·H_I.reApplyInnerSelf ψ` (which is the
specialisation to `ρ = |ψ⟩⟨ψ|`). -/
def entropicRateOfDensity (H_I : Matrix d d ℂ) (ℏ : ℝ) (ρ : Matrix d d ℂ) : ℂ :=
  (2 / (ℏ : ℂ)) * (ρ * H_I).trace

/-- **Trace of the von Neumann rate is the negative entropic rate**.
Theorem from Eqs (75)→(77): the algebraic chain from the master
equation to the entropic rate. -/
theorem trace_vonNeumannRate_eq_neg_entropicRate
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (ρ : Matrix d d ℂ) :
    (vonNeumannRate H_R H_I ℏ ρ).trace =
      -entropicRateOfDensity H_I ℏ ρ := by
  rw [trace_vonNeumannRate H_R H_I ℏ hℏ ρ]
  unfold entropicRateOfDensity
  ring

/-! ## §5 — Master equation in entropic time (Eq 78) -/

/-- **Von Neumann rate in entropic time** (Eq 78):

  `dρ/dτ_ent = (1/λ) · dρ/dt = -i·[H_R, ρ] - {H_I/λ, ρ}` (at `ℏ = 1`).

Chain-rule reparametrisation: `dτ_ent = λ·dt`, so `d_t = λ·d_τ`,
and dividing the master equation by `λ` gives the entropic-time
form.

The expression below is the general-ℏ version: rate divided by
`λ` (with `λ` the entropic rate). -/
def vonNeumannRateInEntropicTime
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (lam : ℝ) (ρ : Matrix d d ℂ) :
    Matrix d d ℂ :=
  ((1 : ℂ) / (lam : ℂ)) • vonNeumannRate H_R H_I ℏ ρ

/-- The entropic-time rate is the coordinate-time rate divided by
`λ` — the chain-rule identity. -/
theorem vonNeumannRateInEntropicTime_eq
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (lam : ℝ) (ρ : Matrix d d ℂ) :
    vonNeumannRateInEntropicTime H_R H_I ℏ lam ρ =
      ((1 : ℂ) / (lam : ℂ)) • vonNeumannRate H_R H_I ℏ ρ := rfl

/-- **Trace of the entropic-time rate**: combining the chain rule
with `trace_vonNeumannRate`,

  `Tr(rate_τ) = -(2/(ℏ·λ)) · Tr(ρ·H_I)`. -/
theorem trace_vonNeumannRateInEntropicTime
    (H_R H_I : Matrix d d ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (lam : ℝ) (hlam : lam ≠ 0) (ρ : Matrix d d ℂ) :
    (vonNeumannRateInEntropicTime H_R H_I ℏ lam ρ).trace =
      -(2 / ((ℏ : ℂ) * (lam : ℂ))) * (ρ * H_I).trace := by
  unfold vonNeumannRateInEntropicTime
  rw [Matrix.trace_smul, trace_vonNeumannRate H_R H_I ℏ hℏ]
  rw [smul_eq_mul]
  have hℏ_c : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  have hlam_c : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  field_simp

end QuantumMechanics.FiniteTarget

end
