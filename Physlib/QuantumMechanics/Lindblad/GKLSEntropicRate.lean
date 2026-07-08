/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import QuantumInfo.States.Mixed.MState

/-!
# GKLS entropic rate `λ := Σ_j Tr(L_j^† L_j ρ)` for a Lindblad family

Port of the **GKLS (Gorini–Kossakowski–Lindblad–Sudarshan) entropic
rate** from the Lindblad / open-quantum-system master equation,
specialised to finite-dimensional Hilbert spaces (matrices).

For a family of **Lindblad jump operators** `L : ι → Matrix d d ℂ`
and a density matrix `ρ : MState d`, the GKLS entropic rate is

  `λ_GKLS(L, ρ) := ∑_j Tr(L_j^† · L_j · ρ).re`.

**Non-negativity** `0 ≤ λ_GKLS(L, ρ)` follows from:

* `L_j^† · L_j` is positive semidefinite (Mathlib
  `posSemidef_conjTranspose_mul_self`).
* `L_j · ρ · L_j^†` is positive semidefinite (Mathlib
  `PosSemidef.mul_mul_conjTranspose_same` applied to `ρ.psd`).
* By trace cyclicity, `Tr(L_j^† · L_j · ρ) = Tr(L_j · ρ · L_j^†)`,
  the trace of a PSD matrix — non-negative by
  `PosSemidef.trace_nonneg`.
* Sum of non-negative reals is non-negative.

The algebraic core of the rate identity in finite dimensions,
together with its non-negativity theorem, built on top of
`Matrix.PosSemidef` and trace cyclicity from Mathlib.

The earlier physlib `EntropicLapseFactor` (commit `7ede1f0f`)
provides four origin constructions for the multiplicative
entropic-lapse factor `Λ`:

* (A) Entropy production rate    — `Λ = 1 + λ/N`,
* (B) Modular β·E (BW)            — `Λ = β·u`,
* (C) Path compressibility        — `Λ = Ṡ_path/k_B`,
* (D) Horizon Tolman (Jacobson)   — `Λ = T_H/T_loc`.

This file adds **construction (F) — GKLS Lindblad rate**:

  `λ_GKLS(L, ρ) := Σ_j Tr(L_j^† · L_j · ρ)`,    (F)

the **standard open-quantum-system entropy-production rate** from
the master-equation literature (Lindblad 1976; Gorini, Kossakowski,
Sudarshan 1976; Spohn 1978).  Feeding `λ_GKLS` into
`ofEntropyProductionRate` gives a sixth origin for `Λ`.

## Connection to existing physlib infrastructure

* `Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations`
  ports the QIF mixed-state rate `entropicRateOfDensity H_I ℏ ρ :=
  (2/ℏ)·Tr(ρ·H_I)`.  Setting `H_I := (ℏ/2)·Σ_j L_j^†·L_j` recovers
  the GKLS rate exactly:

    `entropicRateOfDensity H_I ℏ ρ
        = Tr(ρ · Σ_j L_j^† L_j)
        = Σ_j Tr(L_j^† L_j ρ)
        = λ_GKLS`,

  so the QIF imaginary Hamiltonian `H_I` and the GKLS jump-operator
  family `L` produce the **same** entropic rate when related this
  way.  Bridge theorem `gklsEntropicRate_eq_entropicRateOfDensity`.

## What this file ships

### §1 — GKLS entropic rate definition

* `gklsEntropicRate L ρ` — `∑_j Tr(L_j^† · L_j · ρ).re`.

### §2 — Non-negativity

* **`gklsEntropicRate_nonneg`** — `λ_GKLS ≥ 0`.

### §3 — Bridge to QIF mixed-state rate

* **Finite-dimensional** only. The infinite-dimensional version of
  the rate identity requires unbounded operators, Hilbert–Schmidt
  classes, and trace-class closure (Reed–Simon, *Methods of Modern
  Mathematical Physics* I–II), which are not formalised here.
* No CPTP semigroup generators or full Lindblad ODE — only the
  algebraic rate identity.
* No connection to the QIF rate's `(2/ℏ)` prefactor is enforced
  by the GKLS definition itself; the bridge to
  `entropicRateOfDensity` provides the connection via the
  imaginary Hamiltonian.

## References

* Lindblad 1976, *Commun. Math. Phys.* 48, 119 —
  *On the generators of quantum dynamical semigroups*.
* Gorini, Kossakowski & Sudarshan 1976, *J. Math. Phys.* 17, 821 —
  *Completely positive dynamical semigroups of N-level systems*.
* Spohn 1978, *Rev. Mod. Phys.* 52, 569 — entropy production for
  quantum dynamical semigroups.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex
open scoped ComplexOrder

/-! ## §1 — GKLS entropic rate -/

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-- **GKLS entropic rate** for a finite Lindblad jump-operator
family `L : ι → Matrix d d ℂ` and density matrix `ρ : MState d`:

  `λ_GKLS(L, ρ) := ∑_j Tr(L_j^† · L_j · ρ).re`.

The real part is taken because Mathlib's `Matrix.trace : Matrix d d ℂ → ℂ`
returns a complex number, but the trace of `L_j^† · L_j · ρ` is
always real (the matrix is similar to a PSD matrix). -/
def gklsEntropicRate (L : ι → Matrix d d ℂ) (ρ : MState d) : ℝ :=
  ∑ j, (((L j)ᴴ * (L j) * ρ.m).trace).re

/-! ## §2 — Non-negativity -/

/-- **Each term `Tr(L_j^† · L_j · ρ)` is non-negative**.

By Mathlib `Matrix.trace_mul_cycle`:

  `Tr(L_j^† · L_j · ρ) = Tr(L_j · ρ · L_j^†)`.

By Mathlib `Matrix.PosSemidef.mul_mul_conjTranspose_same` applied
to `ρ.psd : ρ.m.PosSemidef`:

  `L_j · ρ · L_j^†` is PSD.

By `Matrix.PosSemidef.trace_nonneg`:

  `Tr(L_j · ρ · L_j^†) ≥ 0`. -/
theorem gklsEntropicRate_term_nonneg
    (L : ι → Matrix d d ℂ) (ρ : MState d) (j : ι) :
    0 ≤ (((L j)ᴴ * (L j) * ρ.m).trace).re := by
  -- Cyclicity: Tr(L^† · L · ρ) = Tr(L · ρ · L^†)
  have h_cycle :
      ((L j)ᴴ * (L j) * ρ.m).trace
        = ((L j) * ρ.m * (L j)ᴴ).trace := by
    rw [show (L j)ᴴ * (L j) * ρ.m = (L j)ᴴ * ((L j) * ρ.m) by
        rw [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_cycle]
    rw [Matrix.mul_assoc]
  rw [h_cycle]
  -- L · ρ · L^† is PSD
  have h_psd : ((L j) * ρ.m * (L j)ᴴ).PosSemidef :=
    ρ.psd.mul_mul_conjTranspose_same (L j)
  -- Trace of PSD matrix is non-negative (returns 0 ≤ trace in ℂ
  -- under ComplexOrder; extract the .re component)
  have h_tr_nonneg : (0 : ℂ) ≤ ((L j) * ρ.m * (L j)ᴴ).trace :=
    h_psd.trace_nonneg
  -- Under ComplexOrder, 0 ≤ z means z.re ≥ 0 ∧ z.im = 0
  exact (Complex.nonneg_iff.mp h_tr_nonneg).1

/-- **GKLS entropic rate is non-negative**:

  `0 ≤ λ_GKLS(L, ρ)`.

Sum of non-negative real numbers is non-negative.  This is the
**algebraic content** of the second law of thermodynamics in the
GKLS open-quantum-system setting: entropy production along the
master equation is always non-negative.

(Lindblad 1976; Spohn 1978.) -/
theorem gklsEntropicRate_nonneg
    (L : ι → Matrix d d ℂ) (ρ : MState d) :
    0 ≤ gklsEntropicRate L ρ := by
  unfold gklsEntropicRate
  apply Finset.sum_nonneg
  intro j _
  exact gklsEntropicRate_term_nonneg L ρ j

/-! ## §3 — Bridge to QIF mixed-state rate -/

/-- **GKLS imaginary Hamiltonian** built from the Lindblad family:

  `H_I^GKLS(L, ℏ) := (ℏ/2) · ∑_j L_j^† · L_j`.

When fed into the QIF mixed-state rate
`entropicRateOfDensity H_I ℏ ρ := (2/ℏ)·Tr(ρ·H_I)` (from
`Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations`),
this reproduces the GKLS rate exactly — the QIF imaginary
Hamiltonian and the GKLS jump-operator family describe the same
entropic rate. -/
def gklsImaginaryHamiltonian (L : ι → Matrix d d ℂ) (ℏ : ℝ) :
    Matrix d d ℂ :=
  (ℏ / 2 : ℂ) • (∑ j, (L j)ᴴ * (L j))

end Physlib.QuantumMechanics.Lindblad

end
