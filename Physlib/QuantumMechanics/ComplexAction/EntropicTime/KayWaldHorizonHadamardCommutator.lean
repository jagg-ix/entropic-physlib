/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

/-!
# The Hadamard / Pauli–Jordan split of the Kay–Wald horizon two-point function

Decomposes the Kay–Wald horizon two-point (Wightman) function `W(U) = −(1/4π)/(U − iε)²` (Eq. 1.1,
`horizonTwoPointFunction`) into its **symmetric (Hadamard)** and **antisymmetric (Pauli–Jordan commutator)** parts
— the structural content on which the Kay–Wald uniqueness theorem rests: the commutator is state-independent (fixed
by the CCR), while the symmetric part is the state-dependent Hadamard function determined by stationarity and
nonsingularity.

Swapping the two horizon points sends the affine separation `U ↦ −U`, and the two-point function satisfies the
**Wightman hermiticity** `W(−U) = \overline{W(U)}` (the field is Hermitian, `ω(Φ(y)Φ(x)) = \overline{ω(Φ(x)Φ(y))}`).
From this single identity:

* the **Hadamard (symmetric) part** `H(U) = W(U) + W(−U) = 2 Re W(U)` is **real** (`horizonHadamard_isReal`) and
 symmetric `H(−U) = H(U)` (`horizonHadamard_symm`);
* the **Pauli–Jordan commutator (antisymmetric) part** `Δ(U) = W(U) − W(−U) = 2i Im W(U)` is **purely imaginary**
 (`horizonCommutator_isImaginary`) — the `i·(state-independent commutator)` fixed by the CCR — and antisymmetric
 `Δ(−U) = −Δ(U)` (`horizonCommutator_antisymm`);
* the **two-point function is their half-sum** `W = ½(H + Δ)` (`horizonWightman_hadamard_commutator_split`).

So the Kay–Wald horizon correlator splits as `W = ½(H + Δ)` with `H` real symmetric (the Hadamard/nonsingular part)
and `Δ` imaginary antisymmetric (the CCR commutator): the uniqueness of the state is the statement that `Δ` is
fixed and only `H` — the positive-frequency, stationary Hadamard part — must be determined, which the Kay–Wald
theorem does uniquely.

* **§A — Wightman hermiticity** (`horizonTwoPointFunction_neg_eq_conj`).
* **§B — the Hadamard/commutator parts and the split** (`horizonHadamard`, `horizonCommutator`,
 `horizonHadamard_isReal`, `horizonCommutator_isImaginary`, `horizonWightman_hadamard_commutator_split`).
* **§C — symmetry and antisymmetry** (`horizonHadamard_symm`, `horizonCommutator_antisymm`).

The hermiticity relation, the reality/imaginarity of the two parts, the half-sum split, and
the (anti)symmetry are exact `Complex` conjugation algebra on the Eq. 1.1 form. The identification of the
antisymmetric part with the smeared CCR commutator distribution and the full Hadamard parametrix expansion are the
referenced content, not re-derived. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49 (Eq. 1.1); Wightman axioms (hermiticity), Pauli–Jordan commutator.
 Repo structure: `EntropicTime.KayWaldHawkingKMSHorizon` (`horizonTwoPointFunction`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHorizonHadamardCommutator

/-! ## §A — Wightman hermiticity -/

/-- **[Wightman hermiticity] `W(−U) = \overline{W(U)}`.** Swapping the two horizon points (`U ↦ −U`) conjugates
the two-point function: the Hermiticity `ω(Φ(y)Φ(x)) = \overline{ω(Φ(x)Φ(y))}` of the Kay–Wald horizon correlator,
since the `−iε` denominator conjugates to `+iε` and the real prefactor is fixed. -/
theorem horizonTwoPointFunction_neg_eq_conj (U ε : ℝ) :
    horizonTwoPointFunction (-U) ε = (starRingEnd ℂ) (horizonTwoPointFunction U ε) := by
  have hsq : (((-U : ℝ) : ℂ) - Complex.I * (ε : ℂ)) ^ 2
      = ((starRingEnd ℂ) ((U : ℂ) - Complex.I * (ε : ℂ))) ^ 2 := by
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  unfold horizonTwoPointFunction
  rw [map_div₀, map_pow, Complex.conj_ofReal, hsq]

/-! ## §B — the Hadamard / commutator parts and the split -/

/-- **The Hadamard (symmetric) part** `H(U) = W(U) + W(−U)` — the state-dependent symmetric two-point function,
the nonsingular (Hadamard) content determined by stationarity and positive frequency. -/
noncomputable def horizonHadamard (U ε : ℝ) : ℂ :=
  horizonTwoPointFunction U ε + horizonTwoPointFunction (-U) ε

/-- **The Pauli–Jordan commutator (antisymmetric) part** `Δ(U) = W(U) − W(−U)` — the state-independent commutator
`i·[Φ,Φ]`, fixed by the canonical commutation relations. -/
noncomputable def horizonCommutator (U ε : ℝ) : ℂ :=
  horizonTwoPointFunction U ε - horizonTwoPointFunction (-U) ε

/-- **[The Hadamard part is real] `Im H = 0`.** `H(U) = W(U) + \overline{W(U)} = 2 Re W(U)` is real — the
symmetric Hadamard function is a genuine (real) two-point distribution. -/
theorem horizonHadamard_isReal (U ε : ℝ) : (horizonHadamard U ε).im = 0 := by
  unfold horizonHadamard
  rw [horizonTwoPointFunction_neg_eq_conj]
  simp [Complex.add_im, Complex.conj_im]

/-- **[The commutator part is purely imaginary] `Re Δ = 0`.** `Δ(U) = W(U) − \overline{W(U)} = 2i Im W(U)` is
purely imaginary — the Pauli–Jordan commutator is `i` times the real, state-independent commutator distribution. -/
theorem horizonCommutator_isImaginary (U ε : ℝ) : (horizonCommutator U ε).re = 0 := by
  unfold horizonCommutator
  rw [horizonTwoPointFunction_neg_eq_conj]
  simp [Complex.sub_re, Complex.conj_re]

/-- **[The two-point function is the half-sum of its parts] `W = ½(H + Δ)`.** The Kay–Wald horizon correlator
splits into its symmetric Hadamard part and antisymmetric commutator part. -/
theorem horizonWightman_hadamard_commutator_split (U ε : ℝ) :
    horizonTwoPointFunction U ε = (horizonHadamard U ε + horizonCommutator U ε) / 2 := by
  unfold horizonHadamard horizonCommutator
  ring

/-! ## §C — symmetry and antisymmetry -/

/-- **[The Hadamard part is symmetric] `H(−U) = H(U)`.** The symmetric part is invariant under swapping the two
horizon points. -/
theorem horizonHadamard_symm (U ε : ℝ) : horizonHadamard (-U) ε = horizonHadamard U ε := by
  unfold horizonHadamard
  rw [neg_neg]
  ring

/-- **[The commutator part is antisymmetric] `Δ(−U) = −Δ(U)`.** The Pauli–Jordan commutator flips sign under
swapping the two horizon points — the antisymmetry of the commutator distribution. -/
theorem horizonCommutator_antisymm (U ε : ℝ) :
    horizonCommutator (-U) ε = -horizonCommutator U ε := by
  unfold horizonCommutator
  rw [neg_neg]
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHorizonHadamardCommutator

end
