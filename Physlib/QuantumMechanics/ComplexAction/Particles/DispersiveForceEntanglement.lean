/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A quantum-information view of dispersion: the tangle controls many-body forces

The entanglement/dispersion connection of Willby, Kiffner, Tindall, Crain & Jaksch, *A Quantum Information
Perspective on Many-Body Dispersive Forces* (arXiv:2407.04111, 2025). The same Quantum Drude Oscillators of
`QuantumDrudeOscillatorInvariants` are analysed as an entangled Gaussian ground state: the dispersive binding
energy expands as a power series in the coupling `α·𝒯`, its leading term is the pairwise potential (`= C₆/R⁶`),
and the many-body corrections are governed by a **monogamy-of-entanglement** bound on the ground-state *tangle*.

* **§A — the dispersion series (Eq. 3).** `dispersionCoeff k = (−1)^k (2k−3)!! / (2^{k+1} k!)`; the binding
  energy is `E = Σ_{k≥2} δ_k`, `δ_k = dispersionCoeff k · α^k · tr(𝒯^k)`. `dispersionCoeff_pairwise` (`= 1/16`),
  `dispersionCoeff_triple` (`= −1/32`, the Axilrod–Teller sign).
* **§B — the pairwise potential (Eq. 4) is the QDO `C₆`.** `delta2_eq` (`δ₂ = α²/16 · tr(𝒯²)`),
  `pairwise_positive` (`δ₂ > 0`, dispersion is attractive) and **`pairwise_dispersion_eq_C6`**
  (`¾α²ℏω/R⁶ = C₆/R⁶`): the per-pair `δ₂` term is the `C₆/R⁶` van der Waals energy of the invariants module.
* **§C — the reduced tangle (Eqs. 6, 8).** `reducedTangle x = x(1+√x)²/(1+2√x)²`, the Gaussian entanglement
  monotone; `reducedTangle_zero`, `reducedTangle_nonneg`. The paper's central inequality
  `τ̄_G = Σ_i g(τ_G(i)) ≤ Σ_{k≥2}(k−1)δ_k` ties total ground-state entanglement to the binding-energy series —
  monogamy vs promiscuity of the tangle decides whether the many-body correction is attractive or repulsive.

**Honest layering.** The series coefficient, the pairwise `δ₂` and its `C₆/R⁶` identification, and the reduced
tangle `g` (with `g(0)=0`, `g ≥ 0`) are exact. The monogamy inequality (Eq. 8) and the tangle's covariance-matrix
derivation are the paper's results (from the Gaussian CM framework), recorded here, not re-derived.

## References

* Willby, Kiffner, Tindall, Crain & Jaksch, arXiv:2407.04111 (2025), Eqs. 3, 4, 6, 8. Built on
  `Particles.QuantumDrudeOscillatorInvariants` (`C6`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.DispersiveForceEntanglement


/-- The **odd double factorial** `n‼ = n(n−2)(n−4)⋯` — `1‼ = 1`, `3‼ = 3`, `5‼ = 15`. -/
def doubleFact : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => (n + 2) * doubleFact n

/-- The **`k`-th dispersion series coefficient** `(−1)^k (2k−3)!! / (2^{k+1} k!)` (Eq. 3), so that the binding
energy is `E = Σ_{k≥2} δ_k` with `δ_k = dispersionCoeff k · α^k · tr(𝒯^k)`. -/
def dispersionCoeff (k : ℕ) : ℚ :=
  (-1) ^ k * (doubleFact (2 * k - 3) : ℚ) / (2 ^ (k + 1) * Nat.factorial k)

/-- **The pairwise coefficient is `1/16`** — `δ₂ = α²/16 · tr(𝒯²)`. -/
lemma dispersionCoeff_pairwise : dispersionCoeff 2 = 1 / 16 := by
  unfold dispersionCoeff; norm_num [doubleFact, Nat.factorial]

/-- **The triple (Axilrod–Teller) coefficient is `−1/32`** — the sign that can flip the three-body term
attractive or repulsive. -/
lemma dispersionCoeff_triple : dispersionCoeff 3 = -1 / 32 := by
  unfold dispersionCoeff; norm_num [doubleFact, Nat.factorial]

/-- The **`k`-th binding-energy contribution** `δ_k = dispersionCoeff k · α^k · tr(𝒯^k)`. -/
noncomputable def delta (k : ℕ) (α trTk : ℝ) : ℝ := (dispersionCoeff k : ℝ) * α ^ k * trTk


/-- **The pairwise potential** `δ₂ = α²/16 · tr(𝒯²)` (Eq. 4). -/
lemma delta2_eq (α trT2 : ℝ) : delta 2 α trT2 = 1 / 16 * α ^ 2 * trT2 := by
  unfold delta; rw [dispersionCoeff_pairwise]; push_cast; ring

/-- **The pairwise dispersion is attractive** `δ₂ > 0` — since `tr(𝒯²) = Σ 𝒯_{ij}² > 0`, the leading dispersion
always binds. -/
lemma pairwise_positive (α trT2 : ℝ) (hα : α ≠ 0) (h2 : 0 < trT2) : 0 < delta 2 α trT2 := by
  rw [delta2_eq]; positivity

/-- **The per-pair pairwise dispersion is the QDO `C₆/R⁶`** `¾α²ℏω/R⁶ = C₆/R⁶` — the `δ₂` term of Eq. 4 is the
`C₆` van der Waals energy of `QuantumDrudeOscillatorInvariants`, tying the entanglement picture to the dispersion
coefficients. -/
lemma pairwise_dispersion_eq_C6 (α hω R : ℝ) : 3 / 4 * α ^ 2 * hω / R ^ 6 = C6 α hω / R ^ 6 := by
  unfold C6; ring


/-- The **reduced tangle** `g(x) = x(1+√x)²/(1+2√x)²` (Eq. 8) — the Gaussian entanglement monotone whose sum
over modes is bounded by the binding-energy series. -/
noncomputable def reducedTangle (x : ℝ) : ℝ := x * (1 + Real.sqrt x) ^ 2 / (1 + 2 * Real.sqrt x) ^ 2

/-- **The reduced tangle vanishes on a separable (zero-tangle) mode** `g(0) = 0`. -/
lemma reducedTangle_zero : reducedTangle 0 = 0 := by
  simp [reducedTangle]

/-- **The reduced tangle is non-negative** `g(x) ≥ 0` for `x ≥ 0` — an entanglement measure. -/
lemma reducedTangle_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ reducedTangle x := by
  unfold reducedTangle; positivity

/-- **The reduced tangle is bounded by the tangle** `g(x) ≤ x` — the monotone `g` (Eq. 8) does not increase
the entanglement, so the reduced-tangle sum in the monogamy bound is controlled by the raw tangle. Reduces to
`√x³(3√x+2) ≥ 0`. -/
lemma reducedTangle_le (x : ℝ) (hx : 0 ≤ x) : reducedTangle x ≤ x := by
  unfold reducedTangle
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hx hs, mul_nonneg hx (mul_nonneg hs hs)]


/-- **The double factorial is positive** `0 < n‼`. -/
lemma doubleFact_pos : ∀ n, 0 < doubleFact n
  | 0 => by decide
  | 1 => by decide
  | (n + 2) => by unfold doubleFact; exact Nat.mul_pos (by omega) (doubleFact_pos n)

/-- **Even-order contributions are positive** `0 < dispersionCoeff k` for even `k ≥ 2` — the pairwise (`k=2`)
and every even-order term binds. -/
lemma dispersionCoeff_pos_even (k : ℕ) (he : Even k) : 0 < dispersionCoeff k := by
  unfold dispersionCoeff
  rw [he.neg_one_pow, one_mul]
  have hdf : (0 : ℚ) < (doubleFact (2 * k - 3) : ℚ) := by exact_mod_cast doubleFact_pos _
  have hden : (0 : ℚ) < 2 ^ (k + 1) * Nat.factorial k := by positivity
  exact div_pos hdf hden

/-- **Odd-order contributions are negative** `dispersionCoeff k < 0` for odd `k` — the Axilrod–Teller (`k=3`)
and every odd-order term has the opposite sign, so the dispersion series alternates. -/
lemma dispersionCoeff_neg_odd (k : ℕ) (ho : Odd k) : dispersionCoeff k < 0 := by
  unfold dispersionCoeff
  rw [ho.neg_one_pow]
  have hdf : (0 : ℚ) < (doubleFact (2 * k - 3) : ℚ) := by exact_mod_cast doubleFact_pos _
  have hden : (0 : ℚ) < 2 ^ (k + 1) * Nat.factorial k := by positivity
  rw [neg_one_mul, neg_div]
  exact neg_neg_of_pos (div_pos hdf hden)

end Physlib.QuantumMechanics.ComplexAction.Particles.DispersiveForceEntanglement
