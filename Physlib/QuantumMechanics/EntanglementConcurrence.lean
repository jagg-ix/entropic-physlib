/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Two-qubit concurrence and the entanglement of formation

Ports `lean4/QCDVortex/Concurrence.lean` of the qcd-vortex-entanglement tree (own authorship,
Belle II `τ⁺τ⁻` analysis context), re-authored on Mathlib's `Real.binEntropy`: the source's
hand-rolled binary entropy and its boundary analysis collapse to library lemmas, and the port
gains `entanglementOfFormation_le_one` (from `binEntropy_le_log_two`) which the source lacked.

For a two-qubit pure state in a product basis, `|ψ⟩ = α|00⟩ + β|01⟩ + γ|10⟩ + δ|11⟩`, the
**Wootters concurrence** is `C = 2·|αδ − βγ|`:

* `concurrence_nonneg`, `concurrence_le_one_of_norm` — `0 ≤ C ≤ 1` on normalized states
  (triangle inequality plus AM–GM on the amplitude pairs);
* `concurrence_eq_zero_iff` — `C = 0 ↔ αδ = βγ`, the product-state (vanishing two-by-two
  determinant) condition;
* `concurrence_bell_state` — the Bell state `(|00⟩ + |11⟩)/√2` has `C = 1`.

The **entanglement of formation** in bits is `E(C) = h₂((1 + √(1−C²))/2)` with `h₂` the
binary entropy normalized by `log 2`:

* `entanglementOfFormation_zero` / `_one` — product states carry `0` ebits, Bell states
  exactly `1`;
* `entanglementOfFormation_nonneg` / `_le_one` — `E ∈ [0,1]` on `C ∈ [0,1]`;
* `entanglementOfFormation_eq_zero_iff` — `E(C) = 0 ↔ C = 0` on `[0,1]`: entanglement of
  formation vanishes only on product states (via `Real.binEntropy_eq_zero` and
  `Real.sqrt_eq_one`, replacing the source's manual logarithm sign analysis).

**Honest layering.**  Exact amplitude algebra and library entropy facts.  `C` here is the
pure-state concurrence (the mixed-state convex-roof extension and the spin-density-matrix
reconstruction of the Belle II analysis are not taken); the identification of `E(C)` with the
reduced von Neumann entropy is the Wootters theorem, cited not re-proven.  Two-qubit carriers
with Hilbert-space structure live in `QuantumInfo` (`MState`, `Braket`) and
`Foundations.MinimalModalOnticDynamics`; this module works at the amplitude level, where the
Belle II estimator does.

## References

* W. K. Wootters, *Entanglement of formation of an arbitrary state of two qubits*,
  Phys. Rev. Lett. **80** (1998) 2245.
* Source: `qcd-vortex-entanglement/lean4/QCDVortex/Concurrence.lean` (own authorship),
  re-authored on `Real.binEntropy`.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.EntanglementConcurrence

open Real

/-! ## §A — the Wootters concurrence of a pure two-qubit state -/

/-- **The pure-state concurrence** `C = 2·|αδ − βγ|` of the two-qubit state
`α|00⟩ + β|01⟩ + γ|10⟩ + δ|11⟩` — twice the modulus of the amplitude determinant. -/
noncomputable def concurrence (α β γ δ : ℂ) : ℝ :=
  2 * ‖α * δ - β * γ‖

theorem concurrence_nonneg (α β γ δ : ℂ) : 0 ≤ concurrence α β γ δ :=
  mul_nonneg (by norm_num) (norm_nonneg _)

/-- **Concurrence is at most one on normalized states**: triangle inequality on the
determinant, then AM–GM on the two amplitude pairs against the normalization. -/
theorem concurrence_le_one_of_norm (α β γ δ : ℂ)
    (hnorm : Complex.normSq α + Complex.normSq β +
             Complex.normSq γ + Complex.normSq δ = 1) :
    concurrence α β γ δ ≤ 1 := by
  simp only [concurrence]
  have hnorm_sq : ‖α‖^2 + ‖β‖^2 + ‖γ‖^2 + ‖δ‖^2 = 1 := by
    simp only [← Complex.normSq_eq_norm_sq]
    linarith [hnorm]
  have htri : ‖α * δ - β * γ‖ ≤ ‖α‖ * ‖δ‖ + ‖β‖ * ‖γ‖ :=
    calc ‖α * δ - β * γ‖
        ≤ ‖α * δ‖ + ‖β * γ‖ := norm_sub_le _ _
      _ = ‖α‖ * ‖δ‖ + ‖β‖ * ‖γ‖ := by simp
  have hamgm_ad : ‖α‖ * ‖δ‖ ≤ (‖α‖^2 + ‖δ‖^2) / 2 := by
    nlinarith [sq_nonneg (‖α‖ - ‖δ‖), norm_nonneg α, norm_nonneg δ]
  have hamgm_bg : ‖β‖ * ‖γ‖ ≤ (‖β‖^2 + ‖γ‖^2) / 2 := by
    nlinarith [sq_nonneg (‖β‖ - ‖γ‖), norm_nonneg β, norm_nonneg γ]
  linarith [norm_nonneg (α * δ - β * γ), hnorm_sq]

/-- **Vanishing concurrence is the product-state condition** `C = 0 ↔ αδ = βγ` — the
two-by-two amplitude determinant vanishes exactly when the state factorizes. -/
theorem concurrence_eq_zero_iff (α β γ δ : ℂ) :
    concurrence α β γ δ = 0 ↔ α * δ = β * γ := by
  simp only [concurrence, mul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    · rwa [norm_eq_zero, sub_eq_zero] at h
  · intro h
    right
    rwa [norm_eq_zero, sub_eq_zero]

/-- **The Bell state is maximally entangled**: `(|00⟩ + |11⟩)/√2` has `C = 1`. -/
theorem concurrence_bell_state :
    concurrence (1 / Real.sqrt 2) 0 0 (1 / Real.sqrt 2) = 1 := by
  simp only [concurrence, mul_zero, sub_zero]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  suffices h : ‖(1 : ℂ) / Real.sqrt 2 * (1 / Real.sqrt 2)‖ = 1 / 2 by linarith
  rw [div_mul_div_comm, one_mul, norm_div, norm_one]
  rw [show ‖(Real.sqrt 2 : ℂ) * Real.sqrt 2‖ = 2 from by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hsq]]

/-- **[The two-mode-squeezed concurrence is `tanh η`]** the Wootters concurrence of the two-mode
squeezed (Bogoliubov) pair `(cosh(η/2)|00⟩ + sinh(η/2)|11⟩)/√(cosh η)` — the two-level truncation of
the two-mode squeezed vacuum at squeezing `η/2` — is `C = tanh η` for `η ≥ 0`. With the Bell state's
`C₀ = 1` (`concurrence_bell_state`), the concurrence-decay ratio is `C₀/C = coth η`, the Schmidt
number of the rapidity `η` (`tanh η` the Bogoliubov squeezing velocity of
`ComplexAction.Bogoliubov.RapidityBoseFermiCothTanh`). -/
theorem concurrence_twoModeSqueezed_eq_tanh (η : ℝ) (hη : 0 ≤ η) :
    concurrence (↑(Real.cosh (η / 2) / Real.sqrt (Real.cosh η)))
        0 0 (↑(Real.sinh (η / 2) / Real.sqrt (Real.cosh η))) = Real.tanh η := by
  have hcosh : (0 : ℝ) < Real.cosh η := Real.cosh_pos η
  have hsinh_half : 0 ≤ Real.sinh (η / 2) := by
    rw [Real.sinh_eq]
    have hle : Real.exp (-(η / 2)) ≤ Real.exp (η / 2) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hdouble : 2 * Real.sinh (η / 2) * Real.cosh (η / 2) = Real.sinh η := by
    have h := Real.sinh_two_mul (η / 2)
    rw [show 2 * (η / 2) = η from by ring] at h
    linarith [h]
  have hprod_nn : 0 ≤ Real.cosh (η / 2) / Real.sqrt (Real.cosh η) *
      (Real.sinh (η / 2) / Real.sqrt (Real.cosh η)) :=
    mul_nonneg (div_nonneg (Real.cosh_pos _).le (Real.sqrt_nonneg _))
      (div_nonneg hsinh_half (Real.sqrt_nonneg _))
  have hprod : Real.cosh (η / 2) / Real.sqrt (Real.cosh η) *
      (Real.sinh (η / 2) / Real.sqrt (Real.cosh η)) = Real.tanh η / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hcosh.le, Real.tanh_eq_sinh_div_cosh, ← hdouble]
    ring
  simp only [concurrence, mul_zero, sub_zero]
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hprod_nn, hprod]
  ring

/-! ## §B — the entanglement of formation -/

/-- **The entanglement of formation in bits** `E(C) = h₂((1 + √(1−C²))/2)`, with the binary
entropy `Real.binEntropy` (natural units) normalized by `log 2`. -/
noncomputable def entanglementOfFormation (C : ℝ) : ℝ :=
  Real.binEntropy ((1 + Real.sqrt (1 - C^2)) / 2) / Real.log 2

/-- Product states carry no entanglement: `E(0) = 0`. -/
theorem entanglementOfFormation_zero : entanglementOfFormation 0 = 0 := by
  unfold entanglementOfFormation
  norm_num

/-- Bell states carry exactly one ebit: `E(1) = 1`. -/
theorem entanglementOfFormation_one : entanglementOfFormation 1 = 1 := by
  unfold entanglementOfFormation
  norm_num [Real.sqrt_zero]
  rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos (by norm_num)).ne'

/-- `E(C) ≥ 0` on `C ∈ [0,1]`. -/
theorem entanglementOfFormation_nonneg {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    0 ≤ entanglementOfFormation C := by
  unfold entanglementOfFormation
  have hC2 : C^2 ≤ 1 := by nlinarith
  have hsqrt : Real.sqrt (1 - C^2) ≤ 1 :=
    calc Real.sqrt (1 - C^2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [sq_nonneg C])
      _ = 1 := Real.sqrt_one
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  exact Real.binEntropy_nonneg (by linarith [Real.sqrt_nonneg (1 - C^2)]) (by linarith)

/-- **`E(C) ≤ 1`: entanglement of formation never exceeds one ebit** — from the library
bound `binEntropy ≤ log 2`; the source formalization lacked this direction. -/
theorem entanglementOfFormation_le_one (C : ℝ) :
    entanglementOfFormation C ≤ 1 := by
  unfold entanglementOfFormation
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_one hlog2]
  exact Real.binEntropy_le_log_two

/-- **Entanglement of formation vanishes only on product states**: `E(C) = 0 ↔ C = 0` on
`[0,1]` — by `Real.binEntropy_eq_zero` the argument must hit a boundary, `(1+√(1−C²))/2 ≥ ½`
rules out `0`, and hitting `1` forces `√(1−C²) = 1`, i.e. `C = 0`. -/
theorem entanglementOfFormation_eq_zero_iff {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    entanglementOfFormation C = 0 ↔ C = 0 := by
  unfold entanglementOfFormation
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hsqrt_nn : 0 ≤ Real.sqrt (1 - C^2) := Real.sqrt_nonneg _
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hbin | hl2
    · rcases Real.binEntropy_eq_zero.mp hbin with hx0 | hx1
      · linarith
      · have hone : Real.sqrt (1 - C^2) = 1 := by linarith
        have h1C2 : 1 - C^2 = 1 := Real.sqrt_eq_one.mp hone
        have : C^2 = 0 := by linarith
        exact pow_eq_zero_iff (by norm_num) |>.mp this
    · exact absurd hl2 hlog2
  · rintro rfl
    norm_num

end Physlib.QuantumMechanics.EntanglementConcurrence

end
