/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The standard homogeneous decoherence functional, and its complex-action extension (Rudolph–Wright)

Rudolph & Maitland Wright, *Homogeneous decoherence functionals in standard and history quantum
mechanics* (arXiv:quant-ph/9807024). In Isham's history quantum mechanics a **homogeneous history** is a
finite sequence of single-time projections, with **class operator** `C_h = h_{t_n} ⋯ h_{t_1}`, and the
**standard homogeneous decoherence functional** in the state `ρ` is (Eq. 1)

 `d_ρ(h,k) = tr(C_h ρ C_k†)`,

the complex bivariate functional measuring the interference of the histories `h`, `k`. This module
formalizes it as a concrete instance of the abstract `QuantumMeasureHistoryHilbert.IsDecoherenceFunctional`
axioms, and extends it to a **complex weight** `ρ` (a complex-action / non-Hermitian source), where the
*failure* of Hermiticity is exactly the anti-Hermitian (complex-action) part of `ρ`.

* **§A — the functional and the Wigner probability.** `homogeneousDecoherence C ρ h k = tr(C_h ρ C_k†)`;
 the diagonal `d_ρ(h,h) = tr(C_h ρ C_h†)` is the Wigner probability, real and non-negative for a state
 (positive-semidefinite `ρ`) — `homogeneousDecoherence_diag_nonneg`.
* **§B — Hermiticity and the complex-action defect.** For any `ρ`,
 `d(h,k) − d(k,h)* = tr(C_h (ρ − ρ†) C_k†)` (`homogeneousDecoherence_hermiticity_defect`): the
 Hermiticity defect is the trace of the **anti-Hermitian (complex-action) part** `ρ − ρ†` of the
 weight. For a genuine state (`ρ` Hermitian) it vanishes and `d(h,k) = d(k,h)*`
 (`homogeneousDecoherence_hermitian`); a complex-action weight breaks it — the same imaginary-action
 obstruction as `complexActionWeight`.
* **§C — strong positivity (the Gram structure).** For a state `ρ ⪰ 0`, the quadratic form
 `Σ c_h* c_k d(h,k) = tr(M ρ M†) ≥ 0` with `M = Σ c_h* C_h` (`homogeneousDecoherence_posSemidef`) — the
 standard homogeneous decoherence functional is Hermitian and strongly positive, an
 `IsDecoherenceFunctional` on the (homogeneous) histories.

Proven: the Wigner-probability positivity, the Hermiticity defect and hence
Hermiticity for states, and strong positivity via the congruence `M ρ M†`. Interpretive: the class
operators `C_h` are taken as given matrices (the product `h_{t_n}⋯h_{t_1}` of single-time projections is
the datum); biadditivity over the full history event algebra (needed for the complete
`IsDecoherenceFunctional` on all events, §II) is the Isham tensor-embedding structure, not modelled
here; the ILS/quadratic-form representation theorems of §III–§V are beyond this algebraic core.

## References

* O. Rudolph, J. D. M. Wright, "Homogeneous decoherence functionals in standard and history quantum
 mechanics", arXiv:quant-ph/9807024, §II, Eq. (1). Reuses `QuantumMeasureHistoryHilbert`
 (`IsDecoherenceFunctional` axioms) and Mathlib `Matrix.PosSemidef`, `Matrix.trace`.

No new axioms.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.RudolphHomogeneousDecoherence

variable {ι : Type*} {N : ℕ}

/-! ## §A — the standard homogeneous decoherence functional -/

/-- **The standard homogeneous decoherence functional** `d_ρ(h,k) = tr(C_h ρ C_k†)` (Rudolph–Wright
Eq. 1): the complex interference of the homogeneous histories `h`, `k` with class operators `C_h`, `C_k`
in the state `ρ`. -/
noncomputable def homogeneousDecoherence (C : ι → Matrix (Fin N) (Fin N) ℂ)
    (ρ : Matrix (Fin N) (Fin N) ℂ) (h k : ι) : ℂ :=
  (C h * ρ * (C k)ᴴ).trace

/-- **The Wigner probability is non-negative** `d_ρ(h,h) = tr(C_h ρ C_h†) ≥ 0` (Rudolph–Wright §II.1):
for a genuine state (`ρ` positive semidefinite) the diagonal of the decoherence functional is a real,
non-negative probability — the congruence `C_h ρ C_h†` is positive semidefinite and its trace is
non-negative. -/
theorem homogeneousDecoherence_diag_nonneg (C : ι → Matrix (Fin N) (Fin N) ℂ)
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.PosSemidef) (h : ι) :
    0 ≤ (homogeneousDecoherence C ρ h h).re := by
  have hpsd : (C h * ρ * (C h)ᴴ).PosSemidef := hρ.mul_mul_conjTranspose_same (C h)
  simpa [homogeneousDecoherence] using (Complex.le_def.mp hpsd.trace_nonneg).1

/-! ## §B — Hermiticity and the complex-action defect -/

/-- **The Hermiticity defect is the anti-Hermitian (complex-action) part** `d(h,k) − d(k,h)* =
tr(C_h (ρ − ρ†) C_k†)` (Rudolph–Wright, complex extension): the failure of the decoherence functional
to be Hermitian is exactly the trace of the anti-Hermitian part `ρ − ρ†` of the weight. A complex-action
/ non-Hermitian `ρ` sources this defect; a state `ρ = ρ†` kills it. -/
theorem homogeneousDecoherence_hermiticity_defect (C : ι → Matrix (Fin N) (Fin N) ℂ)
    (ρ : Matrix (Fin N) (Fin N) ℂ) (h k : ι) :
    homogeneousDecoherence C ρ h k - starRingEnd ℂ (homogeneousDecoherence C ρ k h)
      = (C h * (ρ - ρᴴ) * (C k)ᴴ).trace := by
  unfold homogeneousDecoherence
  rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, ← Matrix.trace_sub]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, mul_assoc]

/-- **The standard homogeneous decoherence functional is Hermitian** `d(h,k) = d(k,h)*` for a genuine
state `ρ` (`ρ` Hermitian) (Rudolph–Wright §II): the decoherence Hermiticity condition holds because the
anti-Hermitian defect vanishes. -/
theorem homogeneousDecoherence_hermitian (C : ι → Matrix (Fin N) (Fin N) ℂ)
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian) (h k : ι) :
    homogeneousDecoherence C ρ h k = starRingEnd ℂ (homogeneousDecoherence C ρ k h) := by
  have hdef := homogeneousDecoherence_hermiticity_defect C ρ h k
  have hz : ρ - ρᴴ = 0 := by rw [hρ.eq, sub_self]
  rw [hz, mul_zero, zero_mul, Matrix.trace_zero] at hdef
  exact sub_eq_zero.mp hdef

/-! ## §C — strong positivity (the Gram structure) -/

/-- **The standard homogeneous decoherence functional is strongly positive** (Rudolph–Wright §II): for a
state `ρ ⪰ 0`, the quadratic form `Σ_{h,k} c_h* c_k d_ρ(h,k) = tr(M ρ M†) ≥ 0` with
`M = Σ_h c_h* C_h`. Being the congruence `M ρ M†` of a positive-semidefinite `ρ`, the form is
non-negative — so `d_ρ` satisfies the strong-positivity property of
`QuantumMeasureHistoryHilbert.IsDecoherenceFunctional`. -/
theorem homogeneousDecoherence_posSemidef (C : ι → Matrix (Fin N) (Fin N) ℂ)
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.PosSemidef) (s : Finset ι) (c : ι → ℂ) :
    0 ≤ (∑ h ∈ s, ∑ k ∈ s,
      starRingEnd ℂ (c h) * c k * homogeneousDecoherence C ρ h k).re := by
  set M := ∑ h ∈ s, starRingEnd ℂ (c h) • C h with hM
  have key : (M * ρ * Mᴴ).trace = ∑ h ∈ s, ∑ k ∈ s,
        starRingEnd ℂ (c h) * c k * homogeneousDecoherence C ρ h k := by
    rw [hM, Matrix.conjTranspose_sum]
    simp only [Matrix.conjTranspose_smul, starRingEnd_apply, star_star,
      Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul, homogeneousDecoherence]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [← key]
  have hpsd : (M * ρ * Mᴴ).PosSemidef := hρ.mul_mul_conjTranspose_same M
  simpa using (Complex.le_def.mp hpsd.trace_nonneg).1

end Physlib.QuantumMechanics.ComplexAction.RudolphHomogeneousDecoherence
