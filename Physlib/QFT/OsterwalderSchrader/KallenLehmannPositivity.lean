/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Källén–Lehmann reflection positivity of a positive spectral measure

The Osterwalder–Schrader reflection-positivity axiom **E2** for a two-point function with a
**positive spectral measure**.  A Euclidean two-point function admitting the Källén–Lehmann
representation

  `G_E(σ) = ∑_k ρ_k · e^{−E_k σ}`,   `ρ_k ≥ 0`,

(a finite positive combination of free single-mode kernels, one per spectral mode of energy `E_k` and
weight `ρ_k`) has a reflected form that is an exact **positive combination of perfect squares**:

  `∑_{i,j} c_i c_j G_E(τ_i + τ_j) = ∑_k ρ_k · (∑_i c_i e^{−E_k τ_i})²  ≥ 0`,

and, over complex test coefficients, the genuine sesquilinear Osterwalder–Schrader form is a positive
combination of squared norms,

  `∑_{i,j} conj(c_i) c_j G_E(τ_i + τ_j) = ∑_k ρ_k · ‖∑_i c_i e^{−E_k τ_i}‖²  ≥ 0`.

This is the multi-mode generalization of the single free mode: with one mode of unit weight it is the
rank-one Gram square of the free kernel `e^{−E τ}`.  The step from one mode to a positive spectral
measure is the step from a free field to a general (interacting) two-point function whose spectral
density `ρ` is nonnegative — the Källén–Lehmann content of E2.

**Scope.**  This is the reflection-positivity *axiom* for a finite positive spectral measure, not the
Osterwalder–Schrader *reconstruction*: no Schwinger hierarchy `S_n`, Borchers algebra, null quotient,
Hilbert completion, `C₀` semigroup, or Wightman continuation is built here.  Those follow-up steps use
the abstract carrier in `OsterwalderSchrader.ReflectionPositivity` and the Gram/completion machinery in
`QuantumMechanics.ComplexAction.HistoryHilbertFiniteIsomorphism`.

## References

* G. Källén, *On the definition of the renormalization constants in quantum electrodynamics*,
  Helv. Phys. Acta 25 (1952) 417.
* H. Lehmann, *Über Eigenschaften von Ausbreitungsfunktionen und Renormierungskonstanten quantisierter
  Felder*, Nuovo Cimento 11 (1954) 342.
* K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's functions*,
  Commun. Math. Phys. 31 (1973) 83; II, 42 (1975) 281.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QFT.OsterwalderSchrader

variable {ι κ : Type*} [Fintype ι]

/-- **The Källén–Lehmann two-point function** — a positive spectral measure of free modes,
`G_E(σ) = ∑_k ρ_k e^{−E_k σ}`, with spectral weights `ρ` and mode energies `E`. -/
noncomputable def spectralTwoPoint (ρ E : ι → ℝ) (σ : ℝ) : ℝ := ∑ k, ρ k * Real.exp (-(E k * σ))

/-- **The single-mode kernel is the one-point spectrum** — for one mode of unit weight the
Källén–Lehmann function is the free kernel `e^{−E₀ σ}` of `§OS`. -/
@[simp] theorem spectralTwoPoint_unique [Unique ι] (E : ι → ℝ) (σ : ℝ) :
    spectralTwoPoint (fun _ => 1) E σ = Real.exp (-(E default * σ)) := by
  simp [spectralTwoPoint]

/-- **The diagonal value** — `G_E(0) = ∑_k ρ_k`, the total spectral weight. -/
theorem spectralTwoPoint_zero (ρ E : ι → ℝ) :
    spectralTwoPoint ρ E 0 = ∑ k, ρ k := by
  simp [spectralTwoPoint]

/-- **The Källén–Lehmann function is nonnegative** — a positive spectral measure gives a nonnegative
two-point function. -/
theorem spectralTwoPoint_nonneg {ρ E : ι → ℝ} (hρ : ∀ k, 0 ≤ ρ k) (σ : ℝ) :
    0 ≤ spectralTwoPoint ρ E σ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hρ k) (Real.exp_nonneg _)

/-- **Per-mode reflected square** — the contribution of a single spectral mode `k` to the reflected
form is `ρ_k` times a perfect square:
`∑_{i,j} c_i c_j ρ_k e^{−E_k(τ_i+τ_j)} = ρ_k (∑_i c_i e^{−E_k τ_i})²`. -/
theorem reflected_mode_sq (ρ E : ι → ℝ) (s : Finset κ) (c τ : κ → ℝ) (k : ι) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * (ρ k * Real.exp (-(E k * (τ i + τ j)))))
      = ρ k * (∑ i ∈ s, c i * Real.exp (-(E k * τ i))) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show -(E k * (τ i + τ j)) = -(E k * τ i) + -(E k * τ j) by ring, Real.exp_add]
  ring

/-- **The reflected form is a positive combination of squares (Källén–Lehmann E2, real)** — for real
test coefficients the reflected Euclidean form factors over the spectrum as
`∑_{i,j} c_i c_j G_E(τ_i+τ_j) = ∑_k ρ_k (∑_i c_i e^{−E_k τ_i})²`. -/
theorem spectralTwoPoint_reflected_eq_spectral_sq (ρ E : ι → ℝ) (s : Finset κ) (c τ : κ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * spectralTwoPoint ρ E (τ i + τ j))
      = ∑ k, ρ k * (∑ i ∈ s, c i * Real.exp (-(E k * τ i))) ^ 2 := by
  have hswap : (∑ i ∈ s, ∑ j ∈ s, c i * c j * spectralTwoPoint ρ E (τ i + τ j))
      = ∑ k, ∑ i ∈ s, ∑ j ∈ s, c i * c j * (ρ k * Real.exp (-(E k * (τ i + τ j)))) := by
    unfold spectralTwoPoint
    simp_rw [Finset.mul_sum]
    rw [show (∑ i ∈ s, ∑ j ∈ s, ∑ k, c i * c j * (ρ k * Real.exp (-(E k * (τ i + τ j)))))
          = ∑ i ∈ s, ∑ k, ∑ j ∈ s, c i * c j * (ρ k * Real.exp (-(E k * (τ i + τ j))))
        from Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  rw [hswap]
  exact Finset.sum_congr rfl fun k _ => reflected_mode_sq ρ E s c τ k

/-- **Reflection positivity for real coefficients** — the reflected Euclidean form of a positive
spectral measure is nonnegative: `∑_{i,j} c_i c_j G_E(τ_i+τ_j) ≥ 0`. -/
theorem kallen_lehmann_reflection_positive {ρ E : ι → ℝ} (hρ : ∀ k, 0 ≤ ρ k)
    (s : Finset κ) (c τ : κ → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * spectralTwoPoint ρ E (τ i + τ j) := by
  rw [spectralTwoPoint_reflected_eq_spectral_sq]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hρ k) (sq_nonneg _)

/-- **Per-mode reflected squared norm (complex)** — over complex test coefficients a single spectral
mode contributes `ρ_k` times a squared norm, `ρ_k · normSq(∑_i c_i e^{−E_k τ_i})`. -/
theorem reflected_mode_normSq (ρ E : ι → ℝ) (s : Finset κ) (c : κ → ℂ) (τ : κ → ℝ) (k : ι) :
    (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
        * ((ρ k : ℂ) * (Real.exp (-(E k * (τ i + τ j))) : ℂ)))
      = (ρ k : ℂ) * (Complex.normSq (∑ i ∈ s, c i * (Real.exp (-(E k * τ i)) : ℂ)) : ℂ) := by
  have hexp : ∀ i j : κ, (Real.exp (-(E k * (τ i + τ j))) : ℂ)
      = (Real.exp (-(E k * τ i)) : ℂ) * (Real.exp (-(E k * τ j)) : ℂ) := by
    intro i j
    rw [show -(E k * (τ i + τ j)) = -(E k * τ i) + -(E k * τ j) by ring, Real.exp_add,
      Complex.ofReal_mul]
  have base : (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
        * (Real.exp (-(E k * (τ i + τ j))) : ℂ))
      = (starRingEnd ℂ) (∑ i ∈ s, c i * (Real.exp (-(E k * τ i)) : ℂ))
          * (∑ i ∈ s, c i * (Real.exp (-(E k * τ i)) : ℂ)) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hexp i j, map_mul, Complex.conj_ofReal]
    ring
  have hns : (Complex.normSq (∑ i ∈ s, c i * (Real.exp (-(E k * τ i)) : ℂ)) : ℂ)
      = (starRingEnd ℂ) (∑ i ∈ s, c i * (Real.exp (-(E k * τ i)) : ℂ))
          * (∑ i ∈ s, c i * (Real.exp (-(E k * τ i)) : ℂ)) := by
    rw [← Complex.mul_conj]; ring
  rw [hns, ← base, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The sesquilinear reflected form factors over the spectrum (complex)** — the genuine
Osterwalder–Schrader form equals a positive-weighted sum of squared norms:
`∑_{i,j} conj(c_i) c_j G_E(τ_i+τ_j) = ∑_k ρ_k · normSq(∑_i c_i e^{−E_k τ_i})`. -/
theorem spectralTwoPoint_reflected_eq_normSq (ρ E : ι → ℝ) (s : Finset κ) (c : κ → ℂ) (τ : κ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j * (spectralTwoPoint ρ E (τ i + τ j) : ℂ))
      = ∑ k, (ρ k : ℂ) * (Complex.normSq (∑ i ∈ s, c i * (Real.exp (-(E k * τ i)) : ℂ)) : ℂ) := by
  have hswap : (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
        * (spectralTwoPoint ρ E (τ i + τ j) : ℂ))
      = ∑ k, ∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
          * ((ρ k : ℂ) * (Real.exp (-(E k * (τ i + τ j))) : ℂ)) := by
    unfold spectralTwoPoint
    simp_rw [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    rw [show (∑ i ∈ s, ∑ j ∈ s, ∑ k, (starRingEnd ℂ) (c i) * c j
              * ((ρ k : ℂ) * (Real.exp (-(E k * (τ i + τ j))) : ℂ)))
          = ∑ i ∈ s, ∑ k, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
              * ((ρ k : ℂ) * (Real.exp (-(E k * (τ i + τ j))) : ℂ))
        from Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  rw [hswap]
  exact Finset.sum_congr rfl fun k _ => reflected_mode_normSq ρ E s c τ k

/-- **Reflection positivity for complex coefficients (Källén–Lehmann E2)** — the sesquilinear
Osterwalder–Schrader reflected form of a positive spectral measure is a nonnegative real. -/
theorem kallen_lehmann_reflection_positive_complex {ρ E : ι → ℝ} (hρ : ∀ k, 0 ≤ ρ k)
    (s : Finset κ) (c : κ → ℂ) (τ : κ → ℝ) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
        * (spectralTwoPoint ρ E (τ i + τ j) : ℂ)).re := by
  rw [spectralTwoPoint_reflected_eq_normSq, Complex.re_sum]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (hρ k) (Complex.normSq_nonneg _)

end Physlib.QFT.OsterwalderSchrader
