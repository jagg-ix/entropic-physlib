/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction

/-!
# The continuum thermodynamic limit: `Z = ∏_{k∈ℝ³}(1 + e^{−βE_k})` as a regularized infinite product

`Fermion.PartitionFunction` proved the single- and finite-mode fermionic partition function. This
file formalizes the **continuum thermodynamic limit** — the infinite product over the momentum
continuum, regularized in the standard way as the exponential of the free-energy integral:

  `Z = ∏_{k} (1 + e^{−βE_k})  ⟶  exp( ∫_K log(1 + e^{−βE(k)}) dμ(k) )`.

The infinite product `∏_k` is **regularized** by `exp(∫ log)` — the density-of-states integral
`μ = V d³k/(2π)³` over the momentum space `K = ℝ³`. This is the grand potential
`Ω = −T log Z = −T ∫ log(1 + e^{−βE_k}) dμ(k)`.

## The regularization

The single-mode log-weight (free-energy density) is `log(1 + e^{−βE}) = log Z_single`
(`logFermionicPartition`), and the **discrete** product is its exponential sum:

  `∏_k (1 + e^{−βE_k}) = exp( ∑_k log(1 + e^{−βE_k}) )`   (`fermionicPartitionMulti_eq_exp_sum`).

The **continuum** replaces the sum by the integral:

  `Z = exp( ∫_K log(1 + e^{−βE(k)}) dμ(k) )`   (`continuumPartition`),

the regularized infinite product. It is positive and `≥ 1` (the integrand `log(1 + e^{−βE}) ≥ 0` is the
nonnegative free-energy density). For the **counting measure** on finitely many modes the integral is
the sum, recovering the finite product `fermionicPartitionMulti` (`continuumPartition_count`) — so the
continuum framework specializes to the discrete one: it is the right regularization.

## Honest scope

This builds the regularization `Z = exp(∫ log(1 + e^{−βE(k)}) dμ)` and its properties (positivity,
`Z ≥ 1`, the nonnegative free-energy density), and proves it specializes to the finite product over the
counting measure. What is **not** proved: **convergence** of the integral for the physical dispersion
`E(k) = √(k²+m²)` over `ℝ³` with the Lebesgue density of states (the integrability of
`log(1 + e^{−β√(k²+m²)})`, which needs the large-`k` decay and a specific measure) — that is the
analytic estimate for the concrete thermodynamic limit, on top of the regularization framework built
here.

## References

* The free-energy / grand-potential regularization of the fermionic partition function. This
  development: `Fermion.PartitionFunction`, `Fermion.FockFunctor`; physlib `QFT/Matsubara`.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.ContinuumPartition

open Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction


/-- **The single-mode free-energy density** `log(1 + e^{−βE}) = log Z_single` — the log of the
single-mode fermionic partition function. -/
def logFermionicPartition (E β : ℝ) : ℝ := Real.log (1 + Real.exp (-(β * E)))

/-- **`log Z_single = log(1 + e^{−βE})`** (the log of `fermionicPartition`). -/
lemma logFermionicPartition_eq (E β : ℝ) :
    logFermionicPartition E β = Real.log (fermionicPartition E β) := rfl

/-- **The free-energy density is nonnegative** `0 ≤ log(1 + e^{−βE})` (since `1 + e^{−βE} ≥ 1`). -/
lemma logFermionicPartition_nonneg (E β : ℝ) : 0 ≤ logFermionicPartition E β := by
  rw [logFermionicPartition]
  apply Real.log_nonneg
  have := Real.exp_pos (-(β * E))
  linarith


/-- **The finite product is the exponential sum** `∏_k (1 + e^{−βE_k}) = exp(∑_k log(1 + e^{−βE_k}))`
— the discrete regularization of the partition function. -/
lemma fermionicPartitionMulti_eq_exp_sum {k : ℕ} (E : Fin k → ℝ) (β : ℝ) :
    fermionicPartitionMulti E β = Real.exp (∑ i, logFermionicPartition (E i) β) := by
  rw [fermionicPartitionMulti_eq, Real.exp_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [logFermionicPartition, Real.exp_log (by have := Real.exp_pos (-(β * E i)); linarith)]


variable {K : Type*} [MeasurableSpace K]

/-- **The continuum free energy** `log Z = ∫_K log(1 + e^{−βE(k)}) dμ(k)` — the grand potential
`Ω = −T log Z` over the momentum space `K` with density of states `μ`. -/
def continuumLogPartition (μ : Measure K) (E : K → ℝ) (β : ℝ) : ℝ :=
  ∫ k, logFermionicPartition (E k) β ∂μ

/-- **The continuum partition function** `Z = ∏_k (1 + e^{−βE_k}) = exp(∫_K log(1 + e^{−βE(k)}) dμ(k))`
— the regularized infinite product over the momentum continuum. -/
def continuumPartition (μ : Measure K) (E : K → ℝ) (β : ℝ) : ℝ :=
  Real.exp (continuumLogPartition μ E β)

/-- **The continuum free energy is nonnegative** `0 ≤ log Z` (integral of the nonnegative
free-energy density). -/
lemma continuumLogPartition_nonneg (μ : Measure K) (E : K → ℝ) (β : ℝ) :
    0 ≤ continuumLogPartition μ E β :=
  integral_nonneg (fun k => logFermionicPartition_nonneg (E k) β)

/-- **The continuum partition function is positive** `Z > 0`. -/
lemma continuumPartition_pos (μ : Measure K) (E : K → ℝ) (β : ℝ) :
    0 < continuumPartition μ E β := Real.exp_pos _

/-- **The continuum partition function is `≥ 1`** `Z ≥ 1` (the free energy is nonnegative). -/
lemma continuumPartition_ge_one (μ : Measure K) (E : K → ℝ) (β : ℝ) :
    1 ≤ continuumPartition μ E β :=
  Real.one_le_exp (continuumLogPartition_nonneg μ E β)


/-- **The continuum free energy over the counting measure is the discrete sum**
`∫ log(1+e^{−βE}) ∂count = ∑_k log(1 + e^{−βE_k})` (for finitely many modes). -/
lemma continuumLogPartition_count [Fintype K] [MeasurableSingletonClass K] (E : K → ℝ) (β : ℝ) :
    continuumLogPartition Measure.count E β = ∑ k, logFermionicPartition (E k) β := by
  rw [continuumLogPartition, integral_count]

/-- **The continuum partition function over finitely many modes is the finite product**
`Z = ∏_k (1 + e^{−βE_k})` — the regularized infinite product specializes to the finite product
(`fermionicPartitionMulti` for `K = Fin n`), showing it is the right regularization. -/
lemma continuumPartition_count [Fintype K] [MeasurableSingletonClass K] (E : K → ℝ) (β : ℝ) :
    continuumPartition Measure.count E β = ∏ k, fermionicPartition (E k) β := by
  rw [continuumPartition, continuumLogPartition_count, Real.exp_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [logFermionicPartition, fermionicPartition,
    Real.exp_log (by have := Real.exp_pos (-(β * E i)); linarith)]

end Physlib.QuantumMechanics.ComplexAction.Fermion.ContinuumPartition

end
