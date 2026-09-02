/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Fermion.ContinuumPartition

/-!
# The torus (finite-box) fermionic partition function over the momentum lattice `ℤ³`

A relativistic fermion in a box `T³` (periodic boundary conditions) has **discrete momenta** `k ∈ ℤ³`
— exactly the **Fourier modes** of `FourierDerivT3` (the Navier–Stokes `T³` Fourier development). This
file formalizes the fermionic partition function over that lattice. Its thermodynamic limit
(box `→ ℝ³`) is the continuum integral of `Dirac.PartitionIntegrability`.

## The lattice partition function

For a Fourier mode `k : Fin 3 → ℤ` the dispersion is `E_k = √(|k|² + m²)` (`torusDiracEnergy`,
`|k|² = ∑ᵢ kᵢ²`). The free-energy density is `log(1 + e^{−βE_k}) = logFermionicPartition E_k β`,
nonnegative (`torus_logWeight_nonneg`). Over a **finite box** (a `Finset` of modes) the partition
function factorizes:

  `∏_{k} (1 + e^{−βE_k}) = exp(∑_k log(1 + e^{−βE_k}))`   (`torus_finite_box_partition`).

## The per-mode decay bound (input to the lattice summability)

The free-energy density decays exponentially in the lattice momentum:

  `log(1 + e^{−βE_k}) ≤ e^{−βE_k} ≤ e^{−β|k|}`   (`torus_logWeight_le_exp_latticeNorm`),

using `log(1+x) ≤ x` and `E_k ≥ |k|` (`torusDiracEnergy_ge`). This is the **input** to the
infinite-lattice summability `∑'_{k∈ℤ³} log(1 + e^{−βE_k}) < ∞` via Mathlib's
`ZLattice.summable_norm_rpow` (the lattice analog of the `ℝ³` `integrable_one_add_norm` of
`Dirac.PartitionIntegrability`): `e^{−β|k|} ≤ C|k|^{−4}` is summable over `ℤ³` (`finrank = 3 < 4`).

## Honest scope

The lattice dispersion, the free-energy density, the finite-box product factorization, and the per-mode
exponential decay bound are proved here. The **infinite-lattice summability** `∑'_{k∈ℤ³}` (the
thermodynamic limit's convergence) is the remaining step — it uses `ZLattice.summable_norm_rpow`
plus the bound proved here (and the single `k = 0` mode, handled separately), but the full
lattice-summability assembly (the `ZLattice` setup over `ℤ³ ⊆ ℝ³`) is not carried out. This file
supplies the discrete-momentum structure and the decay estimate.

## References

* `FourierDerivT3` / `PeriodicSobolev` (the Navier–Stokes `T³` Fourier-mode lattice, `ZLattice`
  summability). This development: `Fermion.ContinuumPartition`, `Dirac.PartitionIntegrability`.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.Fermion.ContinuumPartition

namespace Physlib.QuantumMechanics.ComplexAction.TorusFourier.TorusFermionicPartition


/-- **The squared lattice momentum** `|k|² = ∑ᵢ kᵢ²` for a Fourier mode `k : Fin 3 → ℤ`. -/
def latticeNormSq (k : Fin 3 → ℤ) : ℝ := ∑ i, (k i : ℝ) ^ 2

/-- **The torus Dirac dispersion** `E_k = √(|k|² + m²)` at the Fourier mode `k`. -/
def torusDiracEnergy (m : ℝ) (k : Fin 3 → ℤ) : ℝ := Real.sqrt (latticeNormSq k + m ^ 2)

/-- **`E_k ≥ |k|`** — the lattice dispersion dominates the lattice momentum. -/
lemma torusDiracEnergy_ge (m : ℝ) (k : Fin 3 → ℤ) :
    Real.sqrt (latticeNormSq k) ≤ torusDiracEnergy m k :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg m))


/-- **The free-energy density is nonnegative** `0 ≤ log(1 + e^{−βE_k})`. -/
lemma torus_logWeight_nonneg (m β : ℝ) (k : Fin 3 → ℤ) :
    0 ≤ logFermionicPartition (torusDiracEnergy m k) β :=
  logFermionicPartition_nonneg _ _

/-- **`log(1 + e^{−βE_k}) ≤ e^{−βE_k}`** (`log(1+x) ≤ x`). -/
lemma torus_logWeight_le_exp (m β : ℝ) (k : Fin 3 → ℤ) :
    logFermionicPartition (torusDiracEnergy m k) β ≤ Real.exp (-(β * torusDiracEnergy m k)) := by
  rw [logFermionicPartition]
  have := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < 1 + Real.exp (-(β * torusDiracEnergy m k)) by positivity)
  linarith

/-- **The per-mode exponential decay bound** `log(1 + e^{−βE_k}) ≤ e^{−β|k|}` — the input to the
infinite-lattice summability over `ℤ³` (via `ZLattice.summable_norm_rpow`, since `e^{−β|k|}` is
dominated by the summable `|k|^{−4}`). -/
lemma torus_logWeight_le_exp_latticeNorm (m β : ℝ) (hβ : 0 < β) (k : Fin 3 → ℤ) :
    logFermionicPartition (torusDiracEnergy m k) β ≤ Real.exp (-(β * Real.sqrt (latticeNormSq k))) := by
  refine le_trans (torus_logWeight_le_exp m β k) ?_
  apply Real.exp_le_exp.mpr
  have h : β * Real.sqrt (latticeNormSq k) ≤ β * torusDiracEnergy m k :=
    mul_le_mul_of_nonneg_left (torusDiracEnergy_ge m k) hβ.le
  linarith


/-- **The finite-box partition function factorizes** `∏_{k∈s} (1 + e^{−βE_k}) = exp(∑_{k∈s} log(1 +
e^{−βE_k}))` over a finite set `s` of Fourier modes — the particle-in-a-box partition function. -/
lemma torus_finite_box_partition (m β : ℝ) (s : Finset (Fin 3 → ℤ)) :
    ∏ k ∈ s, (1 + Real.exp (-(β * torusDiracEnergy m k)))
      = Real.exp (∑ k ∈ s, logFermionicPartition (torusDiracEnergy m k) β) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [logFermionicPartition, Real.exp_log (by positivity)]

/-- **The finite-box free energy is nonnegative** `∑_{k∈s} log(1 + e^{−βE_k}) ≥ 0`. -/
lemma torus_finite_box_logPartition_nonneg (m β : ℝ) (s : Finset (Fin 3 → ℤ)) :
    0 ≤ ∑ k ∈ s, logFermionicPartition (torusDiracEnergy m k) β :=
  Finset.sum_nonneg (fun k _ => torus_logWeight_nonneg m β k)

end Physlib.QuantumMechanics.ComplexAction.TorusFourier.TorusFermionicPartition

end
