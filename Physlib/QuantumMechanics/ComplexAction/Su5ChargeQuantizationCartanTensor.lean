/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationsHyperbolic

/-!
# A. `SU(5)` charge quantization (particles) and the Cartan weight-space metric (tensors)

The `su(5)` weight system built for Sorkin's `R⁴` net (`affineBasis`/`IsAffineWeight` = tracelessness,
`weightConjugation` = the `5 ↔ 5̄` charge conjugation, the icosahedral `A₅` rotation `icosaRot5`
cycling the weights) is the weight system of the `SU(5)` grand unified theory. This module uses it to
extend the particle infrastructure and the tensor infrastructure.

## A.1. Particles — `SU(5)` charge quantization

Electric charge `Q` is one of the `SU(5)` generators, hence **traceless** on every representation.
The anti-fundamental `5̄ = (d^c, d^c, d^c, e⁻, ν)` therefore has charges summing to zero
(`su5AntifundCharge_isAffineWeight`), and with the three colours of the down antiquark sharing one
charge and the neutrino neutral, tracelessness *forces* `3·Q(d^c) = −Q(e⁻)`
(`su5_charge_quantization`): the quark charge is `−1/3` of the electron's **because there are three
colours**. This is the celebrated `SU(5)` explanation of electric-charge quantization, and it is
exactly the affine/traceless condition of the weight system. The `5` (particles) charges are the
`weightConjugation` (charge conjugate) of the `5̄`, and are traceless too.

## A.2. Tensors — the `su(5)` Cartan weight-space metric

`su5CartanMetric i j = δ_ij − 1/5` is the projector onto the traceless (weight) hyperplane — the
natural metric on the `su(5)` Cartan/weight space. Its rows are the affine basis vectors
(`su5CartanMetric_row_eq_affineBasis`), it is symmetric, its rows are traceless
(`su5CartanMetric_row_sum_zero`), and it is **invariant under coordinate permutations** `S₅`
(`su5CartanMetric_permInvariant`), hence under the icosahedral rotation group `A₅`
(`su5CartanMetric_icosahedral_invariant`, `fiveFold_preserves_cartanMetric`). The `5`-fold rotation
also preserves the charge trace (`su5_charge_trace_rotationInvariant`), so charge quantization is
robust under the icosahedral symmetry of the net.

## A.3. References

* H. Georgi, S. L. Glashow, "Unity of All Elementary-Particle Forces", Phys. Rev. Lett. **32**, 438
  (1974) — `SU(5)`, the `5̄ ⊕ 10` fermions and charge quantization from tracelessness. Reuses
  `LeviCivita.SorkinSimplecticNetR4` (`affineBasis`, `IsAffineWeight`, `weightConjugation`,
  `affineBasis_component_sum_zero`) and `IcosahedralRotationsHyperbolic` (`icosaRot5`,
  `IcosahedralGroup`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4
open Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
open Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationsHyperbolic

/-! ## A.4. Particles — `SU(5)` charge quantization from tracelessness -/

/-- The electric charges of the `SU(5)` anti-fundamental `5̄ = (d^c, d^c, d^c, e⁻, ν)`:
`(1/3, 1/3, 1/3, −1, 0)`. -/
def su5AntifundCharge : Fin 5 → ℚ := ![1/3, 1/3, 1/3, -1, 0]

/-- **Charge is a traceless `SU(5)` generator**: the `5̄` charges sum to zero — the affine/traceless
condition of the weight system, here read as a physical constraint. -/
lemma su5AntifundCharge_isAffineWeight : IsAffineWeight su5AntifundCharge := by
  unfold IsAffineWeight su5AntifundCharge
  simp [Fin.sum_univ_five]; norm_num

/-- **`SU(5)` charge quantization.** For any charge assignment on the `5̄` that is traceless (a
`SU(5)` generator), with the three quark colours sharing one charge and the neutrino neutral,
tracelessness forces `3·Q(quark) = −Q(lepton)`: the down antiquark carries exactly `−1/3` of the
electron's charge **because there are three colours**. -/
lemma su5_charge_quantization (q : Fin 5 → ℚ) (htrace : IsAffineWeight q)
    (hcolor : q 0 = q 1 ∧ q 1 = q 2) (hnu : q 4 = 0) : 3 * q 0 = - q 3 := by
  unfold IsAffineWeight at htrace
  rw [Fin.sum_univ_five] at htrace
  obtain ⟨h01, h12⟩ := hcolor
  rw [← h01, ← h12] at htrace
  linarith [htrace, hnu]

/-- The concrete `5̄` is charge-quantized: `3·(1/3) = 1 = −Q(e⁻)`. -/
lemma su5AntifundCharge_quantized : 3 * su5AntifundCharge 0 = - su5AntifundCharge 3 :=
  su5_charge_quantization su5AntifundCharge su5AntifundCharge_isAffineWeight
    ⟨by simp [su5AntifundCharge], by simp [su5AntifundCharge]⟩ (by simp [su5AntifundCharge])

/-- The `SU(5)` fundamental `5` charges are the **charge conjugate** (`weightConjugation`, `5 ↔ 5̄`) of
the `5̄` — the down quark `d` has charge `−1/3`, the antiparticle of `d^c`. -/
def su5FundCharge : Fin 5 → ℚ := weightConjugation su5AntifundCharge

/-- The `5` charges are traceless too — charge quantization holds for the conjugate representation
(reusing `weightConjugation_isAffineWeight`). -/
lemma su5FundCharge_isAffineWeight : IsAffineWeight su5FundCharge :=
  weightConjugation_isAffineWeight _ su5AntifundCharge_isAffineWeight

/-- A particle and its charge conjugate annihilate: `Q(5) + Q(5̄) = 0` componentwise. -/
lemma su5_particle_antiparticle_charge (i : Fin 5) :
    su5FundCharge i + su5AntifundCharge i = 0 := by simp [su5FundCharge, weightConjugation]

/-! ## A.5. Tensors — the `su(5)` Cartan weight-space metric -/

/-- **The `su(5)` Cartan/weight-space metric** `P_ij = δ_ij − 1/5` — the projector onto the traceless
(weight) hyperplane. -/
noncomputable def su5CartanMetric : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (if i = j then 1 else 0) - 1 / 5

/-- **The metric is symmetric** `P_ij = P_ji`. -/
lemma su5CartanMetric_symm (i j : Fin 5) : su5CartanMetric i j = su5CartanMetric j i := by
  simp only [su5CartanMetric]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

/-- **The rows of the metric are the affine basis vectors** (`affineBasis`) — the `su(5)` weights. -/
lemma su5CartanMetric_row_eq_affineBasis (i : Fin 5) :
    (fun j => su5CartanMetric i j) = affineBasis i := by
  funext j; simp only [su5CartanMetric, affineBasis]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

/-- **Each row is traceless** (sums to zero) — reusing `affineBasis_component_sum_zero`. -/
lemma su5CartanMetric_row_sum_zero (i : Fin 5) : ∑ j, su5CartanMetric i j = 0 := by
  have h : ∑ j, su5CartanMetric i j = ∑ j, affineBasis i j :=
    Finset.sum_congr rfl (fun j _ => congrFun (su5CartanMetric_row_eq_affineBasis i) j)
  rw [h, affineBasis_component_sum_zero]

/-- **The metric is invariant under coordinate permutations** `S₅`: `P_{σi,σj} = P_ij`. Being a
function of `i = j` only, it is fixed by any relabelling of the weights. -/
lemma su5CartanMetric_permInvariant (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    su5CartanMetric (σ i) (σ j) = su5CartanMetric i j := by
  simp only [su5CartanMetric, σ.injective.eq_iff]

/-- **The metric is icosahedrally invariant** — fixed by every element of the icosahedral rotation
group `A₅ ⊆ S₅`. -/
lemma su5CartanMetric_icosahedral_invariant (g : IcosahedralGroup) (i j : Fin 5) :
    su5CartanMetric ((g : Equiv.Perm (Fin 5)) i) ((g : Equiv.Perm (Fin 5)) j)
      = su5CartanMetric i j :=
  su5CartanMetric_permInvariant _ i j

/-! ## A.6. The `5`-fold rotation preserves the metric and the charge trace -/

/-- **The `5`-fold rotation is a symmetry of the Cartan metric tensor**: `P_{ρi,ρj} = P_ij` for
`ρ = icosaRot5`. -/
lemma fiveFold_preserves_cartanMetric (i j : Fin 5) :
    su5CartanMetric (icosaRot5 i) (icosaRot5 j) = su5CartanMetric i j :=
  su5CartanMetric_permInvariant icosaRot5 i j

/-- **Charge quantization is icosahedrally robust**: the `5`-fold rotation permutes the multiplet but
preserves the charge trace (still zero), so the traceless condition survives the rotation. -/
lemma su5_charge_trace_rotationInvariant : ∑ i, su5AntifundCharge (icosaRot5 i) = 0 := by
  rw [Equiv.sum_comp icosaRot5 su5AntifundCharge]
  exact su5AntifundCharge_isAffineWeight

end Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
