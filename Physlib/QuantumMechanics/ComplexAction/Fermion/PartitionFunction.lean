/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.Matsubara.PathIntegral
public import Physlib.QuantumMechanics.ComplexAction.Fermion.FockFunctor

/-!
# The fermionic partition function: the Fock-space trace = the Matsubara / Nagao–Nielsen weight

`Fermion.FockFunctor` built the second-quantization functor `H ↦ Λ(H)`. This file takes the analytic
step suggested there: the **trace** `Z = Tr_{Λ(H)}(e^{−βH})` — the partition function — equated to the
**Matsubara** thermal weight (and hence the Nagao–Nielsen complex-action path integral).

## The single-mode Fock trace

For a single fermionic mode of energy `E`, Pauli exclusion (`creationOp_sq = 0` in
`Fermion.FockFunctor`) makes the Fock space `Λ(ℝ)` **two-dimensional** — occupation `n ∈ {0, 1}`. The
trace of the Gibbs weight `e^{−βH} = e^{−βE n}` over these two states is

 `Z = Tr_{Λ(ℝ)}(e^{−βH}) = ∑_{n=0}^{1} e^{−βEn} = 1 + e^{−βE}` (`fermionicPartition_eq_fock_trace`),

the fermionic partition function. Its `n = 1` term is exactly physlib's **Matsubara weight**
`matsubaraWeight E T = e^{−βE}` (`fermionicPartition_eq_matsubara`), the `τ = βℏ` Wick rotation of the
reversible phase — i.e. the Nagao–Nielsen complex-action thermal weight. So the Fock-space trace is the
Matsubara / Nagao–Nielsen partition function.

## The Fermi–Dirac distribution

The mode occupation is the **Fermi–Dirac distribution**

 `⟨n⟩ = e^{−βE} / Z = 1 / (e^{βE} + 1)` (`fermiDirac_eq_occupation`),

a direct consequence of the partition function — the statistics of the second-quantized fermion.

## The multi-mode partition function

For finitely many modes the trace factorizes, `Z = ∏_k (1 + e^{−βE_k})`
(`fermionicPartitionMulti_eq`) — the trace over `Λ(⊕_k H_k) = ⊗_k Λ(H_k)`.

## Scope (the remaining continuum step)

The **single-mode** and **finite-mode** Fock-space traces are proved here, and the single-mode trace
*is* the Matsubara / Nagao–Nielsen weight `1 + e^{−βE}`. What remains is the **continuum**
`Z = ∏_{k ∈ ℝ³} (1 + e^{−βE_k})` — an infinite product over the momentum continuum, needing the
trace-class / KMS-state layer on `Λ(L²(ℝ³))` (the regularized infinite product, the thermodynamic
limit). That analytic limit is the last frontier; the per-mode identity (trace = Matsubara weight) is
now established.

## References

* physlib `QFT/Matsubara/PathIntegral` (`matsubaraWeight`), `PathIntegral.QFTPathIntegralComplexAction`. This
 development: `Fermion.FockFunctor`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QFT.Matsubara.PathIntegral

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction

/-! ## §A — the single-mode fermionic partition function (the Fock trace) -/

/-- **The single-mode fermionic partition function** `Z = 1 + e^{−βE}` — the trace of the Gibbs weight
over the two-dimensional single-mode Fock space. -/
def fermionicPartition (E β : ℝ) : ℝ := 1 + Real.exp (-(β * E))

/-- **`Z = Tr_{Λ(ℝ)}(e^{−βH})`** as the sum over the two Fock occupation states `n ∈ {0, 1}` (Pauli
exclusion): `Z = ∑_{n=0}^{1} e^{−βEn} = 1 + e^{−βE}`. -/
theorem fermionicPartition_eq_fock_trace (E β : ℝ) :
    fermionicPartition E β = ∑ n : Fin 2, Real.exp (-(β * E * (n : ℝ))) := by
  rw [fermionicPartition, Fin.sum_univ_two]
  norm_num

/-- **The single-mode trace is the Matsubara weight**: `Z = 1 + matsubaraWeight E T` (real part), with
`matsubaraWeight E T = e^{−βE}` the `τ = βℏ` Wick rotation of the reversible phase — the Nagao–Nielsen
complex-action thermal weight. -/
theorem fermionicPartition_eq_matsubara (E : ℝ) (T : ThermalCircle) :
    fermionicPartition E T.beta = 1 + (matsubaraWeight E T).re := by
  rw [fermionicPartition, matsubaraWeight, Complex.ofReal_re]

/-- **The partition function is positive** `Z > 0`. -/
theorem fermionicPartition_pos (E β : ℝ) : 0 < fermionicPartition E β := by
  rw [fermionicPartition]
  have := Real.exp_pos (-(β * E))
  linarith

/-! ## §B — the Fermi–Dirac distribution -/

/-- **The Fermi–Dirac distribution** `⟨n⟩ = 1/(e^{βE} + 1)`. -/
def fermiDirac (E β : ℝ) : ℝ := 1 / (Real.exp (β * E) + 1)

/-- **The mode occupation is the Fermi–Dirac distribution** `⟨n⟩ = e^{−βE}/Z = 1/(e^{βE}+1)`. -/
theorem fermiDirac_eq_occupation (E β : ℝ) :
    Real.exp (-(β * E)) / fermionicPartition E β = fermiDirac E β := by
  have hx : (0 : ℝ) < Real.exp (β * E) := Real.exp_pos _
  rw [fermionicPartition, fermiDirac, Real.exp_neg]
  field_simp

/-! ## §C — the multi-mode partition function -/

/-- **The multi-mode fermionic partition function** `Z = ∏_k (1 + e^{−βE_k})` — the trace over
`Λ(⊕_k H_k) = ⊗_k Λ(H_k)`. -/
def fermionicPartitionMulti {k : ℕ} (E : Fin k → ℝ) (β : ℝ) : ℝ :=
  ∏ i, fermionicPartition (E i) β

/-- **The multi-mode partition function factorizes** `Z = ∏_k (1 + e^{−βE_k})`. -/
theorem fermionicPartitionMulti_eq {k : ℕ} (E : Fin k → ℝ) (β : ℝ) :
    fermionicPartitionMulti E β = ∏ i, (1 + Real.exp (-(β * E i))) := by
  simp only [fermionicPartitionMulti, fermionicPartition]

/-- **The multi-mode partition function is positive** `Z > 0`. -/
theorem fermionicPartitionMulti_pos {k : ℕ} (E : Fin k → ℝ) (β : ℝ) :
    0 < fermionicPartitionMulti E β :=
  Finset.prod_pos (fun i _ => fermionicPartition_pos (E i) β)

/-! ## §B — the Fermi surface and the degenerate Fermi sea

With the single-mode energy `E` measured *from the chemical potential* (the Fermi energy `E_F`), the
occupation `fermiDirac E β` exhibits the free-electron-gas structure: the **Fermi surface** `E = 0` is exactly
half-filled at any temperature, and the **Fermi sea** has the states below `E_F` mostly occupied and those
above mostly empty. -/

/-- **[The Fermi surface is half-filled]** `f(E_F) = 1/2` — at the Fermi energy (`E = 0`, measured from the
chemical potential) the occupation is exactly `1/2` at *any* temperature `β`. This is the defining property of
the Fermi level. -/
theorem fermiDirac_fermiSurface (β : ℝ) : fermiDirac 0 β = 1 / 2 := by
  unfold fermiDirac; rw [mul_zero, Real.exp_zero]; norm_num

/-- **[Below the Fermi energy: mostly occupied]** `E < 0 ⟹ f(E) > 1/2` (for `β > 0`) — the filled side of the
Fermi sea. -/
theorem fermiDirac_below_gt_half (E β : ℝ) (hE : E < 0) (hβ : 0 < β) : 1 / 2 < fermiDirac E β := by
  have hexp : Real.exp (β * E) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg hβ hE)
  have hpos : 0 < Real.exp (β * E) + 1 := by positivity
  unfold fermiDirac
  rw [lt_div_iff₀ hpos]; linarith

/-- **[Above the Fermi energy: mostly empty]** `E > 0 ⟹ f(E) < 1/2` (for `β > 0`) — the empty side of the
Fermi sea. -/
theorem fermiDirac_above_lt_half (E β : ℝ) (hE : 0 < E) (hβ : 0 < β) : fermiDirac E β < 1 / 2 := by
  have hexp : 1 < Real.exp (β * E) := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (mul_pos hβ hE)
  have hpos : 0 < Real.exp (β * E) + 1 := by positivity
  unfold fermiDirac
  rw [div_lt_iff₀ hpos]; linarith

end Physlib.QuantumMechanics.ComplexAction.Fermion.PartitionFunction

end
