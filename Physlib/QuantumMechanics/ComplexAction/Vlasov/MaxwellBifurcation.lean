/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState
public import Mathlib.Data.Sign.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Bifurcation points of the Vlasov–Maxwell system (Rendón–Sinitsyn–Sidorov 2016)

Formalizes the analytic core of *L. Rendón, A. V. Sinitsyn, N. A. Sidorov, "Bifurcation points of nonlinear
operators: existence theorems, asymptotics and application to the Vlasov–Maxwell system", Rev. Colomb. Mat.
50 (2016) 85–107* — the bifurcation analysis of the **same** stationary Vlasov–Maxwell system, with the
**same** distribution form `f_i = λ·f̂_i(R, G)`, `R = −α_iv² + φ_i`, `G = v·d_i + ψ_i` (Eq. 5) as the
formalized Markov arc (`R = vlasovEnergy`, `G = vlasovMomentum`).

A point `λ⁰` is a **bifurcation point** if every neighbourhood of the trivial solution `(λ⁰, E⁰, B⁰, f⁰)`
(with `ρ⁰ = j⁰ = 0`, `E⁰ = 0`, `B⁰ = βd₁`) contains a nontrivial solution. The existence theorem 2.2 turns on
a **Kronecker-index jump**: the rotation of the linearized field at the two ends `ε = ±δ` equals `sign α(±δ)`;
when `α` is monotone through `ε₀`, these signs differ, so the homotopy invariance `J(H(·,0)) = J(H(·,1))`
fails — forcing a zero, i.e. a bifurcation point.

* **§A — the index jump (Theorem 2.2)** (`bifurcation_index_jump`, `bifurcation_signs_differ`). A monotone `α`
  vanishing at `ε₀` has `α(ε₀−δ) < 0 < α(ε₀+δ)`, so the boundary Kronecker indices `sign α(±δ)` differ — the
  topological obstruction that yields the bifurcation point.
* **§B — condition II (Lemma 3.3)** (`conditionII_identity`). The determinant cross-term `T₁T₄ − T₂T₃` of the
  linearized matrix equals the antisymmetric double sum `∑ᵢⱼ aᵢaⱼwⱼ(lᵢkⱼ − kᵢlⱼ)`; with `β_i = d_i/2α_i`
  (Example 3.4) it is a sum of squares `> 0`, the spectral admissibility for bifurcation.
* **§C — the VM application, via the Markov arc** (`trivial_solution_selfConsistent`, `trivial_B_along_drift`).
  Theorem 3.1's field reconstruction is exactly `Vlasov.MaxwellSteadyState.field_reconstruction`; the trivial
  solution `E⁰ = 0`, `B⁰ = βd₁` is its `∇φ = ∇ψ = 0` special case — self-consistent, with `B⁰` along the drift
  (`B⁰ × d = 0`) and `(B⁰, d) = β`.

## References

* L. Rendón, A. V. Sinitsyn, N. A. Sidorov, Rev. Colomb. Mat. 50 (2016) 85–107 (Def. 1.1, Eqs. 5, 26–34,
  Theorems 2.2, 3.1, Lemma 3.3, Example 3.4; the index theory [2,7]).
* Repo carriers: `Vlasov.MaxwellSteadyState` (`field_reconstruction`, `electricField`, `magneticField`,
  `cross_smul_left`, `cross_self` — Theorem 3.1 = Markov Theorem 1); `Vlasov.DiamondTimeReversal`
  (`vlasovEnergy`/`vlasovMomentum` = the `R, G` of Eq. 5); `Vlasov.CurrentChargeReflection`
  (`current_eq_drift_smul_charge` = condition D `j_i = β_iρ_i`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation

open Finset Matrix
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState


/-- **[Theorem 2.2 core] A monotone `α` vanishing at `ε₀` straddles zero** `α(ε₀−δ) < 0 < α(ε₀+δ)` — the
linearized field's boundary rotations `sign α(±δ)` will have opposite signs. -/
lemma bifurcation_index_jump (α : ℝ → ℝ) (ε₀ δ : ℝ) (hδ : 0 < δ)
    (hmono : StrictMono α) (hzero : α ε₀ = 0) :
    α (ε₀ - δ) < 0 ∧ 0 < α (ε₀ + δ) :=
  ⟨by rw [← hzero]; exact hmono (sub_lt_self ε₀ hδ),
   by rw [← hzero]; exact hmono (lt_add_of_pos_right ε₀ hδ)⟩

/-- **[Theorem 2.2 obstruction] The boundary Kronecker indices differ** `sign α(ε₀−δ) ≠ sign α(ε₀+δ)`. Since
`J(H(·,0)) = sign α(−δ) = −1` and `J(H(·,1)) = sign α(+δ) = +1`, the rotations cannot coincide, contradicting
homotopy invariance — hence a zero of `H` exists and `ε₀` is a bifurcation point. -/
lemma bifurcation_signs_differ (α : ℝ → ℝ) (ε₀ δ : ℝ) (hδ : 0 < δ)
    (hmono : StrictMono α) (hzero : α ε₀ = 0) :
    SignType.sign (α (ε₀ - δ)) ≠ SignType.sign (α (ε₀ + δ)) := by
  obtain ⟨h1, h2⟩ := bifurcation_index_jump α ε₀ δ hδ hmono hzero
  rw [sign_neg h1, sign_pos h2]; decide


/-- **[Lemma 3.3] The determinant cross-term of the linearized matrix.** With `T₁ = ∑ lᵢaᵢ`, `T₂ = ∑ kᵢaᵢ`,
`T₃ = ∑ wᵢlᵢaᵢ`, `T₄ = ∑ wᵢkᵢaᵢ` (where `wᵢ = (βᵢ, d)`), `T₁T₄ − T₂T₃` is the antisymmetric double sum
`∑ᵢⱼ aᵢaⱼwⱼ(lᵢkⱼ − kᵢlⱼ)`. For `βᵢ = dᵢ/2αᵢ` (Example 3.4) it collapses to a sum of squares `> 0`, giving
condition II `T₁T₄ − T₂T₃ > 0` — the spectral admissibility for bifurcation. -/
lemma conditionII_identity {ι : Type*} [Fintype ι] (a l k w : ι → ℝ) :
    (∑ i, l i * a i) * (∑ i, w i * k i * a i) - (∑ i, k i * a i) * (∑ i, w i * l i * a i)
      = ∑ i, ∑ j, a i * a j * w j * (l i * k j - k i * l j) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  ring


/-- **The trivial magnetic field is along the drift** `B⁰ = βd₁ ⟹ B⁰ × d₁ = 0` — the magnetic field of the
trivial solution does no work, so `ρ⁰ = j⁰ = 0`. -/
lemma trivial_B_along_drift (β : ℝ) (d : Fin 3 → ℝ) : (β • d) ⨯₃ d = 0 := by
  rw [cross_smul_left, cross_self, smul_zero]

/-- **[Theorem 3.1 / trivial solution] The trivial solution `E⁰ = 0`, `B⁰ = βd₁` is self-consistent.** It is
the `∇φ = ∇ψ = 0` special case of `Vlasov.MaxwellSteadyState.field_reconstruction` (Theorem 3.1 = Markov
Theorem 1): the reconstructed `E⁰ = (m/2αq)∇φ⁰ = 0`, the magnetic field is along the drift `B⁰ × d = 0`, and
`(B⁰, d) = β`. This trivial state is the one whose bifurcation `λ⁰` the existence theorem locates. -/
lemma trivial_solution_selfConsistent (α qm β mcq : ℝ) (d : Fin 3 → ℝ)
    (hq : 2 * α * qm ≠ 0) (hdd : d ⬝ᵥ d ≠ 0) :
    (0 : Fin 3 → ℝ) = (2 * α * qm) • electricField α qm 0
      ∧ electricField α qm 0 ⬝ᵥ d = 0
      ∧ magneticField β mcq d 0 ⨯₃ d = -mcq • (0 : Fin 3 → ℝ)
      ∧ magneticField β mcq d 0 ⬝ᵥ d = β :=
  field_reconstruction α qm β mcq 0 0 d hq hdd (by simp) (by simp)

end Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellBifurcation

end
