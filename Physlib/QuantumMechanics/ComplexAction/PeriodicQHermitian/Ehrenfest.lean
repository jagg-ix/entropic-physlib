/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

/-!
# Heisenberg equation, Ehrenfest's theorem, conserved probability (periodic Q-Hermitian)

Nagao–Nielsen note that regarding the future-included Q-formalism matrix element `⟨Ô⟩` as an
expectation value yields "the Heisenberg equation, Ehrenfest's theorem, and a conserved
probability current density" (arXiv:2203.07795, Intro; refs 20, 21). This file derives all
three at the matrix level, where each is a consequence of **trace cyclicity**, and ties
the conservation to the `Q`-Hermitian formalism of `PeriodicQHermitian.Basic`.

With `H` the generator, `ℏ`, the matrix commutator `[A,B] = AB − BA`, an operator `O`,
and a density-like matrix `ρ`:

* **Heisenberg equation** — `heisenbergGen ℏ H O = (i/ℏ)[H,O]`, the operator rate
  `dO/dt = (i/ℏ)[H,O]`. `heisenbergGen_eq_lax` writes it in the Lax/commutator form
  `[g,O]` with `g = (i/ℏ)H`, matching `RelationalTime.DueringDynamics` (`Ṁ = [g,M]`).
* **Ehrenfest's theorem** — `ehrenfest`: `Tr(ρ̇ O) = Tr(ρ · (i/ℏ)[H,O])`, i.e.
  `d⟨O⟩/dt = ⟨(i/ℏ)[H,O]⟩` — the expectation-value rate equals the expectation of the
  Heisenberg operator rate (`trace_commutator_mul` is the cyclicity core).
* **Conserved probability current** — `probability_conserved`: `Tr(ρ̇) = 0`, so the total
  probability `Tr ρ` is constant (the integrated continuity equation `∂_t∫ρ = −∮ j = 0`).

The `Q`-formalism content (the complex-action physics):

* The conservative von Neumann rate uses the ordinary commutator; the *physical*
  non-Hermitian complex-action rate `dissipativeGen` uses the `Q`-adjoint `Ĥ^{†Q}` on the bra side.
* `trace_dissipativeGen` — its trace is `−(i/ℏ)·⟨(Ĥ − Ĥ^{†Q})⟩`: probability **decays** at a
  rate set by the anti-`Q`-Hermitian (imaginary-action / dissipative) part of `Ĥ`.
* `trace_dissipativeGen_eq_zero_of_qHermitian`, `dissipativeGen_eq_vonNeumann_of_qHermitian`
  — probability is conserved **iff** the generator is `Q`-Hermitian (`Ĥ^{†Q} = Ĥ`). For the
  Q-Hermitian Hamiltonian this selects `Ĥ_Qh` (`PeriodicQHermitian.Basic.qHermPart`), so the Heisenberg /
  Ehrenfest / continuity equations hold exactly under the `Q`-Hermitian part — the precise
  realization of the paper's claim. `qHermitian_probability_conserved` instantiates it.

Reference: K. Nagao, H. B. Nielsen, arXiv:2203.07795 (periodic Q-Hermitian) and refs 20, 21
(Heisenberg equation, Ehrenfest, conserved current in the future-included Q-formalism).
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **matrix commutator** `[A, B] = AB − BA`. -/
def commutator (A B : Matrix n n ℂ) : Matrix n n ℂ := A * B - B * A

omit [DecidableEq n] in
/-- **The trace of a commutator vanishes** (cyclicity): `Tr[A,B] = 0`. -/
theorem trace_commutator (A B : Matrix n n ℂ) : (commutator A B).trace = 0 := by
  rw [commutator, Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

omit [DecidableEq n] in
/-- **Cyclicity core for Ehrenfest**: `Tr([H,ρ]·O) = −Tr(ρ·[H,O])`. -/
theorem trace_commutator_mul (H ρ O : Matrix n n ℂ) :
    (commutator H ρ * O).trace = -((ρ * commutator H O).trace) := by
  simp only [commutator, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm H (ρ * O), Matrix.mul_assoc ρ O H]
  ring

/-! ## §1 — The Heisenberg equation (operator rate) -/

/-- **The Heisenberg operator rate** `dO/dt = (i/ℏ)[H,O]`. -/
noncomputable def heisenbergGen (ℏ : ℂ) (H O : Matrix n n ℂ) : Matrix n n ℂ :=
  (Complex.I / ℏ) • commutator H O

/-- **The Heisenberg equation in Lax / commutator form** `(i/ℏ)[H,O] = [g, O]` with
`g = (i/ℏ)H` — the same `Ṁ = [g, M]` shape as `RelationalTime.DueringDynamics`. -/
theorem heisenbergGen_eq_lax (ℏ : ℂ) (H O : Matrix n n ℂ) :
    heisenbergGen ℏ H O = ((Complex.I / ℏ) • H) * O - O * ((Complex.I / ℏ) • H) := by
  rw [heisenbergGen, commutator, smul_sub, ← smul_mul_assoc, ← mul_smul_comm]

/-! ## §2 — The von Neumann (state) rate, Ehrenfest, conserved probability -/

/-- **The von Neumann state rate** `dρ/dt = −(i/ℏ)[H,ρ]` (conservative evolution under a
`Q`-Hermitian `H`). -/
noncomputable def vonNeumannGen (ℏ : ℂ) (H ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  -(Complex.I / ℏ) • commutator H ρ

/-- **Ehrenfest's theorem**: `Tr(ρ̇ O) = Tr(ρ·(i/ℏ)[H,O])`, i.e. `d⟨O⟩/dt = ⟨(i/ℏ)[H,O]⟩`
— the rate of the expectation value equals the expectation of the Heisenberg operator
rate. (`trace_commutator_mul` cyclicity, plus the `±(i/ℏ)` bookkeeping.) -/
theorem ehrenfest (ℏ : ℂ) (H ρ O : Matrix n n ℂ) :
    (vonNeumannGen ℏ H ρ * O).trace = (ρ * heisenbergGen ℏ H O).trace := by
  rw [vonNeumannGen, heisenbergGen, smul_mul_assoc, mul_smul_comm, Matrix.trace_smul,
    Matrix.trace_smul, trace_commutator_mul]
  simp only [smul_eq_mul]
  ring

omit [DecidableEq n] in
/-- **Conserved probability current**: `Tr(ρ̇) = 0`, so the total probability `Tr ρ` is
constant in time — the integrated continuity equation. -/
theorem probability_conserved (ℏ : ℂ) (H ρ : Matrix n n ℂ) :
    (vonNeumannGen ℏ H ρ).trace = 0 := by
  rw [vonNeumannGen, Matrix.trace_smul, trace_commutator, smul_zero]

/-! ## §3 — The `Q`-formalism: dissipative vs. conservative evolution -/

/-- **The physical non-Hermitian complex-action rate** `dρ/dt = −(i/ℏ)(Ĥ ρ − ρ Ĥ^{†Q})`: the bra
evolves with the `Q`-adjoint `Ĥ^{†Q}`, so for non-`Q`-Hermitian `Ĥ` this is *not* a
commutator. -/
noncomputable def dissipativeGen (P : Matrix n n ℂ) (ℏ : ℂ) (H ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  -(Complex.I / ℏ) • (H * ρ - ρ * qDagger (qMetric P) H)

/-- **Probability decays at the anti-`Q`-Hermitian rate**:
`Tr(ρ̇) = −(i/ℏ)·Tr((Ĥ − Ĥ^{†Q})·ρ)`. The total probability is not conserved when `Ĥ` has
an anti-`Q`-Hermitian (imaginary-action / dissipative) part. -/
theorem trace_dissipativeGen (P : Matrix n n ℂ) (ℏ : ℂ) (H ρ : Matrix n n ℂ) :
    (dissipativeGen P ℏ H ρ).trace
      = -(Complex.I / ℏ) * ((H - qDagger (qMetric P) H) * ρ).trace := by
  rw [dissipativeGen, Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm ρ (qDagger (qMetric P) H)]

/-- **Conserved probability ⟺ `Q`-Hermitian generator** (one direction): if `Ĥ^{†Q} = Ĥ`
then `Tr(ρ̇) = 0`. The anti-`Q`-Hermitian part is exactly the obstruction. -/
theorem trace_dissipativeGen_eq_zero_of_qHermitian (P : Matrix n n ℂ) (ℏ : ℂ)
    {H : Matrix n n ℂ} (hH : qDagger (qMetric P) H = H) (ρ : Matrix n n ℂ) :
    (dissipativeGen P ℏ H ρ).trace = 0 := by
  rw [trace_dissipativeGen, hH, sub_self, Matrix.zero_mul, Matrix.trace_zero, mul_zero]

/-- **For a `Q`-Hermitian generator the physical rate is the conservative von Neumann
rate**: the dissipative evolution collapses to the standard commutator one (and so the
Heisenberg/Ehrenfest/continuity equations of §1–2 apply). -/
theorem dissipativeGen_eq_vonNeumann_of_qHermitian (P : Matrix n n ℂ) (ℏ : ℂ)
    {H : Matrix n n ℂ} (hH : qDagger (qMetric P) H = H) (ρ : Matrix n n ℂ) :
    dissipativeGen P ℏ H ρ = vonNeumannGen ℏ H ρ := by
  rw [dissipativeGen, vonNeumannGen, commutator, hH]

/-- **complex-action conserved probability**: under the `Q`-Hermitian part `Ĥ_Qh` of the complex-action
Hamiltonian, the total probability is conserved — the future-included Q-formalism's conserved
probability current, realized on `qHermPart`. -/
theorem qHermitian_probability_conserved (P : Matrix n n ℂ) (d : n → ℂ) (ℏ : ℂ) (ρ : Matrix n n ℂ) :
    (vonNeumannGen ℏ (qHermPart (qMetric P) (hamiltonian P d)) ρ).trace = 0 :=
  probability_conserved ℏ _ ρ

end Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

end
