/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState

/-!
# Lagrangian invariants and drift transport (Markov et al. 1992, Eqs. 3.22, 4.18)

Formalizes the **conservation-law backbone** of *Markov, Rudykh, Sidorov, Sinitsyn, Tolstonogov, Acta Appl.
Math. 28 (1992)*: the **Lagrangian-invariant transport** equation (Eq. 4.18, and the reduced charge continuity
Eq. 3.22)

  `∂Ψ/∂t + (1/2α)(∇Ψ, d) = 0`,

which says `Ψ` is constant along the drift flow `d/2α`. This is the *general* first-integral condition that the
energy/momentum integrals `R, G` (`Vlasov.MaxwellSteadyState`) are special cases of. Two structural facts make
the framework: it is **linear** (sums of invariants are invariant) and **closed under composition** (any
function of an invariant is invariant — generalizing `vlasov_steady_solution`, `f(R, G)` steady). In the
**stationary** case `∂Ψ/∂t = 0` it reduces to `∇Ψ ⟂ d` — *exactly* the §2 orthogonality conditions
(`gradφ_dot_d`, `gradψ_dot_d`), so the self-consistent potentials `φ, ψ` are precisely the stationary
Lagrangian invariants.

* **§A — the drift-transport operator** (`driftTransport`, `LagrangianInvariant`). Eq. 4.18 / 3.22 LHS and the
  invariance predicate `∂Ψ/∂t + (1/2α)(∇Ψ,d) = 0`.
* **§B — the algebra of invariants** (`driftTransport_add`, `lagrangianInvariant_add`, `driftTransport_smul`,
  `lagrangianInvariant_comp`). Linearity and the chain rule `Φ(Ψ)` invariant — the kinetic-theory reason
  functions of first integrals are steady states.
* **§C — the stationary case = §2 orthogonality** (`lagrangianInvariant_stationary_iff`,
  `gradφ_stationary_invariant`, `gradψ_stationary_invariant`). A time-independent `Ψ` is a Lagrangian
  invariant iff `∇Ψ ⟂ d`; the self-consistent `φ, ψ` qualify via the §2 field conditions.

## References

* Y. Markov et al., Acta Appl. Math. 28 (1992), Eqs. 3.20–3.22 (charge continuity, the reduced drift form),
  4.16–4.18 (the conserved Lyapunov functionals `F₃, F₄`; `Ψᵢ` Lagrangian invariants).
* Repo dependencies: `Vlasov.MaxwellSteadyState` (`gradφ_dot_d`, `gradψ_dot_d`, `vlasov_steady_solution`);
  `Vlasov.CurrentChargeReflection` (the current `j = d·ρ` whose continuity Eq. 3.21 reduces to Eq. 3.22).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Vlasov.LagrangianInvariants

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellSteadyState

/-! ## §A — the drift-transport operator (Eqs. 4.18, 3.22) -/

/-- **[Eq. 4.18 / 3.22 LHS] The drift transport** `∂Ψ/∂t + (1/2α)(∇Ψ, d)` — the convective derivative of `Ψ`
along the drift flow `d/2α`. -/
noncomputable def driftTransport (α : ℝ) (gradΨ d : Fin 3 → ℝ) (Ψt : ℝ) : ℝ :=
  Ψt + (1 / (2 * α)) * (gradΨ ⬝ᵥ d)

/-- **A Lagrangian invariant** (first integral of the drift flow): `∂Ψ/∂t + (1/2α)(∇Ψ, d) = 0`. -/
def LagrangianInvariant (α : ℝ) (gradΨ d : Fin 3 → ℝ) (Ψt : ℝ) : Prop :=
  driftTransport α gradΨ d Ψt = 0

/-! ## §B — the algebra of Lagrangian invariants -/

/-- **Linearity** of the drift transport in `(∇Ψ, ∂Ψ/∂t)`. -/
theorem driftTransport_add (α : ℝ) (gradΨ gradΧ d : Fin 3 → ℝ) (Ψt Χt : ℝ) :
    driftTransport α (gradΨ + gradΧ) d (Ψt + Χt)
      = driftTransport α gradΨ d Ψt + driftTransport α gradΧ d Χt := by
  unfold driftTransport; rw [add_dotProduct]; ring

/-- **Homogeneity** `Φ'·Ψ`-scaling of the drift transport. -/
theorem driftTransport_smul (α c : ℝ) (gradΨ d : Fin 3 → ℝ) (Ψt : ℝ) :
    driftTransport α (c • gradΨ) d (c * Ψt) = c * driftTransport α gradΨ d Ψt := by
  unfold driftTransport; rw [smul_dotProduct, smul_eq_mul]; ring

/-- **The sum of two Lagrangian invariants is a Lagrangian invariant.** -/
theorem lagrangianInvariant_add (α : ℝ) (gradΨ gradΧ d : Fin 3 → ℝ) (Ψt Χt : ℝ)
    (hΨ : LagrangianInvariant α gradΨ d Ψt) (hΧ : LagrangianInvariant α gradΧ d Χt) :
    LagrangianInvariant α (gradΨ + gradΧ) d (Ψt + Χt) := by
  unfold LagrangianInvariant at *
  rw [driftTransport_add, hΨ, hΧ, add_zero]

/-- **[Chain rule] Any function of a Lagrangian invariant is a Lagrangian invariant** — with `c = Φ'(Ψ)`, if
`Ψ` is invariant so is `Φ(Ψ)`. This is the abstract form of `vlasov_steady_solution`: functions of first
integrals are steady states. -/
theorem lagrangianInvariant_comp (α c : ℝ) (gradΨ d : Fin 3 → ℝ) (Ψt : ℝ)
    (hΨ : LagrangianInvariant α gradΨ d Ψt) :
    LagrangianInvariant α (c • gradΨ) d (c * Ψt) := by
  unfold LagrangianInvariant at *
  rw [driftTransport_smul, hΨ, mul_zero]

/-! ## §C — the stationary case is the §2 orthogonality -/

/-- **[Stationary ⟺ orthogonality] A time-independent `Ψ` is a Lagrangian invariant iff `∇Ψ ⟂ d`.** With
`∂Ψ/∂t = 0` the transport vanishes exactly when `(∇Ψ, d) = 0` (`α ≠ 0`) — the §2 conditions Eqs. 2.10/2.11. -/
theorem lagrangianInvariant_stationary_iff (α : ℝ) (gradΨ d : Fin 3 → ℝ) (hα : α ≠ 0) :
    LagrangianInvariant α gradΨ d 0 ↔ gradΨ ⬝ᵥ d = 0 := by
  have hne : (1 / (2 * α)) ≠ 0 := by simp [hα]
  unfold LagrangianInvariant driftTransport
  rw [zero_add, mul_eq_zero]
  exact or_iff_right hne

/-- **The potential `φ` is a stationary Lagrangian invariant** — from the energy field condition `∇φ = 2αqm·E`
and `E·d = 0` (Eq. 2.9), `∇φ ⟂ d` (`gradφ_dot_d`), so `φ` is constant along the drift flow. -/
theorem gradφ_stationary_invariant (α qm : ℝ) (gradφ E d : Fin 3 → ℝ) (hα : α ≠ 0)
    (hfield : gradφ = (2 * α * qm) • E) (hEd : E ⬝ᵥ d = 0) :
    LagrangianInvariant α gradφ d 0 :=
  (lagrangianInvariant_stationary_iff α gradφ d hα).mpr (gradφ_dot_d α qm gradφ E d hfield hEd)

/-- **The potential `ψ` is a stationary Lagrangian invariant** — from the momentum field condition Eq. 2.8,
`∇ψ ⟂ d` (`gradψ_dot_d`), so `ψ` too is constant along the drift flow. -/
theorem gradψ_stationary_invariant (α qm cinv : ℝ) (gradψ B d : Fin 3 → ℝ) (hα : α ≠ 0)
    (hfield : (qm * cinv) • (B ⨯₃ d) + gradψ = 0) :
    LagrangianInvariant α gradψ d 0 :=
  (lagrangianInvariant_stationary_iff α gradψ d hα).mpr (gradψ_dot_d qm cinv gradψ B d hfield)

end Physlib.QuantumMechanics.ComplexAction.Vlasov.LagrangianInvariants

end
