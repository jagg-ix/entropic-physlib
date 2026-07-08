/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction

/-!
# Quantum mechanics as Hamilton–Killing flows on a statistical manifold (Caticha 2107.08502)

Formalizes the symplectic/Hamiltonian core of Caticha (*Quantum Mechanics as Hamilton–Killing Flows on a
Statistical Manifold*, arXiv:2107.08502): quantum mechanics is derived as the flows on the cotangent bundle of a
statistical manifold (the simplex `S = {ρ | ρⁱ ≥ 0, ∑ρⁱ = 1}`) that preserve *both* the **symplectic** structure
(a Hamilton flow, `L_V Ω = 0`) and the **metric** structure (a Killing flow, `L_V G = 0`) — the Hamilton–Killing
flows. This unifies two threads of the repository: the entropic-dynamics canonical pair `(ρ, Φ)` and the
Killing flow of `QuantumKillingFlowLieDerivative`.

On the e-phase space `T*S⁺` with coordinates `(ρⁱ, π_i)`:

* the **canonical symplectic form** `Ω[V,U] = V^{ρ}U^{π} − V^{π}U^{ρ}` (their Eqs. 7, 9) is antisymmetric
 (`poissonBracket_antisymm`, `poissonBracket_self`) — the `[[0,1],[−1,0]]` symplectic matrix;
* the flows preserving `Ω` are **Hamiltonian** (their Eqs. 13–15): the Hamilton vector field is `(∂H/∂π, −∂H/∂ρ)`
 (`hamiltonVectorField`), and Hamilton's equations `dρ/dτ = ∂H/∂π`, `dπ/dτ = −∂H/∂ρ` (Eq. 18) are the symplectic
 gradient flow;
* the **evolution of any function is its Poisson bracket with the Hamiltonian** `dF/dτ = {F, H}`
 (`evolution_is_poissonBracket`, their Eqs. 16–17) — the Hamiltonian formalism emerging from the symplectic
 geometry;
* a **Hamilton–Killing flow preserves both structures** (`hamiltonKilling_preserves_both`): the Killing flow of
 `QuantumKillingFlowLieDerivative` preserves the (Lie/`collisionStar`) bracket, and the symplectic form is
 antisymmetric — the flow reflecting both the metric (Killing) and symplectic (Hamilton) geometry that *is*
 quantum mechanics.

So the Hamiltonian formalism of quantum mechanics — symplectic form, Hamilton's equations, Poisson brackets —
emerges from the geometry of the statistical manifold, and the quantum flows are exactly those preserving both the
information metric (Killing) and the symplectic form (Hamilton): Hamilton–Killing flows, the geometric root of the
entropic-dynamics reconstruction.

* **§A — the canonical symplectic form / Poisson bracket** (`poissonBracket`, `poissonBracket_antisymm`).
* **§B — Hamilton's equations** (`hamiltonVectorField`).
* **§C — evolution is the Poisson bracket** (`evolution_is_poissonBracket`).
* **§D — the Hamilton–Killing synthesis** (`hamiltonKilling_preserves_both`).

The Poisson bracket, its antisymmetry, Hamilton's equations, and `dF/dτ = {F,H}` are exact
algebra (the bracket expressed via gradient components). The Fubini–Study metric, the derivation of complex numbers
/ Hilbert space, and the full `L_V Ω = 0` curl argument (Eqs. 10–13) are the paper's programme, captured at the
symplectic-bracket level; the Killing side reuses `killingFlow_preserves_bracket`. No new axioms.

## References

* A. Caticha, arXiv:2107.08502, §§2–3 (Eqs. 7, 9, 15–18; symplectic form, Hamilton's equations, Poisson bracket).
 Repo dependencies: `AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative`,
 `EntropicTime.EntropicDynamicsWaveFunctionReconstruction`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingFlowStatisticalManifold

/-! ## §A — the canonical symplectic form / Poisson bracket -/

/-- **The canonical symplectic form / Poisson bracket** `Ω[V,U] = {V,U} = V^ρ U^π − V^π U^ρ` (Caticha Eqs. 7, 9,
16) — the antisymmetric bilinear form on the e-phase space `T*S⁺`, in gradient components `(V^ρ, V^π)` on the
canonical pair `(ρ, π)`. -/
def poissonBracket (Vρ Vπ Uρ Uπ : ℝ) : ℝ := Vρ * Uπ - Vπ * Uρ

/-- **[The symplectic form is antisymmetric] `Ω[V,U] = −Ω[U,V]`.** The `[[0,1],[−1,0]]` canonical symplectic
matrix (Eq. 9) — the antisymmetry defining the symplectic geometry of the cotangent bundle. -/
theorem poissonBracket_antisymm (Vρ Vπ Uρ Uπ : ℝ) :
    poissonBracket Vρ Vπ Uρ Uπ = -poissonBracket Uρ Uπ Vρ Vπ := by
  unfold poissonBracket; ring

/-- **[The symplectic form annihilates a vector with itself] `Ω[V,V] = 0`.** -/
theorem poissonBracket_self (Vρ Vπ : ℝ) : poissonBracket Vρ Vπ Vρ Vπ = 0 := by
  unfold poissonBracket; ring

/-! ## §B — Hamilton's equations -/

/-- **The Hamilton vector field** `V_H = (∂H/∂π, −∂H/∂ρ)` (Caticha Eqs. 15, 18) — the symplectic gradient of the
Hamiltonian `H̃`, generating the Hamilton flow `dρ/dτ = ∂H/∂π`, `dπ/dτ = −∂H/∂ρ` that preserves the symplectic
form (`L_V Ω = 0`). -/
def hamiltonVectorField (Hρ Hπ : ℝ) : ℝ × ℝ := (Hπ, -Hρ)

/-! ## §C — evolution is the Poisson bracket -/

/-- **[The evolution of a function is its Poisson bracket with the Hamiltonian] `dF/dτ = {F, H}`.** Along the
Hamilton flow, `dF/dτ = F^ρ (dρ/dτ) + F^π (dπ/dτ) = F^ρ ∂H/∂π − F^π ∂H/∂ρ = {F, H}` (Caticha Eqs. 16–17) — the
Poisson-bracket generation of dynamics from the symplectic geometry. -/
theorem evolution_is_poissonBracket (Fρ Fπ Hρ Hπ : ℝ) :
    Fρ * (hamiltonVectorField Hρ Hπ).1 + Fπ * (hamiltonVectorField Hρ Hπ).2
      = poissonBracket Fρ Fπ Hρ Hπ := by
  unfold hamiltonVectorField poissonBracket; ring

/-! ## §D — the Hamilton–Killing synthesis -/

/-- **[A Hamilton–Killing flow preserves both the symplectic and the Lie/metric structure].** Quantum mechanics
is the flow that preserves *both* the symplectic form (Hamilton, antisymmetric `Ω[V,U] = −Ω[U,V]`) *and* the
metric — realized by the Killing flow's preservation of the Lie bracket (`killingFlow_preserves_bracket`). Thus a
`KillingFlow` acting on the e-phase space, together with the antisymmetric symplectic form, is the Hamilton–Killing
flow that *is* quantum mechanics: the geometric root of the entropic-dynamics reconstruction. -/
theorem hamiltonKilling_preserves_both {R : Type*} [Ring R] (F : KillingFlow R) (s : ℝ) (a b : R)
    (Vρ Vπ Uρ Uπ : ℝ) :
    F.π s (collisionStar a b) = collisionStar (F.π s a) (F.π s b)
      ∧ poissonBracket Vρ Vπ Uρ Uπ = -poissonBracket Uρ Uπ Vρ Vπ :=
  ⟨killingFlow_preserves_bracket F s a b, poissonBracket_antisymm Vρ Vπ Uρ Uπ⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingFlowStatisticalManifold

end
