/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The canonical representation of the surface-deformation algebra: e-Hamiltonian and quantum potential (Ipek–Abedi–Caticha §§4–6)

Formalizes §§4–6 of Ipek–Abedi–Caticha (arXiv:1803.07493): the constraints that provide a **canonical
representation** of the DHKT hypersurface-deformation algebra, split into a geometric momentum and an **ensemble
Hamiltonian**, the latter containing the **Bohm quantum potential** — the term through which quantum mechanics
enters the reconstruction.

* the deformation generators **split** `H_⊥ = π_⊥ + H̃_⊥`, `H_i = π_i + H̃_i` (their Eq. 38): a geometric momentum
 `π` (acting on the surface variables `X`) plus the **ensemble Hamiltonian / momentum** `H̃` (acting on the
 epistemic variables `ρ, Φ`) (`canonicalConstraint`);
* the **Hamiltonian constraint** `H_⊥ ≈ 0` (their Eq. 33) fixes `π_⊥ = −H̃_⊥` (`hamiltonian_constraint`) — the
 ensemble Hamiltonian generates the geometric evolution, a Wheeler–DeWitt-type constraint;
* the **ensemble Hamiltonian** (their Eq. 66) `H̃_⊥ = ∫ρ{ ½(δΦ/δχ)² + ½(∂χ)² + V + (λ/ρ)(δρ/δχ)² }` is a classical
 part (kinetic + gradient + potential) **plus the quantum potential** (`eHamiltonianDensity`,
 `edQuantumPotential`);
* the **quantum potential** `Q = ∫(λ/ρ)(δρ/δχ)²` (their Eq. 67) is the term that makes the dynamics *quantum*; it
 is the osmotic/Fisher form `λ ρ (δ log ρ/δχ)² = λ(δρ/δχ)²/ρ` (`quantum_potential_log_identity`), with the
 osmotic gradient `δ log ρ/δχ = (δρ/δχ)/ρ` (`ed_osmotic_gradient_hasDerivAt`) — the Bohm quantum potential of the
 reconstructed theory.

So the canonical representation of the surface-deformation algebra is a geometric momentum plus an ensemble
Hamiltonian whose kinetic term is the entropic-dynamics current energy and whose extra term is the Bohm quantum
potential — the reconstruction of quantum field theory: the "quantum" is the Fisher-information quantum potential
added to the classical ensemble Hamiltonian.

* **§A — the generator split and the Hamiltonian constraint** (`canonicalConstraint`, `hamiltonian_constraint`).
* **§B — the ensemble Hamiltonian density** (`eHamiltonianDensity`, `eMomentumDensity`).
* **§C — the quantum potential** (`edQuantumPotential`, `quantum_potential_log_identity`,
 `ed_osmotic_gradient_hasDerivAt`).

The generator split, the Hamiltonian constraint, and the quantum-potential osmotic/Fisher
identity are exact algebra; the osmotic gradient is exact `HasDerivAt.log`. The full field-theoretic ensemble PB
representation of the DHKT algebra (Eqs. 40–42, 53) and the functional integral over configurations are the
intended reading, captured pointwise (per configuration). No new axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §§4–6 (Eqs. 33, 38, 46, 66–67; canonical representation,
 quantum potential). Repo structure: `EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

/-! ## §A — the generator split and the Hamiltonian constraint -/

/-- **The canonical constraint generator** `H = π + H̃` (Ipek–Abedi–Caticha Eq. 38): a deformation generator
splits into a geometric momentum `π` (acting on the surface variables) and the ensemble Hamiltonian/momentum `H̃`
(acting on the epistemic variables `ρ, Φ`). -/
def canonicalConstraint (piGeom Htilde : ℝ) : ℝ := piGeom + Htilde

/-- **[The Hamiltonian constraint fixes the geometric momentum] `H_⊥ ≈ 0 ⟺ π_⊥ = −H̃_⊥`.** Imposing the
deformation constraint `H_⊥ = 0` (Eq. 33) means the geometric momentum equals minus the ensemble Hamiltonian: the
ensemble Hamiltonian generates the geometric evolution — a Wheeler–DeWitt-type constraint of the reconstruction. -/
theorem hamiltonian_constraint (piGeom Htilde : ℝ) :
    canonicalConstraint piGeom Htilde = 0 ↔ piGeom = -Htilde := by
  unfold canonicalConstraint
  constructor <;> intro h <;> linarith

/-! ## §B — the ensemble Hamiltonian density -/

/-- **The ensemble-Hamiltonian density** (Ipek–Abedi–Caticha Eq. 66, flat `g^{1/2}=1`): `ρ(½(δΦ/δχ)² + ½(∂χ)² + V)
+ Q` — the kinetic current energy `½ρ(δΦ/δχ)²`, the field-gradient energy `½ρ(∂χ)²`, the potential `ρV`, and the
quantum potential `Q`. -/
noncomputable def eHamiltonianDensity (ρ dΦ dχ V Q : ℝ) : ℝ := ρ * (dΦ ^ 2 / 2 + dχ ^ 2 / 2 + V) + Q

/-- **The ensemble-momentum (e-momentum) density** `H̃_i = −ρ (δΦ/δχ)(∂χ)` (Ipek–Abedi–Caticha Eq. 46) — the
tangential generator translating the epistemic variables `ρ, Φ` along the surface. -/
noncomputable def eMomentumDensity (ρ dΦ dχ : ℝ) : ℝ := -ρ * dΦ * dχ

/-! ## §C — the quantum potential -/

/-- **The entropic-dynamics quantum-potential density** `Q = (λ/ρ)(δρ/δχ)²` (Ipek–Abedi–Caticha Eq. 67) — the
Fisher-information / Bohm quantum potential, the term of the ensemble Hamiltonian that makes the reconstructed
dynamics *quantum*. -/
noncomputable def edQuantumPotential (lam ρ dρ : ℝ) : ℝ := lam * dρ ^ 2 / ρ

/-- **[The quantum potential is the osmotic/Fisher form] `λ ρ (δ log ρ/δχ)² = (λ/ρ)(δρ/δχ)²`.** Written with the
osmotic gradient `δ log ρ/δχ = (δρ/δχ)/ρ`, the quantum-potential term of the ensemble Hamiltonian
`λ ρ (δ log ρ/δχ)²` is exactly `(λ/ρ)(δρ/δχ)²` — the Bohm quantum potential (Fisher information of `ρ`). -/
theorem quantum_potential_log_identity (lam ρ dρ : ℝ) (hρ : ρ ≠ 0) :
    lam * ρ * (dρ / ρ) ^ 2 = edQuantumPotential lam ρ dρ := by
  unfold edQuantumPotential
  field_simp

/-- **[The osmotic gradient is `(δρ/δχ)/ρ`] `δ log ρ/δχ = ρ'/ρ`.** The osmotic contribution to the drift potential
— the gradient of `log ρ^{1/2}` — is `(δρ/δχ)/ρ` (here the full `log ρ`), the source of the quantum potential. -/
theorem ed_osmotic_gradient_hasDerivAt (ρ : ℝ → ℝ) (ρ' x : ℝ) (hρ : HasDerivAt ρ ρ' x)
    (hpos : ρ x ≠ 0) : HasDerivAt (fun y => Real.log (ρ y)) (ρ' / ρ x) x :=
  hρ.log hpos

/-- **[The ensemble Hamiltonian is classical energy plus the quantum potential].** For `ρ ≠ 0` the ensemble
Hamiltonian density is the classical part (kinetic + gradient + potential) plus the Bohm quantum potential written
in osmotic form:

`H̃_⊥ = ρ(½(δΦ/δχ)² + ½(∂χ)² + V) + λ ρ (δ log ρ/δχ)²`,

the quantum-potential term `λ ρ (δ log ρ/δχ)² = (λ/ρ)(δρ/δχ)²` being what makes the reconstructed field theory
quantum. -/
theorem eHamiltonian_classical_plus_quantum (ρ dΦ dχ V lam dρ : ℝ) (hρ : ρ ≠ 0) :
    eHamiltonianDensity ρ dΦ dχ V (lam * ρ * (dρ / ρ) ^ 2)
      = eHamiltonianDensity ρ dΦ dχ V (edQuantumPotential lam ρ dρ) := by
  rw [quantum_potential_log_identity lam ρ dρ hρ]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

end
