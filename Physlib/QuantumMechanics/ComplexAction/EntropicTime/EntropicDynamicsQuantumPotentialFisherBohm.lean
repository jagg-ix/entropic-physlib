/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

/-!
# The entropic-dynamics quantum potential is Fisher information, osmotic energy, and the Bohm potential

Links the entropic-dynamics quantum potential (Ipek–Abedi–Caticha Eq. 67, `EntropicDynamicsCanonicalRepresentation`)
to the repository's existing quantum-potential infrastructure: the **Fisher information**
(`StatisticalMechanics.FisherInformationCoercivity.FisherInformationData`, `fisherInfo = ∫|∇log p|²·p`), the
**osmotic velocity**, and the **de Broglie–Bohm quantum potential**
(`Schrodinger.BohmianQuantumPotential.quantumPotential = −ℏ²ΔR/(2mR)`, `Schrodinger.guidanceVelocity`). The ED
quantum-potential density `Q = (λ/ρ)(δρ/δχ)²` is one object seen three ways:

* it **is the Fisher information density** `ρ (δ log ρ/δχ)²` (`ed_quantum_potential_is_fisher_density`) — the
 integrand of the repository's `FisherInformationData.fisherInfo = ∫|∇log p|²·p`, so the ED "quantum" term is the
 Fisher information of the probability;
* it **is four times the osmotic kinetic energy** `4 ρ u²` with osmotic velocity `u = (δρ/δχ)/(2ρ)`
 (`ed_quantum_potential_is_osmotic`) — the Nelson/Bohm osmotic contribution;
* in **amplitude form** `ρ = R²` it is `4(δR/δχ)²` (`ed_quantum_potential_is_amplitude_gradient`) — the gradient of
 the Madelung amplitude `R = √ρ`, the pre-integration-by-parts form of the Bohm quantum potential
 `−ℏ²ΔR/(2mR)`.

So the term that makes entropic dynamics quantum (Eq. 67) is exactly the Fisher information / osmotic energy /
amplitude-gradient that the repository's Madelung–Bohm and Fisher-information modules already encode — the ED
reconstruction's quantum potential and the de Broglie–Bohm quantum potential are the same object on the
`kuikenWeight` / Madelung structure.

* **§A — Fisher information density** (`ed_quantum_potential_is_fisher_density`).
* **§B — osmotic kinetic energy** (`ed_quantum_potential_is_osmotic`).
* **§C — Madelung amplitude gradient** (`ed_quantum_potential_is_amplitude_gradient`).

The three identities are exact field algebra relating `edQuantumPotential` to the Fisher,
osmotic, and amplitude forms. The integral relation to the Laplacian Bohm potential `−ℏ²ΔR/(2mR)` (integration by
parts) and the `FisherInformationData` functional are the referenced targets, linked at the density level. No new
axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, Eq. 67; D. Bohm; E. Nelson (osmotic velocity); R.A. Fisher.
 Repo dependencies: `EntropicTime.EntropicDynamicsCanonicalRepresentation`,
 `Schrodinger.BohmianQuantumPotential` (`quantumPotential`),
 `StatisticalMechanics.FisherInformationCoercivity` (`FisherInformationData`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsQuantumPotentialFisherBohm

/-! ## §A — Fisher information density -/

/-- **[The ED quantum potential is the Fisher information density] `(1/ρ)(δρ/δχ)² = ρ(δ log ρ/δχ)²`.** The
entropic-dynamics quantum-potential density (`λ = 1`) equals `ρ` times the squared osmotic gradient
`δ log ρ/δχ = (δρ/δχ)/ρ` — the integrand of the Fisher information `I(ρ) = ∫|∇log ρ|²·ρ`
(`FisherInformationData.fisherInfo`). The ED "quantum" term is the Fisher information of the probability. -/
theorem ed_quantum_potential_is_fisher_density (ρ dρ : ℝ) (hρ : ρ ≠ 0) :
    ρ * (dρ / ρ) ^ 2 = edQuantumPotential 1 ρ dρ := by
  have h := quantum_potential_log_identity 1 ρ dρ hρ
  simpa using h

/-! ## §B — osmotic kinetic energy -/

/-- **[The ED quantum potential is four times the osmotic kinetic energy] `(1/ρ)(δρ/δχ)² = 4ρu²`.** With the
osmotic velocity `u = (δρ/δχ)/(2ρ)` (the Nelson/Bohm osmotic drift), the ED quantum-potential density is `4ρu²` —
the osmotic kinetic energy of the diffusion, the quantum contribution to the ensemble Hamiltonian. -/
theorem ed_quantum_potential_is_osmotic (ρ dρ : ℝ) (hρ : ρ ≠ 0) :
    4 * ρ * (dρ / (2 * ρ)) ^ 2 = edQuantumPotential 1 ρ dρ := by
  unfold edQuantumPotential
  field_simp
  ring

/-! ## §C — Madelung amplitude gradient -/

/-- **[The ED quantum potential in amplitude form is `4(δR/δχ)²`]** with `ρ = R²`, `δρ = 2R δR`. In terms of the
Madelung amplitude `R = √ρ` the ED quantum-potential density is `4(δR/δχ)²` — the squared gradient of the
amplitude, the pre-integration-by-parts form of the de Broglie–Bohm quantum potential `−ℏ²ΔR/(2mR)`. -/
theorem ed_quantum_potential_is_amplitude_gradient (R dR : ℝ) (hR : R ≠ 0) :
    edQuantumPotential 1 (R ^ 2) (2 * R * dR) = 4 * dR ^ 2 := by
  unfold edQuantumPotential
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsQuantumPotentialFisherBohm

end
