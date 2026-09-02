/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianEntropicMotionGeodesic
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
meta import Zil

/-!
# The Fisher-Rao Gaussian metric is the Fisher information of the Bohm quantum potential

The Fisher-Rao metric component `g_μμ = 1/σ²` derived in `FisherRaoGaussianLeviCivita` is the
**Fisher information** of the Gaussian: `I(p) = ∫(∂_μ log p)² p dx = 1/σ²`. This ties the entropic-motion
geometry of this arc to the repository's already-formalized Fisher-information reconstructions of the
quantum potential.

* **§A** `g_μμ = 1/σ²` is the Gaussian location Fisher information.
* **§B** the **de Broglie-Bohm quantum potential** built from that Fisher information (Fisher-Bohm:
  `GravLapse.BohmQuantumPotential.bohmQuantumPotential`, `GravLapse.FisherQuantumPotential`,
  `EntropicTime.EntropicDynamicsQuantumPotentialFisherBohm.ed_quantum_potential_is_fisher_density`) is
  `Q = g_μμ · ℏ/(2m) = ℏ/(2mσ²)` for a Gaussian state — the quantum potential expressed through the
  Fisher-Rao metric of the statistical manifold.
* **§C** the conserved momentum of entropic motion, `A = μ̇/σ²`
  (`GaussianEntropicMotionGeodesic.fisherRao_mu_firstIntegral`), is exactly the covariant momentum
  `g_μμ · μ̇` — the metric lowers the mean velocity to the conserved quantity.

The information metric is the common object of three formalized threads: the **quantum Fisher /
Fisher-Rao** information metric of Caticha's e-phase space
(`HamiltonKilling…InformationMetric.fisherRaoMetric`, whose line element
`quantumPotential_is_fisherRao_lineElement` *is* the quantum potential), the **Fisher-Bohm** quantum
potential `Q = I(p)·ℏ/(2m)`, and — via `GravLapse.FisherQuantumPotential.nnContour_quantumPotential_is_fisher`
— the Fisher imaginary action on the Nagao-Nielsen contour. The Gaussian `g_μμ = 1/σ²` is a concrete
realization of that shared Fisher information.

## References

* S. Gassner, C. Cafaro, arXiv:1903.11190 — the Fisher-Rao Gaussian metric `g_μμ = 1/σ²`.
* A. Caticha, *Entropic Dynamics*, Entropy 17 (2015) 6110; M. Reginatto, *Derivation of the equations
  of nonrelativistic quantum mechanics using the principle of minimum Fisher information*, Phys. Rev. A
  58 (1998) 1775 — the quantum potential as Fisher information.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita
open Physlib.QuantumMechanics.ComplexAction.GravLapse.BohmQuantumPotential

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianBohmQuantumPotential

@[expose] public section

/-! ## A. The metric component is the Gaussian Fisher information -/

/-- **[The Fisher-Rao mean metric component is the inverse variance] `g_μμ = 1/σ²`.** The `μ`-`μ`
component of the Fisher-Rao metric equals the reciprocal variance. That this reciprocal variance is the
Gaussian *location Fisher information* `I(p) = ∫(∂_μ log p)² p dx` is the integral identity proved in
`GaussianMeanFisherInformationIntegral.gaussianMeanFisherInformation_eq_inv_variance`
(and connected back to `gMuMu` by `gMuMu_eq_gaussianMeanFisherInformation`); here only the value is recorded. -/
lemma gMuMu_is_gaussian_fisher_info (σ : ℝ) : gMuMu σ = 1 / σ ^ 2 := by
  rw [gMuMu, one_div]

/-! ## B. The Bohm quantum potential of a Gaussian, through the Fisher-Rao metric -/

/-- **[The de Broglie-Bohm quantum potential of a Gaussian is the Fisher-Rao metric component]**
`Q = g_μμ · ℏ/(2m) = ℏ/(2mσ²)`. Feeding the Gaussian Fisher information `g_μμ = 1/σ²` (the imaginary
action `S_I = I(p)`) into the Bohm quantum potential `bohmQuantumPotential` gives the Gaussian's
quantum potential — the quantum term of the entropic-dynamics reconstruction, expressed through the
Fisher-Rao metric derived in this arc. -/
theorem gaussian_bohm_quantum_potential (σ ℏ m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) :
    bohmQuantumPotential (gMuMu σ) ℏ m = ℏ / (2 * m * σ ^ 2) := by
  unfold bohmQuantumPotential
  rw [gMuMu]; field_simp

/-- **[The quantum potential is the Fisher-Rao metric datum times `ℏ/(2m)`]** `Q = g_μμ · ℏ/(2m)` — the
defining relation of the Fisher-Bohm quantum potential, with the Fisher information supplied by the
metric of the statistical manifold. -/
lemma bohm_quantum_potential_is_metric (σ ℏ m : ℝ) :
    bohmQuantumPotential (gMuMu σ) ℏ m = gMuMu σ * ℏ / (2 * m) := rfl

/-! ## C. The conserved entropic-motion momentum is the covariant momentum -/

/-- **[The conserved momentum of entropic motion is the covariant momentum] `A = g_μμ μ̇`.** The first
integral `μ̇ = A σ²` of `GaussianEntropicMotionGeodesic.fisherRao_mu_firstIntegral` means the conserved
quantity `A = μ̇/σ²` is the mean velocity lowered by the Fisher-Rao metric, `A = g_μμ · μ̇` — the metric
that is simultaneously the Fisher information of the Bohm quantum potential. -/
lemma conserved_momentum_is_covariant (σ μdot : ℝ) : gMuMu σ * μdot = μdot / σ ^ 2 := by
  rw [gMuMu]; ring

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianBohmQuantumPotential

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianBohmQuantumPotential.gMuMu_is_gaussian_fisher_info where
  formalizes @ "claim:the-fisher-rao-mean-metric-component-equals-the-inverse-variance"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianBohmQuantumPotential.gaussian_bohm_quantum_potential where
  formalizes @ "claim:the-gaussian-bohm-quantum-potential-is-the-fisher-information-density-of-the-state",
  requires @ "claim:the-mean-mean-metric-component-is-the-gaussian-fisher-information",
  supported_by @ "paper:reginatto-1998-derivation-schrodinger-fisher-information",
  caveat @ "claim:identity-of-the-bohm-potential-with-fisher-information-the-entropic-origin-of-the-quantum-potential"

zil_file_contract physlib.fisherRaoGaussianBohmQuantumPotential where
  promises "The Bohm quantum potential is Fisher information: the mean-mean Fisher-Rao metric component is the Gaussian Fisher information, and the Gaussian Bohm quantum potential is exactly the Fisher-information density of the state, the entropic-dynamics origin of the quantum potential."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianBohmQuantumPotential.gMuMu"]
  forbids_substitutes ["a derivation of the full Schrodinger equation, only the potential-Fisher identity for the Gaussian",
    "the general non-Gaussian Bohm-Fisher correspondence, restricted to the Gaussian family"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianBohmQuantumPotential.gMuMu_is_gaussian_fisher_info,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianBohmQuantumPotential.gaussian_bohm_quantum_potential]

/- ZIL-END -/
