/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric

/-!
# Linking the probability metrics to the information geometry (Wasserstein–Fisher, the de Bruijn/Otto identity)

Connects the probability metrics of the entropic-dynamics arc — the **Wasserstein** metric (the gradient flow of
`EntropicDynamicsWassersteinGradientFlow`) and the **Cramér** distance (`CramerDistanceCDFMetric`) — to the
repository's **information geometry**: the Fisher–Rao metric (`HamiltonKillingNormalizationInformationMetric`,
`fisherRaoMetric ρ = 1/2ρ`) and, through it, the entropic quantum potential. The link is the de Bruijn / Otto
identity: the **Wasserstein gradient-flow dissipation of the entropy is the Fisher information**.

The entropy `S = ∫ρ log ρ` has first-variation gradient `∂_χ(δS/δρ) = (∂_χρ)/ρ` (the score); the Wasserstein
metric measures its dissipation as `ρ·(∂_χρ/ρ)² = (∂_χρ)²/ρ`, which is exactly the Fisher information — the
entropic quantum potential `edQuantumPotential 1 ρ (∂_χρ)` — and hence the Fisher–Rao line element
`2·fisherRaoMetric·(∂_χρ)²` (`quantumPotential_is_fisherRao_lineElement`). So the transport (Wasserstein) geometry
and the information (Fisher–Rao) geometry meet: the speed of the entropy's steepest descent in the Wasserstein
metric is measured by the Fisher information.

* the **entropy's Wasserstein dissipation is the Fisher–Rao line element**
 `ρ·(∂_χρ/ρ)² = 2·fisherRaoMetric·(∂_χρ)²` (`entropy_wasserstein_dissipation_is_fisherRao`) — the de Bruijn / Otto
 identity, reusing `quantumPotential_is_fisherRao_lineElement`;
* the **local-time Fokker–Planck osmotic kinetic energy is half the Fisher–Rao line element**
 `ρ·(½ ∂_χρ/ρ)² = ½·fisherRaoMetric·(∂_χρ)²` (`ltfp_osmotic_kinetic_is_fisherRao`) — the osmotic velocity `½∂_χρ/ρ`
 of the local-time Fokker–Planck current (`currentPotential`) contributes the Fisher-information diffusion.

So the entropic-dynamics probability metrics form one geometric family with the repository's information geometry:
the **Wasserstein** metric (transport) whose entropy-dissipation is the **Fisher–Rao** metric (information), and the
**Cramér** distance as its `L²`-on-CDF sibling (`cramerDistance`, the `p=2` member with unbiased gradients). Two
further distances of the arc sit alongside: the **causal-spacetime entropic proper distance**
`r = λ_C log K` (`ComptonClock.EntropicProperDistance`, distance from the entanglement Schmidt number `K`) and the
**path-integral entropic weight** `e^{−S_I/ℏ} = kuikenWeight` (`PathIntegral.ComplexActionPathIntegralWeight`, the
`kuikenWeight` hub with the ED transition probability) — the probability, information, causal, and
path-integral distances of one entropic edifice.

* **§A — the Wasserstein dissipation is the Fisher–Rao metric** (`entropy_wasserstein_dissipation_is_fisherRao`).
* **§B — the Fokker–Planck osmotic kinetic energy is the Fisher–Rao metric** (`ltfp_osmotic_kinetic_is_fisherRao`).

The de Bruijn identity and the osmotic-kinetic identity are exact algebra, reusing
`fisherRaoMetric`, `quantumPotential_is_fisherRao_lineElement`, and `edQuantumPotential`. The full Otto calculus (the
Wasserstein metric tensor, the geodesics), the Cramér–Fisher relationship, and the causal / path-integral distances
are the referenced content. No new axioms.

## References

* R. Jordan, D. Kinderlehrer, F. Otto (Otto calculus); M.G. Bellemare et al., arXiv:1705.10743; A. Caticha
 (information geometry). Repo dependencies: `EntropicTime.HamiltonKillingNormalizationInformationMetric`
 (`fisherRaoMetric`), `EntropicTime.CramerDistanceCDFMetric` (`cramerDistance`, `wasserstein1Distance`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricInformationGeometry

/-! ## §A — the Wasserstein dissipation is the Fisher–Rao metric -/

/-- **[The entropy's Wasserstein dissipation is the Fisher–Rao line element] `ρ·(∂_χρ/ρ)² = 2·fisherRaoMetric·(∂_χρ)²`.**
The Wasserstein gradient-flow dissipation of the entropy — the probability `ρ` times the squared score
`(∂_χρ/ρ)²` — is the Fisher information `(∂_χρ)²/ρ` (the entropic quantum potential), hence the Fisher–Rao line
element `2·fisherRaoMetric·(∂_χρ)²` (`quantumPotential_is_fisherRao_lineElement`): the de Bruijn / Otto identity
linking the transport (Wasserstein) and information (Fisher–Rao) geometries. -/
theorem entropy_wasserstein_dissipation_is_fisherRao (ρ dρ : ℝ) (hρ : ρ ≠ 0) :
    ρ * (dρ / ρ) ^ 2 = 2 * fisherRaoMetric ρ * dρ ^ 2 := by
  rw [← quantumPotential_is_fisherRao_lineElement ρ dρ hρ]
  unfold edQuantumPotential
  field_simp

/-! ## §B — the Fokker–Planck osmotic kinetic energy is the Fisher–Rao metric -/

/-- **[The Fokker–Planck osmotic kinetic energy is half the Fisher–Rao line element]
`ρ·(½ ∂_χρ/ρ)² = ½·fisherRaoMetric·(∂_χρ)²`.** The osmotic velocity `½∂_χρ/ρ` of the local-time Fokker–Planck
current potential `Φ = φ − ½ log ρ` (`currentPotential`) has kinetic energy `ρ·(½∂_χρ/ρ)²` equal to half the
Fisher–Rao line element — the Fisher-information diffusion contributed by the osmotic (entropy-gradient) part of the
current velocity. -/
theorem ltfp_osmotic_kinetic_is_fisherRao (ρ dρ : ℝ) (hρ : ρ ≠ 0) :
    ρ * ((1 / 2) * (dρ / ρ)) ^ 2 = (1 / 2) * fisherRaoMetric ρ * dρ ^ 2 := by
  unfold fisherRaoMetric
  field_simp

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricInformationGeometry

end
