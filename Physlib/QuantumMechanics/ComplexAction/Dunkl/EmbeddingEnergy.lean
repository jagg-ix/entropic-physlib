/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.PhaseSpaceEntropy
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KinematicEntropicTransformations

/-!
# The Wigner–Dunkl complex path integral on the `ℝ^{2,d}` embedding energy = Bogoliubov dispersion

Feeds the Wigner–Dunkl complex-action / Feynman–Kac path integral (`Dunkl.PhaseSpaceEntropy`,
`Dunkl.LorentzianPropagator`) the causal-diamond embedding-energy theorem
`embeddingEnergy_eq_bogoliubov` (`CausalDiamond.EmbeddingZerothLaw`): the `ℝ^{2,d}` de Sitter
embedding coordinate `X^d` **is** the Bogoliubov dispersion of the mode `(ξ, Δ) = (X⁰, w)`,
`X^d = bogoliubovEnergy(X⁰, w) = √((w sinh η)² + w²) = w√(sinh²η + 1) = w cosh η`.

We make this embedding energy the *reversible* part `H_R` of the complex Hamiltonian `Ĥ = H_R − iH_I`.
Then the complex-action propagator's oscillatory phase `e^{−it·X^d/ℏ}` runs at the `ℝ^{2,d}` embedding =
Bogoliubov dispersion, while (from `Dunkl.PhaseSpaceEntropy`) the modulus is the entropy-production
damping. The two halves of the complex path integral are exactly the two halves of the causal diamond:
the embedding energy `X^d` (reversible phase) and the entropic time `τ_ent = binEntropy((1−v)/2)`
(irreversible damping), with the embedding velocity `v = X⁰/X^d = tanh η`.

* **§A** `dunklEmbeddingComplexH`, `dunklEmbedding_H_R_eq` — the complex Hamiltonian whose reversible part
  is `X^d = bogoliubovEnergy(X⁰, w) = w cosh η`.
* **§B** `dunklEmbedding_propagator_norm` — the complex-action propagator's modulus is the Euclidean
  Dunkl weight; its phase runs at the embedding/Bogoliubov energy.
* **§C** `dunklEmbedding_unit_eq_diamond` — the unit hyperboloid `w = 1` reproduces the diamond horizon
  energy `cosh η` (`embedding_unit_eq_diamondEnergy`).
* **§D** `dunklEmbedding_velocity`, `dunklEmbedding_entropicTime` — the embedding velocity `X⁰/X^d = tanh η`
  fixes the irreversible entropic time `τ_ent = binEntropy((1−tanh η)/2)`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.EmbeddingEnergy

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw


/-- **The Wigner–Dunkl complex Hamiltonian on the `ℝ^{2,d}` embedding energy.** `Ĥ = H_R − iH_I` with
reversible part the embedding coordinate `H_R = X^d = bogoliubovEnergy(X⁰, w) = bogoliubovEnergy(w sinh η, w)`
(the Bogoliubov dispersion of the diamond mode `(ξ, Δ) = (X⁰, w)`) and dissipative part `H_I ≥ 0`. -/
noncomputable def dunklEmbeddingComplexH (w η HI : ℝ) (hI : 0 ≤ HI) : ComplexHamiltonian :=
  { H_R := bogoliubovEnergy (w * Real.sinh η) w, H_I := HI, H_I_nonneg := hI }

/-- **[Consume `embeddingEnergy_eq_bogoliubov`] The reversible energy is `X^d = w cosh η`.** The complex
Hamiltonian's reversible part is `bogoliubovEnergy(w sinh η, w) = w cosh η` (`hw : 0 ≤ w`): the `ℝ^{2,d}`
embedding energy that the complex-action propagator's phase oscillates at. -/
lemma dunklEmbedding_H_R_eq (w η HI : ℝ) (hI : 0 ≤ HI) (hw : 0 ≤ w) :
    (dunklEmbeddingComplexH w η HI hI).H_R = w * Real.cosh η := by
  rw [dunklEmbeddingComplexH, embeddingEnergy_eq_bogoliubov w η hw]


/-- **[Bridge] The complex-action propagator of the embedding mode.** Its modulus is the Euclidean Dunkl
weight `matsubaraBoltzmannWeight (t/ℏ) H_I` (`Dunkl.PhaseSpaceEntropy` entropy damping); its reversible
phase `e^{−it·X^d/ℏ}` oscillates at the `ℝ^{2,d}` embedding energy `X^d = bogoliubovEnergy(X⁰, w)`
(`dunklEmbedding_H_R_eq`). The Feynman–Kac complex path integral runs on the Bogoliubov dispersion. -/
lemma dunklEmbedding_propagator_norm (w η HI t ℏ : ℝ) (hI : 0 ≤ HI) :
    ‖lorentzianPropagator (dunklEmbeddingComplexH w η HI hI) t ℏ‖ = matsubaraBoltzmannWeight (t / ℏ) HI := by
  rw [lorentzianPropagator_norm_is_damping]; unfold matsubaraBoltzmannWeight dunklEmbeddingComplexH
  congr 1; ring

/-- **The propagator's reversible phase carries the embedding/Bogoliubov energy** `H_R =
bogoliubovEnergy(w sinh η, w)`. -/
lemma dunklEmbedding_propagator_phase (w η HI : ℝ) (hI : 0 ≤ HI) :
    (dunklEmbeddingComplexH w η HI hI).H_R = bogoliubovEnergy (w * Real.sinh η) w := rfl


/-- **[Consume `embedding_unit_eq_diamondEnergy`] At `w = 1` the reversible energy is the diamond horizon
energy `cosh η`.** `bogoliubovEnergy(sinh η, 1) = cosh η` — the unit-hyperboloid embedding reproduces
`diamond_horizon_energy` of the helicity / metric-common-root bridge, exactly. -/
lemma dunklEmbedding_unit_eq_diamond (η HI : ℝ) (hI : 0 ≤ HI) :
    (dunklEmbeddingComplexH 1 η HI hI).H_R = Real.cosh η := by
  rw [dunklEmbeddingComplexH, one_mul, embedding_unit_eq_diamondEnergy]


/-- **[Consume `embeddingVelocity_eq_tanh`] The embedding velocity is `X⁰/X^d = tanh η`** (`hw : 0 < w`):
the ratio of the two timelike embedding coordinates, the boost velocity `v = ξ/E` that the complex path
integral's entropic damping depends on. -/
lemma dunklEmbedding_velocity (w η : ℝ) (hw : 0 < w) :
    (w * Real.sinh η) / bogoliubovEnergy (w * Real.sinh η) w = Real.tanh η :=
  embeddingVelocity_eq_tanh w η hw

/-- **[Consume `embedding_entropicTime_eq_velocity`] The irreversible entropic time of the embedding mode**
`τ_ent = binEntropy((1 − tanh η)/2)` (`hw : 0 < w`). With the embedding energy `X^d` carrying the reversible
phase (§B), this `binEntropy` of the embedding velocity `v = tanh η` is the irreversible
entropy-production half (`Dunkl.PhaseSpaceEntropy.dunklEntropyProduction`) of the complex path
integral — the two halves are the diamond's `(X^d, τ_ent)`. -/
lemma dunklEmbedding_entropicTime (w η : ℝ) (hw : 0 < w) :
    bogoliubovEntropicTime (w * Real.sinh η) w = Real.binEntropy ((1 - Real.tanh η) / 2) :=
  embedding_entropicTime_eq_velocity w η hw

/-- **[Kinematic rapidity = Dunkl/Bogoliubov embedding entropic time]** For
embedding coordinates `(X⁰, Xᵈ) = (w·sinh η, w·cosh η)`, the Bogoliubov mode
`(ξ, Δ) = (w·sinh η, w)` has velocity `tanh η`, so the rapidity entropy is
exactly the complex-action embedding entropy. -/
lemma kinematicEntropy_eq_dunklEmbedding_entropicTime (w η : ℝ) (hw : 0 < w) :
    EntropicTime.KinematicEntropicTransformations.kinematicEntropy η =
      bogoliubovEntropicTime (w * Real.sinh η) w := by
  simpa [EntropicTime.KinematicEntropicTransformations.kinematicEntropy] using
    (dunklEmbedding_entropicTime w η hw).symm

end Physlib.QuantumMechanics.ComplexAction.Dunkl.EmbeddingEnergy

end
