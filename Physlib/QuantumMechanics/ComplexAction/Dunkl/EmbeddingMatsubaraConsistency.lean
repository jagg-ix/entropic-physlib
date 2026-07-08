/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EmbeddingEnergy
public import Physlib.QuantumMechanics.NonHermitian.WickRotation

/-!
# Consistency of the embedding-energy complex path integral with the Matsubara path integral

`Dunkl.EmbeddingEnergy` put the `ℝ^{2,d}` embedding energy `X^d = bogoliubovEnergy(X⁰, w) = w cosh η`
into the *reversible* part `H_R` of the Wigner–Dunkl complex Hamiltonian, so the complex-action propagator's
phase `e^{−it X^d/ℏ}` oscillates at the Bogoliubov dispersion. This file proves that construction is
**consistent with the Matsubara (thermal, imaginary-time) path integral**: Wick-rotating the reversible
phase of the embedding mode to imaginary time `t = −iβℏ` reproduces exactly the Matsubara Boltzmann weight
`e^{−βX^d}` of the embedding energy.

The engine is `WickRotation.reversiblePhase_wickRotation` (`e^{−iE_R t/ℏ}|_{t=−iτ} = e^{−E_R τ/ℏ}`): the
real-time oscillation and the imaginary-time thermal weight are the same analytic function continued.

* **§A — general Wick ↔ Matsubara** (`reversiblePhaseC_wick_eq_matsubara`): for any reversible energy `E`,
  `reversiblePhaseC E ℏ (−iβℏ) = matsubaraBoltzmannWeight β E` — the imaginary-time period `τ = βℏ` turns the
  unitary phase into the thermal weight.
* **§B — the embedding mode** (`embedding_wickRotation_eq_matsubara`): the same, with `E = X^d =
  bogoliubovEnergy(w sinh η, w)` — the Wigner–Dunkl complex path integral on the embedding energy is
  Matsubara-consistent.
* **§C — the diamond unit case** (`embedding_unit_wickRotation_diamond`): `w = 1` gives the Matsubara
  weight of the diamond horizon energy `cosh η`.
* **§D — the full two-sector factor** (`embedding_euclidean_factor_eq_matsubara`): the embedding mode's
  two-sector Wick rotation (reversible heat kernel × entropy damping) is the Euclidean evolution factor,
  whose energy sector is the Matsubara weight `e^{−βX^d}` and whose entropy sector is the
  `Dunkl.PhaseSpaceEntropy` damping — the complex, Euclidean, and Matsubara path integrals agree.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.EmbeddingMatsubaraConsistency

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EmbeddingZerothLaw
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-! ## §A — general consistency: Wick rotation at `τ = βℏ` is the Matsubara Boltzmann weight -/

/-- **[Wick ↔ Matsubara] The Wick rotation of a reversible phase at imaginary-time period `τ = βℏ` is the
Matsubara Boltzmann weight.** `reversiblePhaseC E ℏ (−iβℏ) = e^{−βE} = matsubaraBoltzmannWeight β E`. The
real-time oscillation `e^{−iEt/ℏ}` and the thermal weight `e^{−βE}` are one analytic continuation — the
foundation of the imaginary-time (Matsubara) formalism. -/
theorem reversiblePhaseC_wick_eq_matsubara (E β ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    reversiblePhaseC E ℏ (-Complex.I * ((β * ℏ : ℝ) : ℂ))
      = ((matsubaraBoltzmannWeight β E : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation]; unfold matsubaraBoltzmannWeight
  norm_cast; congr 1; field_simp

/-! ## §B — the embedding mode is Matsubara-consistent -/

/-- **The Matsubara Boltzmann weight of the embedding energy** is `e^{−βX^d}` with `X^d = w cosh η`. -/
theorem embedding_matsubara_weight (w η β : ℝ) (hw : 0 ≤ w) :
    matsubaraBoltzmannWeight β (bogoliubovEnergy (w * Real.sinh η) w)
      = Real.exp (-(β * (w * Real.cosh η))) := by
  rw [embeddingEnergy_eq_bogoliubov w η hw]; rfl

/-- **[Main consistency] The Wigner–Dunkl complex path integral on the embedding energy is consistent with
the Matsubara path integral.** Wick-rotating the reversible phase of the embedding mode `X^d =
bogoliubovEnergy(X⁰, w)` to imaginary time `t = −iβℏ` gives the Matsubara Boltzmann weight `e^{−βX^d}`:
`reversiblePhaseC X^d ℏ (−iβℏ) = matsubaraBoltzmannWeight β X^d`. The complex-action propagator (real time)
and the thermal partition-function weight (imaginary time) of the embedding/Bogoliubov mode coincide. -/
theorem embedding_wickRotation_eq_matsubara (w η β ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    reversiblePhaseC (bogoliubovEnergy (w * Real.sinh η) w) ℏ (-Complex.I * ((β * ℏ : ℝ) : ℂ))
      = ((matsubaraBoltzmannWeight β (bogoliubovEnergy (w * Real.sinh η) w) : ℝ) : ℂ) :=
  reversiblePhaseC_wick_eq_matsubara _ β ℏ hℏ

/-! ## §C — the diamond unit case -/

/-- **At `w = 1` the embedding mode's Matsubara weight is that of the diamond horizon energy `cosh η`.**
`reversiblePhaseC (cosh η) ℏ (−iβℏ) = matsubaraBoltzmannWeight β (cosh η)` — the unit-hyperboloid
(diamond-horizon) thermal weight, consistent with the complex path integral. -/
theorem embedding_unit_wickRotation_diamond (η β ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    reversiblePhaseC (Real.cosh η) ℏ (-Complex.I * ((β * ℏ : ℝ) : ℂ))
      = ((matsubaraBoltzmannWeight β (Real.cosh η) : ℝ) : ℂ) :=
  reversiblePhaseC_wick_eq_matsubara _ β ℏ hℏ

/-! ## §D — the full two-sector factor: complex = Euclidean = Matsubara -/

/-- **[Two-sector consistency] The embedding mode's full Wick rotation is the Euclidean evolution factor,
whose energy sector is the Matsubara weight.** Rotating the reversible phase (`t = −iτ`) while with the
entropy damping `e^{−S_I/ℏ}` over unchanged gives `euclideanEvolutionFactor (X^d·τ) S_I ℏ` — the reversible
embedding-energy heat kernel times the irreversible entropy damping
(`Dunkl.PhaseSpaceEntropy.dunklEntropyProduction`). At `τ = βℏ` the energy sector is the Matsubara
Boltzmann weight `e^{−βX^d}`; so the complex, Euclidean, and Matsubara path integrals of the embedding mode
all agree. -/
theorem embedding_euclidean_factor_eq_matsubara (w η S_I ℏ τ : ℝ) :
    reversiblePhaseC (bogoliubovEnergy (w * Real.sinh η) w) ℏ (-Complex.I * (τ : ℂ))
        * ((entropyDamping S_I ℏ : ℝ) : ℂ)
      = ((euclideanEvolutionFactor (bogoliubovEnergy (w * Real.sinh η) w * τ) S_I ℏ : ℝ) : ℂ) :=
  lorentzian_to_euclidean_wickRotation _ S_I ℏ τ

end Physlib.QuantumMechanics.ComplexAction.Dunkl.EmbeddingMatsubaraConsistency

end
