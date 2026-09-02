/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
meta import Zil

/-!
# The `G`-free inference coupling reaches the isolated (infinite-space) Newton source

The finite-source layer routes the independent Compton-cell coupling `G = ℏc·σ₀⁴` through a configuration
of finitely many point masses strictly inside the entanglement screen. This file supplies the
**infinite-space** complement: a single **isolated** distributional Newton source over all of `ℝ³`
(`IsolatedNewtonHodgeSphereFlux`), whose potential and field are defined on the whole space rather than
confined inside a screen.

Tiling the entanglement screen by Compton cells at the inference mass `m = 1/σ₀²` gives the `G`-free bit
count `N = comptonCellBits m c ℏ η`, which fixes `G = ℏc·σ₀⁴` (`newtonG_from_positionVariance`) with no `G`
input. Feeding that `G` and `N` into the isolated-source chain
(`isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain`) yields, in one statement:

* the area-per-bit coupling `G = 𝒜c³/(ℏN)`;
* the distributional Poisson law `Δᵈ Φ = (surface flux)·δ_{x₀}` for the isolated source;
* the enclosing-sphere Gauss flux `∮ = 4πG·M`;
* the area-per-bit-per-radius identity `G·M/R² = 4πM c³/(ℏN)`;
* the Nagao–Nielsen horizon damping `‖nnPathWeight‖ = exp(−N/4)`;
* the Einstein coupling `8πG/c⁴ = 8π(𝒜/N)/(ℏc)`.

The `hbits` premise `N = holographicBits(𝒜, G, ℏ, c)` — which the chain still consumes — is supplied here
from the `G`-free side via `holographicBits_eq_comptonCellBits_of_massScale` at `m = 1/σ₀²`
(`ℏc/m² = ℏc·σ₀⁴`), so the identification enters as the content of a proven equality rather than a
circular assumption.

**Honest layering.** This is a round-screen, weak-field, single-isolated-source statement over infinite
space; it does not infer an arbitrary-surface divergence theorem, solve a nonlinear point-mass spacetime,
or independently determine the numerical value of `σ₀`.

## References

* Companions: `EntropicTime.IsolatedNewtonHodgeSphereFlux` (the isolated distributional Newton chain),
  `EntropicTime.FiniteNewtonEnclosingSphereFlux` (the finite confined-source chain),
  `ComptonClock.ComptonCellNewtonConstant` (`G = ℏc·σ₀⁴` from the `G`-free Compton-cell bit count).
-/

set_option autoImplicit false

open MeasureTheory
open scoped Space
open Physlib
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux

/-- **[The inference-variance coupling reaches the isolated infinite-space Newton source].**  Tile the
entanglement screen by Compton cells at the inference mass `m = 1/σ₀²`. The resulting `G`-free count fixes
`G = ℏc·σ₀⁴`; the isolated distributional Newton source over all of `ℝ³` then gives the area-per-bit
coupling, the distributional Poisson law with its surface-flux Dirac source, the `4πG·M` enclosing-sphere
Gauss flux, the Nagao–Nielsen horizon damping, and the Einstein coupling — in one chain, with the bit-count
premise supplied `G`-free. -/
theorem comptonCellInference_isolatedNewton_surfaceFluxEinstein_chain
    (S_R ℏ c σ₀ η M : ℝ) (x₀ : Space 3)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hσ : 0 < σ₀) (hη : 0 < η) :
    let m := inferenceMass σ₀
    let R := entropicProperDistance m c ℏ η
    let N := comptonCellBits m c ℏ η
    let G := ℏ * c * σ₀ ^ 4
    G = sphereArea R * c ^ 3 / (ℏ * N)
      ∧ Δᵈ (isolatedNewtonPotentialDistribution3At G M x₀) =
          sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) •
            Physlib.Distribution.diracDelta ℝ x₀
      ∧ sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) =
          4 * Real.pi * G * M
      ∧ G * M / R ^ 2 = 4 * Real.pi * M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
          Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
          8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  dsimp only
  have hm : 0 < inferenceMass σ₀ := by rw [inferenceMass]; positivity
  have hR : 0 < entropicProperDistance (inferenceMass σ₀) c ℏ η :=
    entropicProperDistance_pos (inferenceMass σ₀) c ℏ η hm hc hℏ hη
  have hG : ℏ * c * σ₀ ^ 4 ≠ 0 := by positivity
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    ne_of_gt (Real.log_pos (schmidtNumber_gt_one η hη))
  have hArea : ℏ * c * σ₀ ^ 4 =
      sphereArea (entropicProperDistance (inferenceMass σ₀) c ℏ η) * c ^ 3 /
        (ℏ * comptonCellBits (inferenceMass σ₀) c ℏ η) :=
    (newtonG_from_positionVariance σ₀ c ℏ η hσ.ne' hc.ne' hℏ.ne' hlog).symm
  have hGeq : ℏ * c / (inferenceMass σ₀) ^ 2 = ℏ * c * σ₀ ^ 4 := by
    rw [inferenceMass, inv_pow, div_inv_eq_mul]; ring
  have hbits : comptonCellBits (inferenceMass σ₀) c ℏ η =
      holographicBits (sphereArea (entropicProperDistance (inferenceMass σ₀) c ℏ η))
        (ℏ * c * σ₀ ^ 4) ℏ c := by
    rw [← hGeq]
    exact (holographicBits_eq_comptonCellBits_of_massScale (inferenceMass σ₀) c ℏ η
      hm.ne' hc.ne' hℏ.ne').symm
  exact ⟨hArea,
    isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain S_R (ℏ * c * σ₀ ^ 4) M ℏ c
      (comptonCellBits (inferenceMass σ₀) c ℏ η)
      (entropicProperDistance (inferenceMass σ₀) c ℏ η) x₀ hℏ.ne' hc.ne' hG hR hbits⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux.comptonCellInference_isolatedNewton_surfaceFluxEinstein_chain where
  formalizes @ "claim:the-g-free-compton-cell-inference-coupling-g-equals-hbar-c-sigma-0-to-the-fourth-reaches-the-isolated-infinite-space-newton-distributional-source-giving-the-area-per-bit-coupling-poisson-law-gauss-flux-nagao-nielsen-damping-and-einstein-coupling-in-one-chain-with-the-bit-count-premise-supplied-g-free",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  caveat @ "claim:round-screen-weak-field-single-isolated-source-statement-not-an-arbitrary-surface-divergence-theorem-nor-a-nonlinear-point-mass-spacetime-nor-an-independent-determination-of-sigma-0"

zil_file_contract physlib.comptonCellIsolatedNewtonFlux where
  promises "The infinite-space (isolated-source) complement of the finite confined-source layer for the independent Compton-cell gravitational coupling. Tiling the entanglement screen by Compton cells at the inference mass m = 1/sigma_0^2 gives the G-free bit count N = comptonCellBits, which fixes G = hbar c sigma_0^4 (newtonG_from_positionVariance) with no G input; feeding that G and N into the isolated distributional Newton source over all of R^3 (isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain) yields in one statement the area-per-bit coupling G = A c^3/(hbar N), the distributional Poisson law Laplacian Phi = (surface flux) dirac at x0, the enclosing-sphere Gauss flux 4 pi G M, the area-per-bit-per-radius identity G M/R^2 = 4 pi M c^3/(hbar N), the Nagao-Nielsen horizon damping norm nnPathWeight = exp(-N/4), and the Einstein coupling 8 pi G/c^4 = 8 pi (A/N)/(hbar c). The holographic bit-count premise the chain consumes is supplied G-free via holographicBits_eq_comptonCellBits_of_massScale at m = 1/sigma_0^2 (hbar c/m^2 = hbar c sigma_0^4), so the identification is the content of a proven equality, not a circular assumption. Honest: a round-screen, weak-field, single-isolated-source statement over infinite space; not an arbitrary-surface divergence theorem, not a nonlinear point-mass spacetime, and not an independent determination of sigma_0."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.holographicBits_eq_comptonCellBits_of_massScale"]
  forbids_substitutes ["the circular Planck-cell bit count N = A c^3/(G hbar), whereas the count here is the G-free Compton tiling",
    "a confined finite-source configuration, whereas this is the single isolated source over infinite space"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux.comptonCellInference_isolatedNewton_surfaceFluxEinstein_chain]

/- ZIL-END -/
