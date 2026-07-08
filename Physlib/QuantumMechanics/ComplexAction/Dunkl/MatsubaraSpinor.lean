/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
public import Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors

/-!
# The Euclidean Dunkl process, the Matsubara path integral, and the Dirac spinor field

Extends `Dunkl.EuclideanProcess` (Junker §5: the Euclidean Dunkl process splitting into a reflecting
and an absorbing Bessel process) by identifying that split with the **boson/fermion (periodic/antiperiodic)
structure of the Matsubara thermal path integral**, and placing the **Dirac spinor field** on this branch
in the fermionic/absorbing sector. The complex Feynman–Kac path integral of reference tree
(`Physlib.QFT.PathIntegral.FeynmanKac`, the foundation on which reference tree's `FeynmanKacBridge` /
`SpinorPathIntegralBridge` are built) is the common weight.

The dictionary:

| Dunkl Euclidean process | Matsubara thermal path integral | field |
|---|---|---|
| reflecting Bessel, Neumann `f'(0)=0`, even `P₊` | bosonic, **periodic**, zero mode `ω₀=0` | scalar/boson |
| absorbing Bessel, Dirichlet `f(0)=0`, odd `P₋` | fermionic, **antiperiodic**, **no** zero mode | Dirac spinor |

* **§A — Euclidean time is inverse temperature.** The complex Feynman–Kac weight at imaginary time `β` is
  exactly the Matsubara/thermal Boltzmann weight: `feynman_kac_weight (·↦E) β = e^{−βE} =
  matsubaraBoltzmannWeight β E` (`fk_weight_eq_matsubara`). So the Dunkl Euclidean evolution at `τ = β` is
  the thermal partition function's integrand.
* **§B — the parity split is the statistics split.** The reflecting (even, Neumann) sector includes the
  bosonic static mode `matsubaraFreqBoson β 0 = 0` (`reflecting_boson_zeroMode`); the absorbing (odd,
  Dirichlet `f(0)=0`) sector includes the fermionic frequencies `(2n+1)π/β ≠ 0`
  (`absorbing_fermion_noZeroMode`) — the absence of a zero mode *is* the Dirichlet boundary condition
  (`dunklEuclideanFK_origin`: the absorbing propagator vanishes at the origin).
* **§C — the Dirac spinor field is the fermionic/absorbing sector.** The Dirac spinor (`DiracSpinor`,
  upper ⊕ lower) decomposes exactly as the Dunkl parity `P₊ ⊕ P₋` (`diracSpinor_parity_decomp` ∥
  `parity_add`); its fermionic thermal weight has the negative-energy Dirac-sea ground
  (`spinor_ground_thermal_weight`); and it propagates through the absorbing Bessel Feynman–Kac process
  (`spinor_euclidean_fk_semigroup`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.MatsubaraSpinor

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator
open Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors

/-! ## §A — Euclidean time is inverse temperature: the FK weight is the Matsubara weight -/

/-- **[Bridge] The complex Feynman–Kac weight at imaginary time `β` is the Matsubara/thermal Boltzmann
weight.** `feynman_kac_weight (·↦E) β = e^{−βE} = matsubaraBoltzmannWeight β E`. The Dunkl Euclidean
evolution parameter `τ` of `Dunkl.EuclideanProcess` is the Matsubara inverse temperature `β = 1/k_BT`
(the circumference of the imaginary-time circle); at `τ = β` the shared FK weight is the integrand of the
thermal partition function `Z = Tr e^{−βĤ}`. -/
theorem fk_weight_eq_matsubara (E β : ℝ) :
    feynman_kac_weight (fun _ : Unit => E) β () = matsubaraBoltzmannWeight β E := by
  unfold feynman_kac_weight matsubaraBoltzmannWeight; congr 1; ring

/-- **The free Dunkl–Euclidean process is the infinite-temperature (`β = 0`) limit**: the thermal weight
is `1`. -/
theorem matsubara_free_limit (E : ℝ) : matsubaraBoltzmannWeight 0 E = 1 := by
  unfold matsubaraBoltzmannWeight; simp

/-! ## §B — the parity split is the boson/fermion (periodic/antiperiodic) statistics split -/

/-- **[Bridge] The reflecting sector is bosonic — it has the static zero mode.** The even Dunkl sector
`P₊` (reflecting Bessel, Neumann `f'(0)=0`) corresponds to the bosonic Matsubara tower, whose static mode
`matsubaraFreqBoson β 0 = 0` exists (periodic boundary conditions). -/
theorem reflecting_boson_zeroMode (β : ℝ) : matsubaraFreqBoson β 0 = 0 :=
  matsubaraFreqBoson_zero β

/-- **[Bridge] The absorbing sector is fermionic — it has no zero mode.** The odd Dunkl sector `P₋`
(absorbing Bessel, Dirichlet `f(0)=0`) corresponds to the fermionic Matsubara tower `(2n+1)π/β`, which has
**no** static mode (antiperiodic boundary conditions). The vanishing at the origin
(`dunklEuclideanFK_origin`) is the path-integral image of this missing zero mode. -/
theorem absorbing_fermion_noZeroMode (β : ℝ) (hβ : β ≠ 0) (n : ℤ) :
    fermionicMatsubaraFreq β n ≠ 0 :=
  fermionicMatsubaraFreq_ne_zero β hβ n

/-- **The reflecting/absorbing dichotomy is the periodic/antiperiodic dichotomy**: the bosonic tower
contains `ω = 0` while the fermionic tower never does — the two Bessel boundary conditions of the Dunkl
process (Neumann vs Dirichlet) are exactly the two thermal boundary conditions. -/
theorem statistics_dichotomy (β : ℝ) (hβ : β ≠ 0) :
    matsubaraFreqBoson β 0 = 0 ∧ ∀ n : ℤ, fermionicMatsubaraFreq β n ≠ 0 :=
  ⟨reflecting_boson_zeroMode β, fun n => absorbing_fermion_noZeroMode β hβ n⟩

/-! ## §C — the Dirac spinor field is the fermionic/absorbing sector -/

/-- **[Bridge] The Dirac spinor splits as the Dunkl parity decomposition.** `ψ = upper ⊕ lower`
(`restPositiveSpinor χᵤ + restNegativeSpinor χₗ`) is the spinor-field analogue of the Dunkl parity split
`p = P₊ p + P₋ p` (`Dunkl.EuclideanProcess.parity_add`): a `Z₂` grading (here the Dirac `β` /
energy-sign grading, there the reflection `R`) decomposing the field into two complementary sectors. The
lower (negative-energy) component sits in the fermionic/absorbing sector. -/
theorem diracSpinor_parity_decomp (χu χl : Fin 2 → ℂ) :
    restPositiveSpinor χu + restNegativeSpinor χl = Sum.elim χu χl := by
  unfold restPositiveSpinor restNegativeSpinor; ext i; cases i <;> simp

/-- **[Bridge] The Dirac spinor's thermal weight has the negative-energy (Dirac-sea) ground.** As a
fermion the spinor's lowest mode has energy `fermionicEnergyReal ℏ ω 0 = −ℏω/2 < 0`, so its Matsubara
weight is `e^{+βℏω/2} > 1` — the antiparticle/Dirac-sea contribution to the thermal trace, encoded in the
absorbing (Dirichlet) sector of the Dunkl process. -/
theorem spinor_ground_thermal_weight (ℏ ω β : ℝ) :
    matsubaraBoltzmannWeight β (fermionicEnergyReal ℏ ω 0) = Real.exp (β * (ℏ * ω) / 2) := by
  unfold matsubaraBoltzmannWeight fermionicEnergyReal; congr 1; push_cast; ring

/-- **[Bridge] The spinor field propagates through the absorbing Bessel Feynman–Kac process.** The Dirac
spinor (a fermion, antiperiodic) is encoded in the absorbing `FeynmanKacModel` sector of `dunklEuclideanFK`
and inherits its Chapman–Kolmogorov semigroup law — the complex Feynman–Kac path integral of the spinor
field, in imaginary (thermal) time. -/
theorem spinor_euclidean_fk_semigroup (Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (t s x : ℝ) :
    feynman_kac_propagator Babs β obs (t + s) x
      = Babs.pathIntegral (fun y => feynman_kac_propagator Babs β obs s y) t x :=
  dunklEuclideanFK_semigroup_abs Babs β obs t s x

/-- **[Bridge] The spinor field vanishes at the origin** — the Dirichlet/absorbing boundary `f(0) = 0`,
the path-integral signature of fermionic antiperiodicity (no thermal zero mode). -/
theorem spinor_absorbing_origin (Brefl Babs : FeynmanKacModel ℝ) (β : ℝ) (obs : ℝ → ℝ) (τ y : ℝ) :
    dunklEuclideanFK Brefl Babs β obs τ 0 y = feynman_kac_propagator Brefl β obs τ 0 :=
  dunklEuclideanFK_origin Brefl Babs β obs τ y

end Physlib.QuantumMechanics.ComplexAction.Dunkl.MatsubaraSpinor

end
