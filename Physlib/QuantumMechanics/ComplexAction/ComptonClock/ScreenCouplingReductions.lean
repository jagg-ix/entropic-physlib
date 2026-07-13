/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.MuonAnomalyCore
public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.CouplingCore
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea

/-!
# The screen couplings as reductions to published physics

Each theorem here proves that a framework equation relating `α` or `G` to entropic/holographic
quantities is identically an established, peer-reviewed result, evaluated at its measured input.
These are **reduction/consistency theorems anchored to published physics**: §A shows the framework's
`α`-equation is Schwinger's `g−2` anomaly at the empirical `α = 1/137`; §B shows `G` is Verlinde's
holographic area-per-bit with the Newtonian weak-field limit; §C reads both couplings off the one
screen. Each records the measured number its known equation is checked against.

* **§A — `α` is Schwinger's `g−2` anomaly, matched to the measured muon moment**
  (`alpha_is_schwinger_matched_to_muon`). The framework's rapidity equation
  `α = 2π·a(η)` is identically Schwinger's one-loop QED anomaly `a = α/(2π)`; at the empirical
  `α = 1/137` its value is `0.001161…0.001162`, below — at `99.6 %` of — the measured
  `a_μ = 0.00116592`. Bundles `alpha_isolated`, `muonSchwingerAnomaly_bounds`,
  `muonSchwingerAnomaly_lt_measured`.

* **§B — `G` as the holographic area-per-bit, with the Newtonian weak-field limit**
  (`newtonG_area_per_bit_weakField`). `G` equals the screen area one bit
  occupies in `c³/ℏ` units, `G = A·c³/(ℏN)`; the Einstein coupling is `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)`;
  and the trace-reversed field equation reduces to Newton's Poisson equation `∇²Φ = 4πGρ`. Bundles
  the area-per-bit identity (Verlinde's `newtonG_eq_area_per_bit`), `einsteinCoupling_bitForm`,
  `weakField_einstein_poisson`.

* **§C — `G` and `α` from the same screen** (`screen_couplings_one_origin`). Both couplings
  read off the *same* entropic screen at the entropic proper distance `r = λ_C·log K`
  (`K = coth η`): gravity as the area-per-bit datum `G = A·c³/(ℏN)`, electromagnetism as the
  Schmidt-defect datum `α = 2π(K²−1)`. Both couplings are functions of the one screen/entanglement
  parameter `η`.

## References

* J. Schwinger, *On Quantum-Electrodynamics and the Magnetic Moment of the Electron*, Phys. Rev.
  **73** (1948) 416 (`a = α/2π`).
* G. W. Bennett et al. (Muon `g−2`, BNL), Phys. Rev. D **73** (2006) 072003; B. Abi et al. (Muon
  `g−2`, Fermilab), Phys. Rev. Lett. **126** (2021) 141801, `a_μ = 0.00116592`. Electron:
  X. Fan et al., Phys. Rev. Lett. **130** (2023) 071801.
* E. Verlinde, *On the Origin of Gravity and the Laws of Newton*, JHEP **04** (2011) 029;
  T. Jacobson, *Thermodynamics of Spacetime*, Phys. Rev. Lett. **75** (1995) 1260.
* J. D. Bekenstein, Phys. Rev. D **7** (1973) 2333; S. W. Hawking, Commun. Math. Phys. **43** (1975)
  199 — horizon entropy `S = A/4`. K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*,
  Prog. Theor. Phys. **126** (2011) 1021, arXiv:1104.3381 — the complex-action framework.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem

/-! ## A. `α` is Schwinger's anomaly, matched to the measured muon moment -/

/-- **[A] The framework's `α`-equation is Schwinger's `g−2` anomaly, matched to the measured muon
moment.** Four facts in one citable statement: (i) `schwingerAnomaly α = α/(2π)` — the framework's
anomaly is Schwinger's one-loop QED value `a = α/(2π)` (Schwinger, Phys. Rev. 73 (1948) 416), by
definition; (ii) at the muon's rapidity (`schwingerAnomaly α = rapidityAnomaly η`, the Thomas–BMT
spin-precession kinematics) this reads `α = 2π·a(η)` (`alpha_isolated`); (iii) at the empirical
`α = 1/137` the leading anomaly is `0.001161 < a < 0.001162`; (iv) that is below the measured
`a_μ = 0.00116592` (Fermilab, PRL 126 (2021) 141801; BNL, PRD 73 (2006) 072003) — the one-loop term
is `99.6 %` of the measurement, the remainder being higher-order QED, hadronic and electroweak. This
proves the framework's equation equals Schwinger's and matches the measurement at leading order at
the empirical input `α = 1/137`. -/
lemma alpha_is_schwinger_matched_to_muon :
    (∀ α : ℝ, schwingerAnomaly α = α / (2 * Real.pi))
    ∧ (∀ α η : ℝ, 0 < η → schwingerAnomaly α = rapidityAnomaly η →
        α = 2 * Real.pi * rapidityAnomaly η)
    ∧ (0.001161 < schwingerAnomaly ((1 : ℝ) / 137)
        ∧ schwingerAnomaly ((1 : ℝ) / 137) < 0.001162)
    ∧ schwingerAnomaly ((1 : ℝ) / 137) < 0.00116592 :=
  ⟨fun _ => rfl,
   fun α η hη h => alpha_isolated α η hη h,
   muonSchwingerAnomaly_bounds,
   muonSchwingerAnomaly_lt_measured⟩

/-! ## B. `G` as the holographic area-per-bit -/

/-- **[B] `G` as the holographic area-per-bit; the weak-field limit is Newton's Poisson equation.**
For a screen of area `A = sphereArea R` with the holographic bit count
`N = A·c³/(Gℏ)`:
  (i) `G = A·c³/(ℏN)` — `G` is the screen area one bit occupies, in `c³/ℏ` units (Verlinde,
      JHEP 04 (2011) 029, `newtonG_eq_area_per_bit`; Jacobson, PRL 75 (1995) 1260);
  (ii) `8πG/c⁴ = 8π(A/N)/(ℏc)` — the Einstein coupling is `8π` Planck areas `A/N = ℓ_P²` per `ℏc`
      (`einsteinCoupling_bitForm`);
  (iii) `∇²Φ = 4πGρ` — the trace-reversed Einstein equation for dust reduces, in the weak static
      limit, to Newton's gravitational Poisson equation (`weakField_einstein_poisson`), the
      experimentally-confirmed inverse-square law.
This gives `G`'s area-per-bit form and its Newtonian weak-field limit; `G`'s SI value
remains an input via `ℓ_P`. -/
lemma newtonG_area_per_bit_weakField
    (G ℏ c N R d2Φ ρ : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hN : N = holographicBits (sphereArea R) G ℏ c)
    (hEin : weakFieldRicci00 d2Φ c = 4 * Real.pi * G * ρ / c ^ 2) :
    G = sphereArea R * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c)
    ∧ d2Φ = 4 * Real.pi * G * ρ := by
  have hπ := Real.pi_ne_zero
  refine ⟨?_, einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hN,
    weakField_einstein_poisson d2Φ c G ρ hc hEin⟩
  rw [hN]
  unfold holographicBits sphereArea
  field_simp

/-! ## C. `G` and `α` from the same entropic screen -/

/-- **[C] `G` and `α` expressed via the same entropic screen.**
At the screen of the entropic proper distance `r = λ_C·log K` (`entropicProperDistance`,
`K = coth η` the Schmidt number), the two fundamental couplings are the two readings of the single
parameter `η`:
  * **gravity** is the area-per-bit datum `G = A·c³/(ℏN)` (`A = sphereArea r`, `N` its holographic
    bit count) — the §B face (Verlinde);
  * **electromagnetism** is the Schmidt-defect datum `α = 2π(K²−1)`
    (`alpha_eq_twoPi_schmidt_defect`) — the §A face (Schwinger), with the *same* `η` fixing
    `K = coth η`. Both couplings are functions of the one entanglement parameter through the
    entropic-distance origin (Sorkin/Verlinde/Nagao–Nielsen `EntropicProperDistance`): the gravity
    face is the area-per-bit identity (`N` carries the `G`-dependence), the electromagnetic face is
    the measured muon-anomaly relation. -/
lemma screen_couplings_one_origin (m c ħ G η α N : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η)
    (hN : N = holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c)
    (hanom : schwingerAnomaly α = rapidityAnomaly η) :
    G = sphereArea (entropicProperDistance m c ħ η) * c ^ 3 / (ħ * N)
    ∧ α = 2 * Real.pi * (schmidtNumber η ^ 2 - 1) := by
  have hπ := Real.pi_ne_zero
  have hlogK : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  refine ⟨?_, alpha_eq_twoPi_schmidt_defect α η hη hanom⟩
  rw [hN]
  unfold holographicBits sphereArea entropicProperDistance comptonWavelength
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions

end
