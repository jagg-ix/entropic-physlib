/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.DensityParameters
public import Physlib.Cosmology.FLRW.MatterContent
public import Physlib.Relativity.SemiClassical.SelfGravitatingRadiationEntropy

/-!
# The density-sector welds

Pairwise welds among the homogeneous density carriers — `criticalDensity` (`3H²/8πG`),
`vacuumEnergyDensity` (`Λc²/8πG`), the black-body `energyDensity` (`bT⁴`) and
`radiationPressure` (`ρ/3`).  `#zil_groupoid_report` found the four mutually homogeneous
(with `entropyDensity` exactly one temperature unit off every edge) but almost disconnected:
only the radiation trio's internal relations were proven, and the two `G`-carrying
cosmological densities were isolated vertices — not even connected to each other.  The six
welds below close every edge of the quadrilateral; each names a cosmological condition:
exact de Sitter (`3H² = Λc²`), the radiation-dominated Friedmann temperature–Hubble
relation (`8πGbT⁴ = 3H²`), and the radiation–vacuum equality temperature
(`8πGbT⁴ = Λc²`).  Guarded by `Physlib.Meta.DensitySectorGate`.
-/

@[expose] public section

namespace Cosmology.FLRW.DensitySectorWelds

open Cosmology.FLRW.DensityParameters
open Cosmology.FLRW.MatterContent
open Physlib.Relativity.SemiClassical.SelfGravitatingRadiation

/-- **The critical density equals the vacuum energy density exactly at `3H² = Λc²`** — the
exact de Sitter relation: a universe whose expansion is entirely carried by `Λ`.  Both
carriers divide by the same `8πG`, so the weld is `G`-free content despite two `G`-carrying
sides — the two holographic densities sit on the same information rung. -/
theorem criticalDensity_eq_vacuumEnergyDensity_iff {H G Λ c : ℝ} (hG : 0 < G) :
    criticalDensity H G = vacuumEnergyDensity Λ G c ↔ 3 * H ^ 2 = Λ * c ^ 2 := by
  unfold criticalDensity vacuumEnergyDensity
  exact div_left_inj' (by positivity)

/-- **Black-body radiation is critical exactly at `8πGbT⁴ = 3H²`** — the flat
radiation-dominated Friedmann equation as a rest-point weld: the early-universe
temperature–Hubble dictionary `H² = (8πG/3)·bT⁴`. -/
theorem energyDensity_eq_criticalDensity_iff {b T H G : ℝ} (hG : 0 < G) :
    energyDensity b T = criticalDensity H G ↔ 8 * Real.pi * G * (b * T ^ 4) = 3 * H ^ 2 := by
  unfold energyDensity criticalDensity
  rw [eq_div_iff (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- **Black-body radiation matches the vacuum energy density exactly at `8πGbT⁴ = Λc²`** —
the radiation–vacuum equality temperature, the moment a cooling radiation bath hands the
universe over to `Λ`. -/
theorem energyDensity_eq_vacuumEnergyDensity_iff {b T Λ G c : ℝ} (hG : 0 < G) :
    energyDensity b T = vacuumEnergyDensity Λ G c
      ↔ 8 * Real.pi * G * (b * T ^ 4) = Λ * c ^ 2 := by
  unfold energyDensity vacuumEnergyDensity
  rw [eq_div_iff (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- **The radiation pressure of density `ρ` is critical exactly at `8πGρ = 9H²`** — the
density three times critical, since radiation pays only a third of its density as
pressure. -/
theorem radiationPressure_eq_criticalDensity_iff {ρ H G : ℝ} (hG : 0 < G) :
    radiationPressure ρ = criticalDensity H G ↔ 8 * Real.pi * G * ρ = 9 * H ^ 2 := by
  unfold radiationPressure criticalDensity
  rw [div_eq_div_iff (by norm_num) (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- **The radiation pressure of `ρ` reaches the black-body energy density exactly at
`ρ = 3bT⁴`** — the equation of state `P = ρ/3` read as a rest-point weld against the
carrier itself. -/
theorem radiationPressure_eq_energyDensity_iff {ρ b T : ℝ} :
    radiationPressure ρ = energyDensity b T ↔ ρ = 3 * (b * T ^ 4) := by
  unfold radiationPressure energyDensity
  rw [div_eq_iff (by norm_num : (3:ℝ) ≠ 0)]
  constructor <;> intro h <;> linear_combination h

/-- **The radiation pressure matches the vacuum energy density exactly at `8πGρ = 3Λc²`.** -/
theorem radiationPressure_eq_vacuumEnergyDensity_iff {ρ Λ G c : ℝ} (hG : 0 < G) :
    radiationPressure ρ = vacuumEnergyDensity Λ G c
      ↔ 8 * Real.pi * G * ρ = 3 * (Λ * c ^ 2) := by
  unfold radiationPressure vacuumEnergyDensity
  rw [div_eq_div_iff (by norm_num) (by positivity)]
  constructor <;> intro h <;> linear_combination h

end Cosmology.FLRW.DensitySectorWelds
