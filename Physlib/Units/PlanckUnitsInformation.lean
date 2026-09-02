/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.GravitationalCouplingDimensions

/-!
# Planck units under the information axis: the half-bit grading

`GravitationalCouplingDimensions` forced two typings on the gravitational system: the
holographic bit count carries `[N] = I𝓭`, and consistently `[G]` absorbs `I𝓭⁻¹`
(`holographicBits_forces_newton_perBit`). This module runs the **Planck units** through
both readings.

## §A — SI reading: all Planck units are pure … except the temperature

With the SI `[G] = L³M⁻¹T⁻²`, the Planck combinations land exactly on the base axes
(`siPlanck_units_pure`): `[Gℏ/c³] = L²`, `[√(Gℏ/c³)] = L`, `[√(Gℏ/c⁵)] = T`,
`[√(ℏc/G)] = M`, `[√(ℏc⁵/G)] = E`. The single exception is the **Planck temperature**
(`planckTemperature_carries_bit`): `T_P = E_P/k_B` with the framework Landauer
`[k_B] = E·Θ⁻¹·I𝓭⁻¹` gives `[E_P/k_B] = Θ·I𝓭` — one nat rides along *before any
holographic typing*, because dividing by `k_B` converts energy-per-nat, not energy.

## §B — informed reading: the Planck area is area-per-bit, and lengths carry half bits

Substituting the forced `[G] = L³M⁻¹T⁻²·I𝓭⁻¹` (`informedNewton_dim`):

* `informedPlanckArea_eq` — `[ℓ_P²] = L²·I𝓭⁻¹`: the Planck area is **one area per
  bit**, so the Verlinde count is typed exactly, `[A/ℓ_P²] = I𝓭`
  (`holographicCount_isBits`).
* `bekensteinHawking_forces_informedPlanckArea` — the *iff*: the Bekenstein–Hawking
  entropy `S = k_B·A/(4ℓ_P²)` is a Clausius entropy `E·Θ⁻¹` **iff** the Planck area
  carries `L²·I𝓭⁻¹`. The BH formula itself forces the informed typing.
* the **half-bit grading** — the linear Planck units acquire *half-integer* information
  exponents (the rational-exponent group supports them):
  `[ℓ_P] = L·I𝓭^(−1/2)`, `[t_P] = T·I𝓭^(−1/2)`, `[m_P] = M·I𝓭^(+1/2)`,
  `[E_P] = E·I𝓭^(+1/2)`, `[T_P] = Θ·I𝓭^(3/2)`.

## §C — why entropy counts area, and where the half-bits cancel

* `planckLength_information_not_integer` — the Planck length's information exponent is
  `−1/2`, **not an integer**: no whole number of bits corresponds to one Planck length.
  The Planck *area* is the smallest Planck carrier with integral information (`−1`) —
  the dimensional reason holographic entropy counts area, not length.
* `planckPairs_infoFree` — the `G`-free pairings cancel the half-bits exactly:
  `ℓ_P·m_P = ℏ/c`, `E_P·t_P = ℏ`, `ℓ_P/t_P = c` — pure mechanical dimensions, zero
  information. The information content of the Planck system lives entirely in `G`; any
  combination reducible to `ℏ` and `c` is information-free.
* `halfBit_invisible_in_SI` — `forgetInfo` sends `L·I𝓭^(−1/2)` to `L`: the 5-base SI
  projection cannot distinguish the informed Planck length from a pure length — the
  half-bit grading is a collision in SI, visible only on the `[I]` axis.

## References

* Carriers: `Units.GravitationalCouplingDimensions` (forced typings, dimension vectors),
  `Units.InformationDimensionCollision` (`forgetInfo`, `boltzmann_dim`,
  `thermoEntropy_dim`, `action_dim`), `Units.Dimension` (rational-exponent group).
* M. Planck, *Über irreversible Strahlungsvorgänge* (1899) — the natural units.
* J. D. Bekenstein (1973), S. W. Hawking (1975) — `S = k_B·A/(4ℓ_P²)`.
-/

set_option autoImplicit false

open Dimension.LTMCTI Physlib.Units.InformationDimensionCollision
open Physlib.Units.GravitationalCouplingDimensions

@[expose] public section

namespace Physlib.Units.PlanckUnitsInformation

/-! ## §A — SI reading -/

/-- **In the SI reading every quadratic-and-square-root Planck combination is pure**:
`[Gℏ/c³] = L²` (area), `[√(Gℏ/c³)] = L` (length), `[√(Gℏ/c⁵)] = T` (time),
`[√(ℏc/G)] = M` (mass), `[√(ℏc⁵/G)] = E` (energy). -/
theorem siPlanck_units_pure :
    newtonConstant_dim * action_dim * velocity_dim ^ (-3 : ℚ) = area_dim
    ∧ (newtonConstant_dim * action_dim * velocity_dim ^ (-3 : ℚ)) ^ ((1 : ℚ)/2) = L𝓭
    ∧ (newtonConstant_dim * action_dim * velocity_dim ^ (-5 : ℚ)) ^ ((1 : ℚ)/2) = T𝓭
    ∧ (action_dim * velocity_dim * newtonConstant_dim⁻¹) ^ ((1 : ℚ)/2) = M𝓭
    ∧ (action_dim * velocity_dim ^ (5 : ℚ) * newtonConstant_dim⁻¹) ^ ((1 : ℚ)/2)
        = energy_dim :=
  ⟨by ext b <;> cases b <;> norm_num [newtonConstant_dim, action_dim, velocity_dim, area_dim],
   by ext b <;> cases b <;> norm_num [newtonConstant_dim, action_dim, velocity_dim],
   by ext b <;> cases b <;> norm_num [newtonConstant_dim, action_dim, velocity_dim],
   by ext b <;> cases b <;> norm_num [newtonConstant_dim, action_dim, velocity_dim],
   by ext b <;> cases b <;> norm_num [newtonConstant_dim, action_dim, velocity_dim, energy_dim]⟩

/-- **The Planck temperature carries one nat even in the SI reading**:
`[E_P/k_B] = Θ·I𝓭` — dividing by the Landauer `k_B` (energy per temperature *per nat*)
leaves the information unit exposed. `T_P` is the temperature at which one nat costs one
Planck energy, and its dimension says so. -/
theorem planckTemperature_carries_bit :
    energy_dim * boltzmann_dim⁻¹ = Θ𝓭 * I𝓭 := by
  ext b <;> cases b <;> norm_num [boltzmann_dim, energy_dim]

/-! ## §B — informed reading: area-per-bit and the half-bit grading -/

/-- Newton's constant with the holographically forced typing
`[G] = L³·M⁻¹·T⁻²·I𝓭⁻¹` (`holographicBits_forces_newton_perBit`). -/
def informedNewton_dim : Dimension LTMCTIDimensionBase := newtonConstant_dim * I𝓭⁻¹

/-- The informed Planck area `[Gℏ/c³]` at `[G] = informedNewton_dim`. -/
def informedPlanckArea_dim : Dimension LTMCTIDimensionBase :=
  informedNewton_dim * action_dim * velocity_dim ^ (-3 : ℚ)

/-- The informed Planck length `[√(Gℏ/c³)]`. -/
def informedPlanckLength_dim : Dimension LTMCTIDimensionBase := informedPlanckArea_dim ^ ((1 : ℚ)/2)

/-- The informed Planck time `[√(Gℏ/c⁵)]`. -/
def informedPlanckTime_dim : Dimension LTMCTIDimensionBase :=
  (informedNewton_dim * action_dim * velocity_dim ^ (-5 : ℚ)) ^ ((1 : ℚ)/2)

/-- The informed Planck mass `[√(ℏc/G)]`. -/
def informedPlanckMass_dim : Dimension LTMCTIDimensionBase :=
  (action_dim * velocity_dim * informedNewton_dim⁻¹) ^ ((1 : ℚ)/2)

/-- The informed Planck energy `[√(ℏc⁵/G)]`. -/
def informedPlanckEnergy_dim : Dimension LTMCTIDimensionBase :=
  (action_dim * velocity_dim ^ (5 : ℚ) * informedNewton_dim⁻¹) ^ ((1 : ℚ)/2)

/-- The informed Planck temperature `[√(ℏc⁵/G)/k_B]`. -/
def informedPlanckTemperature_dim : Dimension LTMCTIDimensionBase :=
  informedPlanckEnergy_dim * boltzmann_dim⁻¹

/-- **The informed Planck area is one area per bit**: `[ℓ_P²] = L²·I𝓭⁻¹`. -/
theorem informedPlanckArea_eq :
    informedPlanckArea_dim = area_dim * I𝓭⁻¹ := by
  ext b <;> cases b <;> norm_num [informedPlanckArea_dim, informedNewton_dim, newtonConstant_dim,
    action_dim, velocity_dim, area_dim]

/-- **The holographic count is exactly a bit count**: `[A/ℓ_P²] = I𝓭` — the Verlinde
`N = A·c³/(Gℏ)` typed through the informed Planck area. -/
theorem holographicCount_isBits :
    area_dim / informedPlanckArea_dim = I𝓭 := by
  rw [informedPlanckArea_eq]
  ext b <;> cases b <;> norm_num [area_dim]

/-- **The Bekenstein–Hawking formula forces the informed Planck area.** The entropy
`S = k_B·A/(4ℓ_P²)` is a Clausius entropy `E·Θ⁻¹` **iff** `[ℓ_P²] = L²·I𝓭⁻¹`: black
hole thermodynamics is dimensionally consistent exactly when the Planck area is
area-per-bit. -/
theorem bekensteinHawking_forces_informedPlanckArea (a : Dimension LTMCTIDimensionBase) :
    boltzmann_dim * (area_dim * a⁻¹) = thermoEntropy_dim ↔
      a = informedPlanckArea_dim := by
  rw [informedPlanckArea_eq]
  have key : boltzmann_dim * (area_dim * (area_dim * I𝓭⁻¹)⁻¹) = thermoEntropy_dim := by
    ext b <;> cases b <;> norm_num [boltzmann_dim, area_dim, thermoEntropy_dim, energy_dim]
  refine ⟨fun h => ?_, fun h => by rw [h]; exact key⟩
  exact inv_injective (mul_left_cancel (mul_left_cancel (h.trans key.symm)))

/-- **The half-bit grading of the linear Planck units**: `[ℓ_P] = L·I𝓭^(−1/2)`,
`[t_P] = T·I𝓭^(−1/2)`, `[m_P] = M·I𝓭^(1/2)`, `[E_P] = E·I𝓭^(1/2)`,
`[T_P] = Θ·I𝓭^(3/2)` — under the informed typing, every linear Planck unit carries a
half-integer information exponent. -/
theorem informedPlanck_halfBit_grading :
    informedPlanckLength_dim = L𝓭 * I𝓭 ^ (-(1 : ℚ)/2)
    ∧ informedPlanckTime_dim = T𝓭 * I𝓭 ^ (-(1 : ℚ)/2)
    ∧ informedPlanckMass_dim = M𝓭 * I𝓭 ^ ((1 : ℚ)/2)
    ∧ informedPlanckEnergy_dim = energy_dim * I𝓭 ^ ((1 : ℚ)/2)
    ∧ informedPlanckTemperature_dim = Θ𝓭 * I𝓭 ^ ((3 : ℚ)/2) :=
  ⟨by ext b <;> cases b <;> norm_num [informedPlanckLength_dim, informedPlanckArea_dim,
      informedNewton_dim, newtonConstant_dim, action_dim, velocity_dim],
   by ext b <;> cases b <;> norm_num [informedPlanckTime_dim, informedNewton_dim,
      newtonConstant_dim, action_dim, velocity_dim],
   by ext b <;> cases b <;> norm_num [informedPlanckMass_dim, informedNewton_dim,
      newtonConstant_dim, action_dim, velocity_dim],
   by ext b <;> cases b <;> norm_num [informedPlanckEnergy_dim, informedNewton_dim,
      newtonConstant_dim, action_dim, velocity_dim, energy_dim],
   by ext b <;> cases b <;> norm_num [informedPlanckTemperature_dim, informedPlanckEnergy_dim,
      informedNewton_dim, newtonConstant_dim, action_dim, velocity_dim,
      boltzmann_dim, energy_dim]⟩

/-! ## §C — integrality, cancellation, invisibility -/

/-- **No whole number of bits corresponds to one Planck length**: the informed Planck
length's information exponent is `−1/2`, not an integer. The Planck *area* has integral
exponent `−1` (`informedPlanckArea_eq`) — so area is the smallest Planck carrier of
whole bits, the dimensional reason holographic entropy counts area rather than
length. -/
theorem planckLength_information_not_integer :
    ¬ ∃ n : ℤ, (n : ℚ) = informedPlanckLength_dim.exponent .information := by
  rintro ⟨n, hn⟩
  have h : informedPlanckLength_dim.exponent .information = -(1/2 : ℚ) := by
    norm_num [informedPlanckLength_dim, informedPlanckArea_dim, informedNewton_dim,
      newtonConstant_dim, action_dim, velocity_dim]
  rw [h] at hn
  have h2 : (2 * n : ℤ) = -1 := by exact_mod_cast (by linarith : (2 : ℚ) * n = -1)
  omega

/-- **The `G`-free Planck pairings are information-free**: `ℓ_P·m_P = ℏ/c`,
`E_P·t_P = ℏ`, `ℓ_P/t_P = c` — the half-bits cancel exactly in every combination that
eliminates `G`. The information content of the Planck system lives entirely in Newton's
constant. -/
theorem planckPairs_infoFree :
    informedPlanckLength_dim * informedPlanckMass_dim = action_dim * velocity_dim⁻¹
    ∧ informedPlanckEnergy_dim * informedPlanckTime_dim = action_dim
    ∧ informedPlanckLength_dim / informedPlanckTime_dim = velocity_dim :=
  ⟨by ext b <;> cases b <;> norm_num [informedPlanckLength_dim, informedPlanckArea_dim,
      informedPlanckMass_dim, informedNewton_dim, newtonConstant_dim, action_dim,
      velocity_dim],
   by ext b <;> cases b <;> norm_num [informedPlanckEnergy_dim, informedPlanckTime_dim,
      informedNewton_dim, newtonConstant_dim, action_dim, velocity_dim, energy_dim],
   by ext b <;> cases b <;> norm_num [informedPlanckLength_dim, informedPlanckArea_dim,
      informedPlanckTime_dim, informedNewton_dim, newtonConstant_dim, action_dim,
      velocity_dim]⟩

/-- **The half-bit is invisible in SI**: `forgetInfo` collapses the informed Planck
length onto the pure length `L`, yet the two dimensions are distinct — the
`InformationDimensionCollision` mechanism at exponent `−1/2`. -/
theorem halfBit_invisible_in_SI :
    forgetInfo informedPlanckLength_dim = forgetInfo L𝓭
      ∧ informedPlanckLength_dim ≠ L𝓭 := by
  refine collision_of_info_differ ?_ ?_
  · ext b <;> cases b <;> norm_num [informedPlanckLength_dim, informedPlanckArea_dim,
      informedNewton_dim, newtonConstant_dim, action_dim, velocity_dim]
  · norm_num [informedPlanckLength_dim, informedPlanckArea_dim, informedNewton_dim,
      newtonConstant_dim, action_dim, velocity_dim]

/-! ## §D — the fine-structure isolation, dimensionally

The isolation equations of `EntanglementScreenArea` §J and `ScaleDilationLogMetric` §K checked
in the dimension group, in *both* systems. Classically: `α` and `α_G` are dimensionless, the
squared Planck charge is pure `C²` and the squared Planck mass pure `M²`, and the isolation
`α = (e/m)²(log K)²/(ε₀GN)` is dimensionless with `N` a pure number. In the *informed* system
the bookkeeping is sharper: Newton's constant carries `I⁻¹` (`informedNewton_dim`) and the
holographic count carries `I` (`holographicCount_isBits`), the informed Planck mass² picks up a
*bit* (`informedPlanckMassSq_carries_bit` — the half-bit grading of the mass rung), and the
isolation stays exactly dimensionless because the information axis cancels *between `G` and
`N`* (`alphaIsolation_informed_dimensionless`) — the dimensional reason the two always appear
together in the screen equations. -/

/-- **The vacuum permittivity dimension** `[ε₀] = C²·T²·M⁻¹·L⁻³` (from Coulomb's law). -/
def vacuumPermittivity_dim : Dimension LTMCTIDimensionBase :=
  C𝓭 ^ (2 : ℚ) * T𝓭 ^ (2 : ℚ) * M𝓭⁻¹ * L𝓭 ^ (-3 : ℚ)

/-- **[The squared Planck charge is pure charge]** `[4πε₀ℏc] = C²` — the denominator of the
fine-structure constant carries exactly the dimension of `e²`. -/
theorem planckChargeSq_dim :
    vacuumPermittivity_dim * action_dim * velocity_dim = C𝓭 ^ (2 : ℚ) := by
  ext b <;> cases b <;> norm_num [vacuumPermittivity_dim, action_dim, velocity_dim]

/-- **[`α` is dimensionless]** `[e²/(4πε₀ℏc)] = 1`. -/
theorem fineStructure_dimensionless :
    C𝓭 ^ (2 : ℚ) / (vacuumPermittivity_dim * action_dim * velocity_dim) = 1 := by
  ext b <;> cases b <;> norm_num [vacuumPermittivity_dim, action_dim, velocity_dim]

/-- **[The squared Planck mass is pure mass]** `[ℏc/G] = M²`. -/
theorem planckMassSq_dim :
    action_dim * velocity_dim / newtonConstant_dim = M𝓭 ^ (2 : ℚ) := by
  ext b <;> cases b <;> norm_num [action_dim, velocity_dim, newtonConstant_dim]

/-- **[`α_G` is dimensionless]** `[Gm²/(ℏc)] = 1`. -/
theorem gravitationalCoupling_dimensionless :
    newtonConstant_dim * M𝓭 ^ (2 : ℚ) / (action_dim * velocity_dim) = 1 := by
  ext b <;> cases b <;> norm_num [action_dim, velocity_dim, newtonConstant_dim]

/-- **[The classical isolation is dimensionless]** `[(e/m)²/(ε₀·G)] = 1` — with `log K` and the
classical bit count pure numbers, the isolation equation balances with no residue. -/
theorem alphaIsolation_dimensionless :
    (C𝓭 / M𝓭) ^ (2 : ℚ) / (vacuumPermittivity_dim * newtonConstant_dim) = 1 := by
  ext b <;> cases b <;> norm_num [vacuumPermittivity_dim, newtonConstant_dim]

/-- **[The informed Planck mass² carries a bit]** `[ℏc/G_informed] = M²·I` — in the
information-graded system the mass rung of the Planck ladder is not pure mass: it absorbs one
bit, the square of the half-bit grading of `informedPlanckMass_dim`. -/
theorem informedPlanckMassSq_carries_bit :
    action_dim * velocity_dim * informedNewton_dim⁻¹ = M𝓭 ^ (2 : ℚ) * I𝓭 := by
  ext b <;> cases b <;> norm_num [action_dim, velocity_dim, informedNewton_dim, newtonConstant_dim]

/-- **[The informed isolation is dimensionless]** `[(e/m)²/(ε₀·G_informed·N_bits)] = 1` — with
`[G] = …·I⁻¹` and `[N] = I` (`holographicCount_isBits`), the information axis cancels exactly
between Newton's constant and the bit count: the isolation equation is consistent in the
informed system precisely because `G` and `N` enter as the pair `G·N`. -/
theorem alphaIsolation_informed_dimensionless :
    (C𝓭 / M𝓭) ^ (2 : ℚ) / (vacuumPermittivity_dim * informedNewton_dim * I𝓭) = 1 := by
  ext b <;> cases b <;> norm_num [vacuumPermittivity_dim, informedNewton_dim, newtonConstant_dim]

/-! ## §E — the length ladder, dimensionally

The `ScaleDilationLogMetric` §K ladder route `α = exp(−d(ƛ_C, a₀))` checked in the dimension
group. Each rung is a pure length from its *independent* defining expression — Compton
`ℏ/(mc)`, Bohr `4πε₀ℏ²/(me²)`, Thomson `e²/(4πε₀mc²)` — so the `scaleDistance` argument
`ƛ_C/a₀` is dimensionless (`ladderRatio_dimensionless`) and the `log`/`exp` of the metric route
is licit; numerically that ratio *is* `e²/(4πε₀ℏc)`, the same combination as
`fineStructure_dimensionless`. The geometric-mean midpoint `a₀·r_e = ƛ_C²` already holds at the
level of dimensions, with the charge and permittivity axes cancelling between the outer rungs
exactly as `α` cancels numerically (`ladderMidpoint_dim`). -/

/-- **[The Compton wavelength is a length]** `[ℏ/(mc)] = L`. -/
theorem comptonWavelength_dim : action_dim / (M𝓭 * velocity_dim) = L𝓭 := by
  ext b <;> cases b <;> norm_num [action_dim, velocity_dim]

/-- **[The Bohr radius is a length]** `[4πε₀ℏ²/(me²)] = L` — from the Coulomb-form defining
expression, independent of the Compton rung. -/
theorem bohrRadius_dim :
    vacuumPermittivity_dim * action_dim ^ (2 : ℚ) / (M𝓭 * C𝓭 ^ (2 : ℚ)) = L𝓭 := by
  ext b <;> cases b <;> norm_num [vacuumPermittivity_dim, action_dim]

/-- **[The Thomson radius is a length]** `[e²/(4πε₀mc²)] = L`. -/
theorem thomsonRadius_dim :
    C𝓭 ^ (2 : ℚ) / (vacuumPermittivity_dim * M𝓭 * velocity_dim ^ (2 : ℚ)) = L𝓭 := by
  ext b <;> cases b <;> norm_num [vacuumPermittivity_dim, velocity_dim]

/-- **[The geometric-mean midpoint holds dimensionally]** `[a₀]·[r_e] = [ℏ/(mc)]²` — the charge
and permittivity axes cancel between the outer rungs of the ladder, the dimensional shadow of
the `α`-cancellation in `compton_geometric_mean_of_ladder`. -/
theorem ladderMidpoint_dim :
    vacuumPermittivity_dim * action_dim ^ (2 : ℚ) / (M𝓭 * C𝓭 ^ (2 : ℚ))
        * (C𝓭 ^ (2 : ℚ) / (vacuumPermittivity_dim * M𝓭 * velocity_dim ^ (2 : ℚ)))
      = (action_dim / (M𝓭 * velocity_dim)) ^ (2 : ℚ) := by
  rw [bohrRadius_dim, thomsonRadius_dim, comptonWavelength_dim]
  ext b <;> cases b <;> norm_num

/-- **[The ladder ratio is a pure number]** `[ƛ_C/a₀] = 1` — the `scaleDistance` argument of
`alpha_isolated_from_ladder` is dimensionless, licensing the `log`/`exp` of the metric route. -/
theorem ladderRatio_dimensionless :
    action_dim / (M𝓭 * velocity_dim)
        / (vacuumPermittivity_dim * action_dim ^ (2 : ℚ) / (M𝓭 * C𝓭 ^ (2 : ℚ))) = 1 := by
  rw [comptonWavelength_dim, bohrRadius_dim]
  ext b <;> cases b <;> norm_num

end Physlib.Units.PlanckUnitsInformation

end
