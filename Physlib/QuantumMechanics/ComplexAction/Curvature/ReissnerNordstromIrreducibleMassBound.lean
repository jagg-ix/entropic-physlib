/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea
public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSurfaceGravity

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula -/

/-!
# The Christodoulou–Ruffini mass formula for Reissner–Nordström

The irreducible mass of a Reissner–Nordström black hole is `M_irr = r_+/2` (so `𝒜 = 16π M_irr²`), and
the Christodoulou–Ruffini formula decomposes the total mass into its irreducible part and the
electromagnetic contribution:

`M = M_irr + Q²/(4 M_irr)`.

Equivalently `2M = r_+ + Q²/r_+`, which follows from the horizon product `r_+ r_- = Q²` and sum
`r_+ + r_- = 2M`.  The `Q²/(4 M_irr)` term is the reducible (extractable) electromagnetic energy — the
basis of the Penrose/Christodoulou energy-extraction bound.

* `irreducibleMass` — `M_irr = r_+/2`.
* `christodoulou_horizon_relation` — `r_+ + Q²/r_+ = 2M`.
* `christodoulou_mass_formula` — `M = M_irr + Q²/(4 M_irr)`.
* `irreducibleMass_extremal` — at extremality `M² = Q²` the irreducible mass is `M/2`.

Honest scope: this is the mass/charge/horizon algebra; the identification of `Q²/(4 M_irr)` with the
extractable energy via a physical process is not carried here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons

/-- **The irreducible mass** `M_irr = r_+/2` of a Reissner–Nordström black hole. -/
def irreducibleMass (M Q : ℝ) : ℝ := outerHorizon M Q / 2

/-- **The horizon form of the mass relation** `r_+ + Q²/r_+ = 2M` — from `r_+ r_- = Q²` and
`r_+ + r_- = 2M`. -/
@[zil_level physical_theorem]
theorem christodoulou_horizon_relation (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) (hr : outerHorizon M Q ≠ 0) :
    outerHorizon M Q + Q ^ 2 / outerHorizon M Q = 2 * M := by
  rw [← horizon_product M Q h, ← horizon_sum M Q]
  field_simp

/-- **The Christodoulou–Ruffini mass formula** `M = M_irr + Q²/(4 M_irr)`: the total mass is the
irreducible mass plus the reducible electromagnetic energy. -/
@[zil_level physical_theorem]
theorem christodoulou_mass_formula (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) (hr : outerHorizon M Q ≠ 0) :
    M = irreducibleMass M Q + Q ^ 2 / (4 * irreducibleMass M Q) := by
  have hrel := christodoulou_horizon_relation M Q h hr
  rw [irreducibleMass]
  have hcombine : outerHorizon M Q / 2 + Q ^ 2 / (4 * (outerHorizon M Q / 2))
      = (outerHorizon M Q + Q ^ 2 / outerHorizon M Q) / 2 := by ring
  rw [hcombine, hrel]
  ring

/-- **At extremality the irreducible mass is `M/2`** (`M² = Q² ⇒ r_+ = M`). -/
@[zil_level physical_theorem]
theorem irreducibleMass_extremal (M Q : ℝ) (h : M ^ 2 = Q ^ 2) :
    irreducibleMass M Q = M / 2 := by
  rw [irreducibleMass, (extremal_horizons_eq M Q h).1]

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula

zil attach christodoulou_horizon_relation where
  supported_by @ "lean:horizon_product",
  formalizes @ "claim:the-reissner-nordstrom-horizon-mass-relation-r-plus-plus-q-squared-over-r-plus-equals-two-m-from-the-horizon-product-and-sum"

zil attach christodoulou_mass_formula where
  formalizes @ "claim:the-christodoulou-ruffini-mass-formula-m-equals-the-irreducible-mass-plus-q-squared-over-four-times-the-irreducible-mass-decomposing-the-total-mass-into-irreducible-and-reducible-electromagnetic-parts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_horizon_relation"

zil attach irreducibleMass_extremal where
  supported_by @ "lean:extremal_horizons_eq",
  formalizes @ "claim:at-extremality-m-squared-equals-q-squared-the-reissner-nordstrom-irreducible-mass-is-m-over-two"

zil_file_contract physlib.reissnerNordstromMassFormula where
  promises "The Christodoulou-Ruffini mass formula for Reissner-Nordstrom black holes. The irreducible mass is the outer horizon radius over two. The horizon form of the mass relation, the outer horizon radius plus Q squared over the outer horizon radius equals twice the mass, follows from the horizon product r plus times r minus equals Q squared and the horizon sum r plus plus r minus equals twice the mass. The Christodoulou-Ruffini formula then decomposes the total mass as the irreducible mass plus Q squared over four times the irreducible mass, the reducible electromagnetic energy. At extremality M squared equals Q squared the irreducible mass is M over two. Honest scope: this is the mass, charge, and horizon algebra; the identification of the reducible term with the extractable energy via a physical process is not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.outerHorizon",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.horizon_product",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.horizon_sum"
  ]
  forbids_substitutes [
    "reading the mass-charge-horizon algebra as an identification of the reducible term with the extractable energy via a concrete physical extraction process"
  ]
  witnessed_by [
    christodoulou_horizon_relation,
    christodoulou_mass_formula,
    irreducibleMass_extremal
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromMassFormula

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound -/

/-!
# The Christodoulou irreducibility bound and Penrose energy extraction

The Christodoulou–Ruffini mass formula `M = M_irr + Q²/(4 M_irr)` (`christodoulou_mass_formula`) splits
the total mass into the irreducible mass `M_irr = r_+/2` and the reducible electromagnetic energy
`Q²/(4 M_irr)`.  Since the reducible term is non-negative, the irreducible mass is a **lower bound** on
the total mass — it cannot be reduced by any classical process — and the difference `M − M_irr` is the
maximum extractable (Penrose) energy.

* `irreducibleMass_pos` — `M_irr > 0` for `M > 0`.
* `extractableEnergy_nonneg` — the reducible energy `Q²/(4 M_irr) ≥ 0`.
* `mass_ge_irreducibleMass` — `M_irr ≤ M` (the irreducibility bound).
* `mass_eq_irreducibleMass_iff_uncharged` — `M = M_irr ⇔ Q = 0`: the mass is irreducible exactly when
  the black hole is uncharged.

Honest scope: this is the algebraic energy bound from the mass formula; the dynamical Penrose process
that saturates it is not modelled here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula

/-- **The maximum extractable (Penrose) energy** `E_ext = Q²/(4 M_irr) = M − M_irr`. -/
def extractableEnergy (M Q : ℝ) : ℝ := Q ^ 2 / (4 * irreducibleMass M Q)

/-- **The irreducible mass is positive** `M_irr = r_+/2 > 0` for `M > 0`. -/
theorem irreducibleMass_pos (M Q : ℝ) (hM : 0 < M) : 0 < irreducibleMass M Q := by
  rw [irreducibleMass]
  unfold outerHorizon
  have hs : (0 : ℝ) ≤ Real.sqrt (M ^ 2 - Q ^ 2) := Real.sqrt_nonneg _
  linarith

/-- **The extractable energy is non-negative** `Q²/(4 M_irr) ≥ 0` (for `M > 0`). -/
@[zil_level physical_theorem]
theorem extractableEnergy_nonneg (M Q : ℝ) (hM : 0 < M) : 0 ≤ extractableEnergy M Q := by
  rw [extractableEnergy]
  have hpos := irreducibleMass_pos M Q hM
  positivity

/-- **The irreducibility bound** `M_irr ≤ M`: the irreducible mass is a lower bound on the total mass. -/
@[zil_level physical_theorem]
theorem mass_ge_irreducibleMass (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) (hM : 0 < M)
    (hr : outerHorizon M Q ≠ 0) :
    irreducibleMass M Q ≤ M := by
  have hform := christodoulou_mass_formula M Q h hr
  have hext := extractableEnergy_nonneg M Q hM
  rw [extractableEnergy] at hext
  linarith

/-- **The mass is irreducible exactly for an uncharged black hole** `M = M_irr ⇔ Q = 0`. -/
@[zil_level physical_theorem]
theorem mass_eq_irreducibleMass_iff_uncharged (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) (hM : 0 < M)
    (hr : outerHorizon M Q ≠ 0) :
    M = irreducibleMass M Q ↔ Q = 0 := by
  have hform := christodoulou_mass_formula M Q h hr
  have hpos := irreducibleMass_pos M Q hM
  constructor
  · intro hEq
    have hden : (4 : ℝ) * irreducibleMass M Q ≠ 0 := by positivity
    have hz : Q ^ 2 / (4 * irreducibleMass M Q) = 0 := by linarith
    have hQ2 : Q ^ 2 = 0 := by rwa [div_eq_zero_iff, or_iff_left hden] at hz
    exact pow_eq_zero_iff (by norm_num) |>.mp hQ2
  · intro hQ
    subst hQ
    simpa using hform

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound

zil attach extractableEnergy_nonneg where
  formalizes @ "claim:the-reissner-nordstrom-extractable-penrose-energy-q-squared-over-four-times-the-irreducible-mass-is-non-negative"

zil attach mass_ge_irreducibleMass where
  formalizes @ "claim:the-christodoulou-irreducibility-bound-the-irreducible-mass-is-a-lower-bound-on-the-total-reissner-nordstrom-mass-so-the-mass-cannot-be-reduced-below-the-irreducible-mass",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_mass_formula"

zil attach mass_eq_irreducibleMass_iff_uncharged where
  supported_by @ "lean:christodoulou_mass_formula",
  formalizes @ "claim:the-reissner-nordstrom-mass-is-irreducible-equal-to-the-irreducible-mass-exactly-when-the-black-hole-is-uncharged"

zil_file_contract physlib.reissnerNordstromIrreducibleMassBound where
  promises "The Christodoulou irreducibility bound and Penrose energy extraction for Reissner-Nordstrom black holes, from the Christodoulou-Ruffini mass formula. The maximum extractable Penrose energy is Q squared over four times the irreducible mass, equal to the total mass minus the irreducible mass, and is non-negative. The irreducible mass is a lower bound on the total mass, the irreducibility bound: the mass cannot be reduced below the irreducible mass by any classical process. The mass is irreducible, equal to the irreducible mass, exactly when the black hole is uncharged. Honest scope: this is the algebraic energy bound from the mass formula; the dynamical Penrose process that saturates it is not modelled here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.irreducibleMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_mass_formula"
  ]
  forbids_substitutes [
    "reading the algebraic irreducibility bound as a dynamical model of the Penrose energy-extraction process that saturates it"
  ]
  witnessed_by [
    extractableEnergy_nonneg,
    mass_ge_irreducibleMass,
    mass_eq_irreducibleMass_iff_uncharged
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromIrreducibleMassBound

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula -/

/-!
# The Reissner–Nordström Smarr formula: connecting surface gravity, area, and charge

The three Reissner–Nordström thermodynamic sectors — surface gravity `κ` (`ReissnerNordstromSurfaceGravity`),
horizon area `𝒜` (`ReissnerNordstromEntropyArea`), and mass/charge (`ReissnerNordstromMassFormula`) — are
tied together by the **Smarr formula**

`M = κ 𝒜 / (4π) + Φ_H Q`,

where `Φ_H = Q/r_+` is the electric potential at the horizon.  The geometric term collapses to
`κ 𝒜/(4π) = r_+ − M = √(M² − Q²)`, and the identity is then equivalent to the horizon mass relation
`r_+ + Q²/r_+ = 2M`.  The repository had a Schwarzschild Smarr relation on the entropic-time carrier but
no charged (`Φ_H Q`) generalization joining the three charged-horizon quantities.

* `horizonPotential` — `Φ_H = Q/r_+`.
* `smarrGeometricTerm_eq` — `κ 𝒜/(4π) = r_+ − M`.
* `rn_smarr_formula` — `κ 𝒜/(4π) + Φ_H Q = M`.

Honest scope: this is the static (integral) Smarr identity connecting the algebraic thermodynamic
quantities; the differential first law `dM = (κ/8π) d𝒜 + Φ_H dQ` as a genuine variation is not carried
here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSurfaceGravity
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula

/-- **The electric potential at the outer horizon** `Φ_H = Q/r_+`. -/
def horizonPotential (M Q : ℝ) : ℝ := Q / outerHorizon M Q

/-- **The horizon potential vanishes at zero charge** `Φ_H = 0`. -/
theorem horizonPotential_uncharged (M : ℝ) : horizonPotential M 0 = 0 := by
  simp [horizonPotential]

/-- **The Smarr geometric term** `κ 𝒜/(4π) = r_+ − M` (`= √(M² − Q²)`) — the surface gravity times the
horizon area is the extremality gap. -/
@[zil_level physical_theorem]
theorem smarrGeometricTerm_eq (M Q : ℝ) (hr : outerHorizon M Q ≠ 0) :
    rnSurfaceGravity M Q * rnHorizonArea M Q / (4 * Real.pi) = outerHorizon M Q - M := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr2 : outerHorizon M Q ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [rnSurfaceGravity_eq, rnHorizonArea,
    show outerHorizon M Q - M = Real.sqrt (M ^ 2 - Q ^ 2) from by unfold outerHorizon; ring]
  field_simp

/-- **The Reissner–Nordström Smarr formula** `M = κ 𝒜/(4π) + Φ_H Q` — connecting the surface gravity,
horizon area and electric charge/potential of the three thermodynamic sectors into the total mass. -/
@[zil_level bridge_theorem]
theorem rn_smarr_formula (M Q : ℝ) (h : Q ^ 2 ≤ M ^ 2) (hr : outerHorizon M Q ≠ 0) :
    rnSurfaceGravity M Q * rnHorizonArea M Q / (4 * Real.pi) + horizonPotential M Q * Q = M := by
  have hrel := christodoulou_horizon_relation M Q h hr
  rw [smarrGeometricTerm_eq M Q hr, horizonPotential, div_mul_eq_mul_div, ← pow_two]
  linarith [hrel]

end Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula

zil attach smarrGeometricTerm_eq where
  supported_by @ "lean:rnSurfaceGravity_eq",
  formalizes @ "claim:the-reissner-nordstrom-smarr-geometric-term-surface-gravity-times-horizon-area-over-four-pi-equals-the-outer-horizon-radius-minus-the-mass-the-extremality-gap"

zil attach rn_smarr_formula where
  formalizes @ "claim:the-reissner-nordstrom-smarr-formula-the-total-mass-equals-surface-gravity-times-horizon-area-over-four-pi-plus-the-horizon-electric-potential-times-charge-connecting-the-three-thermodynamic-sectors",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_horizon_relation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula.smarrGeometricTerm_eq"

zil_file_contract physlib.reissnerNordstromSmarrFormula where
  promises "The Reissner-Nordstrom Smarr formula, connecting the three charged-horizon thermodynamic sectors of surface gravity, horizon area, and mass/charge. The electric potential at the outer horizon is the charge over the outer horizon radius. The Smarr geometric term, the surface gravity times the horizon area over four pi, equals the outer horizon radius minus the mass, the extremality gap. The Smarr formula then states that the total mass equals the surface gravity times the horizon area over four pi plus the horizon electric potential times the charge, connecting the surface gravity, horizon area, and electric charge into the total mass; it is equivalent to the horizon mass relation. Honest scope: this is the static integral Smarr identity connecting the algebraic thermodynamic quantities; the differential first law as a genuine variation is not carried here."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSurfaceGravity.rnSurfaceGravity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromEntropyArea.rnHorizonArea",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_horizon_relation"
  ]
  forbids_substitutes [
    "reading the static integral Smarr identity as the differential first law of black-hole thermodynamics proved as a genuine variation"
  ]
  witnessed_by [
    smarrGeometricTerm_eq,
    rn_smarr_formula
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.reissnerNordstromSmarrFormula

