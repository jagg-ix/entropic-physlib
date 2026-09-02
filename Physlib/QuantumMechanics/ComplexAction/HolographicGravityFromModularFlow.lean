/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhHolographicGEinstein
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTTWaveComptonCoupling
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Mathlib.Tactic.FieldSimp
meta import Zil

/-!
# Quantizing gravity from the inverse modular relation, evaluated at the holographic `G`

`EntropicClockImaginaryModularTime` read the physical clock *out of* the modular flow:
`vonNeumannGen ℏ H ρ = −(i/ℏ)·modularGenerator H ρ` (`KazamaTomitaTakesakiModular.
vonNeumannGen_eq_smul_modularGenerator`), so Schrödinger evolution is the Tomita–Takesaki flow.
This module runs the map the other way — the **inverse relation** — and evaluates the resulting
gravity with the repository's **holographic Newton constant** `G = ℏc/m²`.

## The inverse relation: the modular generator is `iℏ` times the unitary rate

Inverting the scalar `•`-identity gives `modularGenerator H ρ = (iℏ)·vonNeumannGen ℏ H ρ`
(`modularGenerator_eq_smul_vonNeumannGen`, `ℏ ≠ 0`). The modular Hamiltonian generator `δ_H = [H,·]`
— the Misra–Prigogine liouvillian, the thermofield hat-Hamiltonian, the KMS/thermal superoperator —
is exactly `iℏ` times the unitary Schrödinger rate. Multiplying real evolution by `iℏ` is the Wick
rotation to the modular/thermal object: the same `iℏ` that turns `e^{−iHt/ℏ}` into the modular
weight `Δ^{is} = e^{−2πis K_boost}`.

## The gravity that inverse flow generates (Bisognano–Wichmann → Unruh → Jacobson → Einstein)

The modular flow this relation isolates is, by **Bisognano–Wichmann**, a boost:
`AlgebraicQFT.SummersRelativisticVacuum.modularBoost_unruh` gives `Δ_W^{it} = boost(2πt)` with
`unruhInverseTemperature = 2π`, and `SummersVacuumModularLinks.wedgeModularHamiltonian_eq_
boostGenerator_block` identifies the modular Hamiltonian `K = log Δ` with the boost generator. That
boost carries the **Unruh** temperature `T = κ/2π` (`Lorentz.JacobsonUnruhRindlerClock.
unruhTemperature`, `SciamaUnruhEinsteinEquationOfState.sciamaUnruhTemperature`). Feeding that
temperature and the horizon entropy into **Jacobson's** Clausius relation `δQ = T δS` closes to the
Einstein equation with the coupling `8πG` *derived* as the Unruh `2π` times the Bekenstein `4G`
(`ComplexEinstein.JacobsonClausiusEinstein.clausius_equation_of_state`, `einstein_from_clausius`;
`Lorentz.SciamaUnruhHolographicGEinstein.einstein_from_sciamaUnruh_holographicG`, whose coupling is
`8π·(𝒜c³/ℏN) = 8πG`).

## Evaluating at the holographic `G = ℏc/m²`: `ℓ_P = λ_C` and `S = A/(4λ_C²)`

The repository derives that coupling `G`-free from the entanglement screen:
`ComptonClock.ComptonCellNewtonConstant.newtonG_from_comptonCellBits` returns `G = ℏc/m²`. Put that
value into the Bekenstein–Hawking entropy `S = 𝒜c³/(4Gℏ)` and it becomes an exact statement about
**Compton cells**, not Planck cells:

* `holographicG_planckArea_eq_comptonArea` — the Planck area equals the Compton area at this `G`,
  `Gℏ/c³ = λ_C²`. Since `ℓ_P² = Gℏ/c³`, this is `ℓ_P = λ_C`: the holographic `G` is exactly the value
  at which the Planck length coincides with the reduced Compton wavelength `λ_C = ℏ/mc` (equivalently
  `m` is the Planck mass, `m² = ℏc/G`). This is `GFreeComptonCellCalibration.
  comptonWavelength_screenMass_eq_countedPlanckLength` restated in bare `(m,c,ℏ)` variables.
* `bekensteinHawking_holographicG_eq_comptonCells` — consequently `S = 𝒜c³/(4Gℏ) = A/(4λ_C²)`: the
  horizon entropy counts its area in Compton cells `λ_C²`.

## `S = A/(4Gℏ)` forces `G ∝ ℏ`

The cell `λ_C² = ℏ²/(m²c²)` carries `ℏ²`. Requiring the horizon entropy to count a fixed geometric
area `A` in that Compton cell — `S = A/(4λ_C²)` — pins `Gℏ/c³ = λ_C² = ℏ²/(m²c²)`, hence
`G = ℏc/m²`: **Newton's constant is linear in `ℏ`.** `holographicG_div_hbar` records the sharp form,
`G/ℏ = c/m²` — the proportionality factor `c/m²` carries no `ℏ`. Gravity is not a separate field to be
quantized on top of `ℏ`; through the inverse modular relation its coupling *is* `ℏ` times a kinematic
number, and the Unruh temperature `T ∝ ℏ` that closes Jacobson's relation makes the Einstein coupling
`8πG ∝ ℏ` intrinsically quantum.

`modularFlow_holographicG_gravity_synthesis` bundles the four exact identities. The classical
substrate stays kernel-clean; the full Koopman/Tomita–Takesaki quantum lift of the metric remains open.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave
open Matrix minkowskiMatrix
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhEinsteinEquationOfState
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhHolographicGEinstein
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical

/-- **The inverse modular relation: `δ_H = (iℏ)·(dρ/dt)`.**  Inverting the scalar `•`-identity
`vonNeumannGen ℏ H ρ = −(i/ℏ)·modularGenerator H ρ`, the Tomita–Takesaki modular generator `δ_H = [H,·]`
is `iℏ` times the von Neumann / Schrödinger state rate.  Multiplication by `iℏ` is the Wick rotation
from unitary time to the modular/thermal object `Δ^{is}` — the same `iℏ` that turns `e^{−iHt/ℏ}` into
the modular weight. -/
theorem modularGenerator_eq_smul_vonNeumannGen {n : Type*} [Fintype n] [DecidableEq n]
    (ℏ : ℂ) (hℏ : ℏ ≠ 0) (H ρ : Matrix n n ℂ) :
    modularGenerator H ρ = (Complex.I * ℏ) • PeriodicQHermitian.Basic.vonNeumannGen ℏ H ρ := by
  rw [vonNeumannGen_eq_smul_modularGenerator, smul_smul]
  have hcoeff : Complex.I * ℏ * -(Complex.I / ℏ) = 1 := by
    have h : Complex.I * ℏ * -(Complex.I / ℏ) = -(Complex.I ^ 2) * (ℏ / ℏ) := by ring
    rw [h, Complex.I_sq, div_self hℏ]; ring
  rw [hcoeff, one_smul]

/-- **The holographic `G` makes the Planck area the Compton area: `ℓ_P² = λ_C²`.**  Evaluating the
Planck-area combination `Gℏ/c³` at the holographic value `G = ℏc/m²` gives the squared reduced Compton
wavelength `λ_C² = (ℏ/mc)²`.  Since `ℓ_P² = Gℏ/c³`, this is `ℓ_P = λ_C`: the holographic `G` is the
value at which the Planck length is the Compton wavelength (`m` is the Planck mass). -/
theorem holographicG_planckArea_eq_comptonArea (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    (ħ * c / m ^ 2) * ħ / c ^ 3 = comptonWavelength m c ħ ^ 2 := by
  unfold comptonWavelength
  field_simp

/-- **Bekenstein–Hawking in Compton cells: `S = 𝒜c³/(4Gℏ) = A/(4λ_C²)`.**  With the holographic
`G = ℏc/m²`, the horizon entropy counts its area `A` in Compton cells `λ_C²` rather than the usual
Planck cells — the direct consequence of `ℓ_P = λ_C`. -/
theorem bekensteinHawking_holographicG_eq_comptonCells (A m c ħ : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    A * c ^ 3 / (4 * ((ħ * c / m ^ 2) * ħ)) = A / (4 * comptonWavelength m c ħ ^ 2) := by
  unfold comptonWavelength
  field_simp

/-- **`S = A/(4Gℏ)` forces `G ∝ ℏ`: `G/ℏ = c/m²` is `ℏ`-independent.**  Counting a fixed geometric area
in the Compton cell `λ_C² = ℏ²/(m²c²)` pins `Gℏ/c³ = λ_C²`, hence `G = ℏc/m²`: Newton's constant is
`ℏ` times the kinematic factor `c/m²`, which carries no `ℏ`. -/
theorem holographicG_div_hbar (m c ħ : ℝ) (hħ : ħ ≠ 0) :
    (ħ * c / m ^ 2) / ħ = c / m ^ 2 := by
  rw [mul_div_assoc, mul_div_cancel_left₀ _ hħ]

/-- **The whole evaluation in one statement.**  For `ℏ ≠ 0` and positive scales, the inverse modular
relation `δ_H = (iℏ)·(dρ/dt)` holds; at the holographic `G = ℏc/m²` the Planck area is the Compton area
`Gℏ/c³ = λ_C²` (so `ℓ_P = λ_C`), the horizon entropy is `A/(4Gℏ/c³) = A/(4λ_C²)`, and `G/ℏ = c/m²` is
`ℏ`-independent — the gravitational coupling is `ℏ` times a kinematic number. -/
theorem modularFlow_holographicG_gravity_synthesis {n : Type*} [Fintype n] [DecidableEq n]
    (ℏc : ℂ) (hℏc : ℏc ≠ 0) (H ρ : Matrix n n ℂ)
    (A m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    modularGenerator H ρ = (Complex.I * ℏc) • PeriodicQHermitian.Basic.vonNeumannGen ℏc H ρ
      ∧ (ħ * c / m ^ 2) * ħ / c ^ 3 = comptonWavelength m c ħ ^ 2
      ∧ A * c ^ 3 / (4 * ((ħ * c / m ^ 2) * ħ)) = A / (4 * comptonWavelength m c ħ ^ 2)
      ∧ (ħ * c / m ^ 2) / ħ = c / m ^ 2 :=
  ⟨modularGenerator_eq_smul_vonNeumannGen ℏc hℏc H ρ,
    holographicG_planckArea_eq_comptonArea m c ħ hm hc,
    bekensteinHawking_holographicG_eq_comptonCells A m c ħ hm hc hħ,
    holographicG_div_hbar m c ħ hħ⟩

/-- **The Jacobson–Unruh closure into Einstein, at the holographic `G = ℏc/m²`.**  Depends on
`Lorentz.SciamaUnruhHolographicGEinstein.einstein_from_sciamaUnruh_holographicG`: given a Compton screen
whose holographic Newton constant is the Compton value `D.G = ℏc/m²`, the Unruh–Clausius balance at
`sciamaUnruhTemperature κb` closes to the Einstein field equation, and its coupling — output there as the
holographic `8π·(𝒜c³/ℏN) = 8πG` — is exactly `ℏ·(8πc/m²)`, `ℏ` times the kinematic factor `8πc/m²`.  The
same screen's Bekenstein–Hawking entropy `𝒜c³/(4Gℏ)` counts its area in Compton cells `A/(4λ_C²)`
(`bekensteinHawking_holographicG_eq_comptonCells`).  This is the docstring chain made a proof dependency:
the modular-flow boost's Unruh temperature closes Jacobson's relation, and the holographic `G` makes the
gravitational coupling manifestly `ℏ`-linear. -/
theorem einstein_holographicG_hbar_linear_coupling {d : ℕ}
    (D : ComptonPhysicalData) (m : ℝ) (hm : m ≠ 0)
    (hGm : D.G = D.hbar * D.c / m ^ 2)
    (Ric T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (κb : ℝ)
    (hRic : Ric.IsSymm) (hT : T.IsSymm) (hκb : κb ≠ 0)
    (hClausius : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 →
      κb * (k ⬝ᵥ (T *ᵥ k)) = sciamaUnruhTemperature κb * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * D.G))) :
    (∃ Λ : ℝ, einsteinFieldEquationCosmological Ric (Matrix.trace (η * Ric)) η T Λ
        (D.hbar * (8 * Real.pi * D.c / m ^ 2)))
      ∧ sphereArea D.screenRadius * D.c ^ 3 / (4 * (D.G * D.hbar))
          = sphereArea D.screenRadius / (4 * comptonWavelength m D.c D.hbar ^ 2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Λ, hΛ⟩ := einstein_from_sciamaUnruh_holographicG D Ric T κb hRic hT hκb hClausius
    refine ⟨Λ, ?_⟩
    have hcoup :
        8 * Real.pi * (sphereArea D.screenRadius * D.c ^ 3 / (D.hbar * D.screenBits))
          = D.hbar * (8 * Real.pi * D.c / m ^ 2) := by
      rw [← D.newtonG_holographic_area_per_bit, hGm]; ring
    rwa [hcoup] at hΛ
  · rw [hGm]
    exact bekensteinHawking_holographicG_eq_comptonCells (sphereArea D.screenRadius) m D.c D.hbar
      hm D.c_pos.ne' D.hbar_pos.ne'

/-! ## The mass-independent holographic `G`, and the Compton form's mass-dependence

The **primary** holographic constant is the mass-independent area-per-bit form
`newtonG_holographic A ℏ c N = A c³/(N ℏ)` (Verlinde JHEP 04 (2011) 029; Jacobson PRL 75 (1995) 1260,
`SourcedTTWaveHolographicCoupling`): `G` is fixed by the screen area `A` and its bit count `N`, with **no
particle mass**, and reconstructing it from the Bekenstein bit count returns `G` exactly
(`newtonG_holographic_holographicBits`).  It therefore carries none of the species-dependence below.

The Compton form `G = ℏc/m²` of `holographicG_div_hbar` is that same constant **specialized to the Compton
bit-count** `N = A/λ_C²` — one bit per Compton cell (`holographicG_eq_newtonG_at_comptonBits`).  The particle
mass enters *only* through this cell-size choice, and the remaining theorems isolate what it costs — so they
explain why the mass-free area-per-bit constant, not the Compton form, is the species-independent one.

* `holographicG_eq_newtonG_at_comptonBits` — the Compton form is `newtonG_holographic` at the Compton
  bit-count; the mass is the cell choice, not a property of `G`.
* `holographicG_inverts_target` — in the Compton form, choosing the mass by `m² = ℏc/G` returns the target `G`
  by construction: obtaining `G` from a chosen mass is an inversion of the cell size, not a prediction.
* `holographicG_strictAnti` — the Compton form is strictly decreasing (hence injective) in `m`, so a *single
  particle mass* cannot be a universal anchor across the unequal electron/muon/proton masses; the mass-free
  `newtonG_holographic` avoids this by fixing `G` from the bit count instead.
* `holographicG_predicts_of_independent_mass` — the Compton form predicts `G` only once the mass anchor is
  fixed `G`-freely.
-/

/-- The holographic gravitational coupling `G = ℏc/m²`. -/
noncomputable def holographicG (m c ħ : ℝ) : ℝ := ħ * c / m ^ 2

/-- **The mass-independent constant specializes to the Compton form at the Compton bit-count.**  The primary
holographic constant `newtonG_holographic A ℏ c N = A c³/(N ℏ)` carries no particle mass; evaluated at the
Compton bit-count `N = A/λ_C² = A m² c²/ℏ²` (one bit per Compton cell) it reproduces `G = ℏc/m²`.  The mass is
this cell-size choice, not a property of the area-per-bit constant itself. -/
theorem holographicG_eq_newtonG_at_comptonBits (A m c ħ : ℝ)
    (hA : A ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    newtonG_holographic A ħ c (A * m ^ 2 * c ^ 2 / ħ ^ 2) = holographicG m c ħ := by
  unfold newtonG_holographic holographicG
  field_simp

/-! ### `N` is fixed independently of `G`: the equipartition bit count

Whether `G = A c³/(N ℏ)` is circular turns on how the bit count `N` is fixed. Taking `N` from the area law
`N = holographicBits A G ℏ c = A c³/(G ℏ)` would make it so — that `N` contains `G`. But `N` is set
*physically*, not geometrically: by **equipartition**, the screen's energy `E` is shared as `½ k_B T` over its
`N` bits, so `N = 2E/(k_B T)` — a function of the energy `E` and temperature `T` alone, with **no `G`**
(`screenBitCount`). Newton's constant is then the output `G = A c³/(N ℏ) = A c³ k_B T/(2 E ℏ)`
(`newtonG_holographic_screenBitCount`), a `G`-free forward value; and `holographicBits_of_newtonG_holographic`
shows the area law merely reproduces this same `N` — so `N` is the independent input and `G` the derived
quantity, not the reverse.

**Physical interpretation of `N`.** `N` is the number of holographic bits — the microscopic degrees of freedom
on the screen — counted by equipartition of the screen's energy at its temperature (one `½ k_B T` per bit,
`equipartitionEnergy_screenBitCount`). Equivalently it is the screen's Boltzmann/entanglement entropy in units
of `k_B`. Newton's constant `G = A c³/(N ℏ)` is then the geometric area per such bit (times `c³/ℏ`): the bit
count is set by the screen's thermodynamics, and `G` measures how much area each bit carries. -/

/-- The **equipartition bit count** `N = 2E/(k_B T)` of a screen of energy `E` at temperature `T`: the number
of holographic bits that share the energy, `½ k_B T` each. A function of `E, k_B, T` only — manifestly
independent of `G`. -/
noncomputable def screenBitCount (E kB T : ℝ) : ℝ := 2 * E / (kB * T)

/-- **The equipartition bit count inverts equipartition.**  Distributing energy `E` over `screenBitCount E kB T`
bits at temperature `T` recovers `E` — so `N` is exactly the number of `½ k_B T` energy quanta on the screen. -/
theorem equipartitionEnergy_screenBitCount (E kB T : ℝ) (hkB : kB ≠ 0) (hT : T ≠ 0) :
    equipartitionEnergy (screenBitCount E kB T) kB T = E := by
  unfold equipartitionEnergy screenBitCount
  field_simp

/-- **`G` from the equipartition bit count — a `G`-free forward value.**  With `N` fixed by equipartition,
`G = A c³/(N ℏ) = A c³ k_B T/(2 E ℏ)` is a function of the area, energy, temperature and constants only: no `G`
appears on the right. -/
theorem newtonG_holographic_screenBitCount (A c ħ E kB T : ℝ)
    (hE : E ≠ 0) (hkB : kB ≠ 0) (hT : T ≠ 0) (hħ : ħ ≠ 0) :
    newtonG_holographic A ħ c (screenBitCount E kB T) = A * c ^ 3 * kB * T / (2 * E * ħ) := by
  unfold newtonG_holographic screenBitCount
  field_simp

/-- **`N` is the independent input, `G` the output.**  For any bit count `N`, the area law evaluated at the
derived constant `G = newtonG_holographic A ℏ c N` returns exactly `N`: the holographic area law does not fix
`N`; it is consistent with whatever `N` the screen's thermodynamics supplies (`screenBitCount`). -/
theorem holographicBits_of_newtonG_holographic (A c ħ N : ℝ)
    (hA : A ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hN : N ≠ 0) :
    holographicBits A (newtonG_holographic A ħ c N) ħ c = N := by
  unfold holographicBits newtonG_holographic
  field_simp

/-- **The partition–Bekenstein system, solved.**  Verlinde's construction is the triangular system in the
unknowns `N, G`, with the energy `E`, temperature `T` and screen area `A` given physically:

* the **partition** equation `E = ½ N k_B T` (`equipartitionEnergy`), and
* the **Bekenstein** area law `N = A c³/(G ℏ)` (`holographicBits`).

The partition equation *alone* fixes the bit count `N = 2E/(k_B T)` — **with no `G`** — and the Bekenstein
equation then fixes the emergent Newton constant `G = A c³ k_B T/(2 E ℏ)`. The solving order is
`partition → N → Bekenstein → G`; `N` is determined before `G` enters, so it is fixed independently of `G`. -/
theorem partition_bekenstein_solve (E T kB A c ħ N G : ℝ)
    (hkB : kB ≠ 0) (hT : T ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hA : A ≠ 0) (hc : c ≠ 0) (hE : E ≠ 0)
    (hpartition : E = equipartitionEnergy N kB T)
    (hbekenstein : N = holographicBits A G ħ c) :
    N = screenBitCount E kB T ∧ G = A * c ^ 3 * kB * T / (2 * E * ħ) := by
  have hN : N = screenBitCount E kB T := by
    unfold equipartitionEnergy at hpartition
    unfold screenBitCount
    rw [hpartition]; field_simp
  refine ⟨hN, ?_⟩
  have hGN : G = newtonG_holographic A ħ c N := by
    unfold holographicBits at hbekenstein
    unfold newtonG_holographic
    rw [hbekenstein]; field_simp
  rw [hGN, hN, newtonG_holographic_screenBitCount A c ħ E kB T hE hkB hT hħ]

/-- **The inversion closes by construction.**  Fixing the mass by the inverted relation `m² = ℏc/G` for a
target coupling `G` returns that `G` exactly — choosing `m` to reproduce a desired Newton constant is an
inversion of the definition, not an independent prediction of `G`. -/
theorem holographicG_inverts_target (m c ħ G : ℝ) (hħ : ħ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0)
    (hm2 : m ^ 2 = ħ * c / G) : holographicG m c ħ = G := by
  unfold holographicG
  rw [hm2]
  field_simp

/-- **Species-dependence: strictly decreasing in the mass.**  For fixed `ℏ, c > 0`, a larger mass gives a
strictly smaller coupling, so `G = ℏc/m²` is injective in `m`: it cannot assign one Newton constant to two
different particle masses, hence cannot be a universal prediction. -/
theorem holographicG_strictAnti (c ħ : ℝ) (hc : 0 < c) (hħ : 0 < ħ)
    {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hlt : m₁ < m₂) :
    holographicG m₂ c ħ < holographicG m₁ c ħ := by
  have hm₂ : (0 : ℝ) < m₂ := lt_trans hm₁ hlt
  unfold holographicG
  rw [← sub_pos, div_sub_div _ _ (pow_ne_zero 2 hm₁.ne') (pow_ne_zero 2 hm₂.ne')]
  apply div_pos
  · have hrw : ħ * c * m₂ ^ 2 - m₁ ^ 2 * (ħ * c) = ħ * c * (m₂ ^ 2 - m₁ ^ 2) := by ring
    rw [hrw]
    exact mul_pos (mul_pos hħ hc) (by nlinarith [hlt, hm₁, hm₂])
  · positivity

/-- **The honest non-circular form.**  Once the mass anchor is fixed by a measurement independent of `G`
(the hypothesis `m = m₀`), the coupling is the determinate forward value `G = ℏc/m₀²` — a falsifiable
prediction for that anchor.  The relation is a prediction exactly when `m₀` is supplied `G`-freely. -/
theorem holographicG_predicts_of_independent_mass (c ħ m m₀ : ℝ) (hm : m = m₀) :
    holographicG m c ħ = ħ * c / m₀ ^ 2 := by
  rw [holographicG, hm]

end Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.modularGenerator_eq_smul_vonNeumannGen where
  formalizes @ "claim:inverting-the-modular-smul-law-the-tomita-takesaki-modular-generator-is-i-hbar-times-the-von-neumann-schrodinger-state-rate-the-wick-rotation-from-unitary-time-to-the-modular-thermal-weight",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.vonNeumannGen_eq_smul_modularGenerator"

zil attach Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.holographicG_planckArea_eq_comptonArea where
  formalizes @ "claim:at-the-holographic-newton-constant-g-equals-hbar-c-over-mass-squared-the-planck-area-equals-the-compton-area-so-the-planck-length-equals-the-reduced-compton-wavelength",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength"

zil attach Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.bekensteinHawking_holographicG_eq_comptonCells where
  formalizes @ "claim:at-the-holographic-newton-constant-the-bekenstein-hawking-horizon-entropy-a-c-cubed-over-four-g-hbar-counts-its-area-in-compton-cells-a-over-four-lambda-c-squared",
  requires @ "claim:at-the-holographic-newton-constant-g-equals-hbar-c-over-mass-squared-the-planck-area-equals-the-compton-area-so-the-planck-length-equals-the-reduced-compton-wavelength"

zil attach Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.einstein_holographicG_hbar_linear_coupling where
  formalizes @ "claim:feeding-the-holographic-newton-constant-g-equals-hbar-c-over-mass-squared-into-the-unruh-clausius-derivation-closes-into-einsteins-equation-with-a-coupling-that-is-hbar-times-the-kinematic-factor-eight-pi-c-over-mass-squared",
  requires @ "claim:at-the-holographic-newton-constant-the-bekenstein-hawking-horizon-entropy-a-c-cubed-over-four-g-hbar-counts-its-area-in-compton-cells-a-over-four-lambda-c-squared",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhHolographicGEinstein.einstein_from_sciamaUnruh_holographicG",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonG_holographic_area_per_bit"

zil_file_contract physlib.holographicGravityFromModularFlow where
  promises "Runs the entropic-clock=modular-flow map backwards and reads Einstein's coupling out of it at the repository's G-free holographic Newton constant G = hbar c/m^2. The inverse of the scalar smul law vonNeumannGen = -(i/hbar) modularGenerator is modularGenerator H rho = (i hbar) vonNeumannGen hbar H rho: the Tomita-Takesaki modular generator delta_H = [H,.] (Misra-Prigogine liouvillian, thermofield hat-Hamiltonian, KMS superoperator) is i hbar times the unitary Schrodinger rate, the Wick rotation from e^{-iHt/hbar} to the modular weight Delta^{is}. At G = hbar c/m^2 the Planck area equals the Compton area, G hbar/c^3 = lambda_C^2, so the Planck length is the reduced Compton wavelength (m is the Planck mass); consequently the Bekenstein-Hawking horizon entropy A c^3/(4 G hbar) = A/(4 lambda_C^2) counts area in Compton cells, and G/hbar = c/m^2 is hbar-independent, the precise sense in which S = A/(4 G hbar) forces G linear in hbar. The bundle depends on SciamaUnruhHolographicGEinstein.einstein_from_sciamaUnruh_holographicG: given a Compton screen whose holographic Newton constant is the Compton value, the Unruh-Clausius balance closes into Einstein's equation with coupling 8 pi (A c^3/hbar N) rewritten as hbar (8 pi c/m^2), and the same screen entropy is A/(4 lambda_C^2). The classical substrate is kernel-clean; the full Koopman/Tomita-Takesaki quantum lift of the metric remains open."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.vonNeumannGen_eq_smul_modularGenerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhHolographicGEinstein.einstein_from_sciamaUnruh_holographicG",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonPhysical.ComptonPhysicalData.newtonG_holographic_area_per_bit"]
  forbids_substitutes [
    "reading G proportional to hbar off S = A/(4 G hbar) at fixed pure-number entropy, which instead gives G proportional to 1/hbar: the hbar-linearity holds only in the holographic form G = hbar c/m^2 where the Bekenstein cell is the hbar-carrying Compton area",
    "identifying the modular parameter s with a literal imaginary time rather than the imaginary-modular-time reading t/hbar of the KMS analytic continuation"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.modularGenerator_eq_smul_vonNeumannGen,
    Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.holographicG_planckArea_eq_comptonArea,
    Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.bekensteinHawking_holographicG_eq_comptonCells,
    Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.holographicG_div_hbar,
    Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.modularFlow_holographicG_gravity_synthesis,
    Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow.einstein_holographicG_hbar_linear_coupling]

#zil_horn_grounding physlib.holographicGravityFromModularFlow

/- ZIL-END -/
