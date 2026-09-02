/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.LTMCTIDimensionBase
public import Mathlib.Tactic.NormNum

/-!
# Forgetting the information dimension forces a collision

The dimension of a physical quantity is an element of the free abelian group on the
base axes; "a collision" is two *distinct* dimensions that become *equal* — the
dimension map failing to be injective. This file proves that **dropping the
information axis `[I]` is a quotient with non-trivial kernel**, so collisions are
guaranteed:

* `forgetInfo` zeros the information component (the 6-base → 5-base SI projection); it
  is a homomorphism (`forgetInfo_mul`, `forgetInfo_one`) but **not injective**
  (`forgetInfo_not_injective`).
* `shannon_collides_dimensionless` — its kernel already contains `I𝓭`: Shannon
  entropy `I` and a pure dimensionless number become the same dimension.
* `boltzmann_collides_thermoEntropy` — the physically relevant collision: without
  `[I]`, the **Boltzmann constant** `k_B = E·Θ⁻¹·I⁻¹` and **thermodynamic entropy**
  `E·Θ⁻¹` are indistinguishable. That is exactly the Brillouin/Landauer point, now as
  a forced collision: any theory containing a quantity with an information dimension collapses
  it onto an information-free one the moment `[I]` is dropped.
* `collision_of_info_differ` — the general criterion: any two dimensions agreeing off
  the information axis but differing on it collide under `forgetInfo`.

## The collisions `[I]` does *not* resolve (your examples)

Adding `[I]` is **necessary** for the information collision but **not sufficient** to
make dimension injective. Collisions that are information-free survive in *both* the
5- and 6-base structures — they are orthogonal to `[I]`:

* `action_eq_angularMomentum` — action and angular momentum are both `M·L²·T⁻¹`.
* `torque_eq_energy` — torque and energy are both `M·L²·T⁻²`.

These are *geometric* collisions (a scalar vs a pseudovector, etc.): dimensional
analysis tracks only the `{M,L,T,…}` scaling, not tensor character, so no base axis
separates them. The information axis fixes precisely one identification — information
vs dimensionless — and leaves these untouched.

References: Brillouin (1956); Landauer (1961).
-/

set_option autoImplicit false

open Dimension.LTMCTI

@[expose] public section

namespace Physlib.Units.InformationDimensionCollision

/-- **The 6-base → 5-base projection**: forget the information exponent. -/
def forgetInfo (d : Dimension LTMCTIDimensionBase) : Dimension LTMCTIDimensionBase :=
  ofLTMCTI (d.exponent .length) (d.exponent .time) (d.exponent .mass)
    (d.exponent .charge) (d.exponent .temperature) 0

@[simp] lemma forgetInfo_length (d : Dimension LTMCTIDimensionBase) : (forgetInfo d).exponent .length = d.exponent .length := rfl
@[simp] lemma forgetInfo_time (d : Dimension LTMCTIDimensionBase) : (forgetInfo d).exponent .time = d.exponent .time := rfl
@[simp] lemma forgetInfo_mass (d : Dimension LTMCTIDimensionBase) : (forgetInfo d).exponent .mass = d.exponent .mass := rfl
@[simp] lemma forgetInfo_charge (d : Dimension LTMCTIDimensionBase) : (forgetInfo d).exponent .charge = d.exponent .charge := rfl
@[simp] lemma forgetInfo_temperature (d : Dimension LTMCTIDimensionBase) :
    (forgetInfo d).exponent .temperature = d.exponent .temperature := rfl
@[simp] lemma forgetInfo_information (d : Dimension LTMCTIDimensionBase) : (forgetInfo d).exponent .information = 0 := rfl

/-- `forgetInfo` is multiplicative (a group homomorphism on dimensions). -/
lemma forgetInfo_mul (d e : Dimension LTMCTIDimensionBase) :
    forgetInfo (d * e) = forgetInfo d * forgetInfo e := by ext b <;> cases b <;> simp [forgetInfo]

lemma forgetInfo_one : forgetInfo 1 = 1 := by ext b <;> cases b <;> simp [forgetInfo]

/-! ## The guaranteed collision: `forgetInfo` is not injective -/

lemma forgetInfo_I𝓭 : forgetInfo I𝓭 = 1 := by ext b <;> cases b <;> simp [forgetInfo]

lemma I𝓭_ne_one : (I𝓭 : Dimension LTMCTIDimensionBase) ≠ 1 := by
  intro h; have := congrArg (fun d => d.exponent .information) h; simp at this

/-- **Shannon entropy collides with a dimensionless number.** `I𝓭` is a non-trivial
element of the kernel of `forgetInfo`: forgetting `[I]`, one bit of information and a
pure number are the same dimension. -/
lemma shannon_collides_dimensionless :
    forgetInfo I𝓭 = forgetInfo (1 : Dimension LTMCTIDimensionBase) ∧ I𝓭 ≠ (1 : Dimension LTMCTIDimensionBase) :=
  ⟨by rw [forgetInfo_I𝓭, forgetInfo_one], I𝓭_ne_one⟩

/-- **Forgetting `[I]` is not injective** — collisions are guaranteed. -/
lemma forgetInfo_not_injective : ¬ Function.Injective forgetInfo := fun hinj =>
  I𝓭_ne_one (hinj (by rw [forgetInfo_I𝓭, forgetInfo_one]))

/-! ## The physically relevant collision: `k_B` vs thermodynamic entropy -/

/-- Energy dimension `E = M·L²·T⁻²`. -/
def energy_dim : Dimension LTMCTIDimensionBase := M𝓭 * L𝓭 ^ (2 : ℚ) * T𝓭 ^ (-2 : ℚ)

/-- Framework Boltzmann constant `[k_B] = E·Θ⁻¹·I⁻¹`. -/
def boltzmann_dim : Dimension LTMCTIDimensionBase := energy_dim * Θ𝓭⁻¹ * I𝓭⁻¹

/-- Thermodynamic (Clausius) entropy `[S] = E·Θ⁻¹`. -/
def thermoEntropy_dim : Dimension LTMCTIDimensionBase := energy_dim * Θ𝓭⁻¹

/-- **Without `[I]`, the Boltzmann constant and thermodynamic entropy collide.** They
agree off the information axis (`forgetInfo k_B = forgetInfo S = E·Θ⁻¹`) but are
distinct dimensions (`k_B` has `I⁻¹`, `S` does not). So the 5-base SI structure
*cannot* tell `k_B` from an entropy — the Brillouin/Landauer collision, forced. -/
lemma boltzmann_collides_thermoEntropy :
    forgetInfo boltzmann_dim = forgetInfo thermoEntropy_dim ∧
      boltzmann_dim ≠ thermoEntropy_dim := by
  refine ⟨by ext b <;> cases b <;> simp [boltzmann_dim, thermoEntropy_dim, energy_dim], fun h => ?_⟩
  have := congrArg (fun d => d.exponent .information) h
  simp [boltzmann_dim, thermoEntropy_dim, energy_dim] at this

/-- **The general collision criterion.** Any two dimensions that agree off the
information axis but differ on it collide under `forgetInfo` (same image, distinct
sources) — so every quantity with a nonzero information dimension has a collision partner once `[I]`
is dropped. -/
lemma collision_of_info_differ {d e : Dimension LTMCTIDimensionBase}
    (hoff : forgetInfo d = forgetInfo e) (hinfo : d.exponent .information ≠ e.exponent .information) :
    forgetInfo d = forgetInfo e ∧ d ≠ e :=
  ⟨hoff, fun h => hinfo (congrArg (fun d => d.exponent .information) h)⟩

/-! ## Collisions orthogonal to `[I]` (your examples) -/

/-- Action `M·L²·T⁻¹`. -/
def action_dim : Dimension LTMCTIDimensionBase := M𝓭 * L𝓭 ^ (2 : ℚ) * T𝓭⁻¹

/-- Angular momentum `r × p = L · (M·L·T⁻¹)`. -/
def angularMomentum_dim : Dimension LTMCTIDimensionBase := L𝓭 * (M𝓭 * L𝓭 * T𝓭⁻¹)

/-- Torque `r × F = L · (M·L·T⁻²)`. -/
def torque_dim : Dimension LTMCTIDimensionBase := L𝓭 * (M𝓭 * L𝓭 * T𝓭 ^ (-2 : ℚ))

/-- **Action and angular momentum collide** — both `M·L²·T⁻¹`. This collision is
information-free, so it is present with *and* without `[I]`: the information axis does
not resolve it. -/
lemma action_eq_angularMomentum : action_dim = angularMomentum_dim := by
  ext b <;> cases b <;> norm_num [action_dim, angularMomentum_dim]

/-- **Torque and energy collide** — both `M·L²·T⁻²` — again orthogonal to `[I]`. -/
lemma torque_eq_energy : torque_dim = energy_dim := by
  ext b <;> cases b <;> norm_num [torque_dim, energy_dim]

/-- **The torque/energy collision is orthogonal to `[I]`**: both have information
exponent `0`, so — unlike the `k_B`/entropy collision — the information axis cannot
tell them apart.  Resolving it needs a genuinely new (plane-angle) axis, which the
6-base `Dimension LTMCTIDimensionBase` does not include: torque is `r × F` (a moment, one factor of angle),
energy is `F · d` (a scalar). -/
lemma torque_energy_information_equal :
    torque_dim.exponent .information = energy_dim.exponent .information := by
  rw [torque_eq_energy]

/-! ## More explicit geometric collisions (dimensionally identical, physically distinct)

Each pair below is a provable collision of the dimension map: two physically distinct
quantities have the *same* six-exponent vector, so no dimensional analysis can
separate them.  Like `torque_eq_energy` they are orthogonal to `[I]`; a plane-angle
axis (outside the present base set) is what distinguishes each pair physically. -/

/-- Frequency `T⁻¹` (cycles per second, hertz). -/
def frequency_dim : Dimension LTMCTIDimensionBase := T𝓭⁻¹

/-- Angular velocity `T⁻¹` (radian per second; the radian is dimensionless). -/
def angularVelocity_dim : Dimension LTMCTIDimensionBase := T𝓭⁻¹

/-- Radioactivity `T⁻¹` (decays per second, becquerel). -/
def becquerel_dim : Dimension LTMCTIDimensionBase := T𝓭⁻¹

/-- **Frequency and angular velocity collide** — both `T⁻¹` (hertz vs radian/second):
the `2π` and the plane-angle factor are dimensionless, so the base set cannot see them. -/
lemma frequency_eq_angularVelocity : frequency_dim = angularVelocity_dim := rfl

/-- **Frequency and radioactivity collide** — both `T⁻¹` (hertz vs becquerel). -/
lemma frequency_eq_becquerel : frequency_dim = becquerel_dim := rfl

/-- Heat capacity `E·Θ⁻¹` (joule per kelvin). -/
def heatCapacity_dim : Dimension LTMCTIDimensionBase := energy_dim * Θ𝓭⁻¹

/-- **Heat capacity and (Clausius) entropy collide** — both `E·Θ⁻¹` (J/K): an extensive
`dQ/dT` and a state function `dS` share a dimension.  (This is the *geometric* J/K
collision; the `k_B`/entropy collision above is the one `[I]` resolves.) -/
lemma heatCapacity_eq_thermoEntropy : heatCapacity_dim = thermoEntropy_dim := rfl

/-- Absorbed dose `L²·T⁻²` (gray = joule per kilogram). -/
def gray_dim : Dimension LTMCTIDimensionBase := L𝓭 ^ (2 : ℚ) * T𝓭 ^ (-2 : ℚ)

/-- Dose equivalent `L²·T⁻²` (sievert = joule per kilogram × dimensionless weighting). -/
def sievert_dim : Dimension LTMCTIDimensionBase := L𝓭 ^ (2 : ℚ) * T𝓭 ^ (-2 : ℚ)

/-- Specific energy `L²·T⁻²` (joule per kilogram). -/
def specificEnergy_dim : Dimension LTMCTIDimensionBase := L𝓭 ^ (2 : ℚ) * T𝓭 ^ (-2 : ℚ)

/-- **Absorbed dose and dose equivalent collide** — both `L²·T⁻²` (gray vs sievert): the
radiation-weighting factor `w_R` is dimensionless, so physically distinct doses (energy
deposited vs biological effect) are dimensionally one. -/
lemma gray_eq_sievert : gray_dim = sievert_dim := rfl

/-- **Absorbed dose and specific energy collide** — both `L²·T⁻²` (gray vs J/kg). -/
lemma gray_eq_specificEnergy : gray_dim = specificEnergy_dim := rfl

/-- Pressure `M·L⁻¹·T⁻²` (pascal = N/m²). -/
def pressure_dim : Dimension LTMCTIDimensionBase := M𝓭 * L𝓭 ^ (-1 : ℚ) * T𝓭 ^ (-2 : ℚ)

/-- Energy density `M·L⁻¹·T⁻²` (joule per cubic metre). -/
def energyDensity_dim : Dimension LTMCTIDimensionBase := energy_dim * L𝓭 ^ (-3 : ℚ)

/-- **Pressure and energy density collide** — both `M·L⁻¹·T⁻²` (Pa vs J/m³): the
equation-of-state identity `[p] = [ρc²]` at the level of dimensions. -/
lemma pressure_eq_energyDensity : pressure_dim = energyDensity_dim := by
  ext b <;> cases b <;> norm_num [pressure_dim, energyDensity_dim, energy_dim]

/-- **The collision map is not injective (geometric example).** The dimension map
identifies torque with energy while they are physically distinct — an explicit failure
of injectivity of dimensional labelling, present already in the full six-base system
(not only after `forgetInfo`). -/
lemma dimensionMap_not_injective_geometric :
    torque_dim = energy_dim ∧ frequency_dim = angularVelocity_dim
      ∧ gray_dim = sievert_dim ∧ pressure_dim = energyDensity_dim :=
  ⟨torque_eq_energy, frequency_eq_angularVelocity, gray_eq_sievert,
    pressure_eq_energyDensity⟩

end Physlib.Units.InformationDimensionCollision

end
