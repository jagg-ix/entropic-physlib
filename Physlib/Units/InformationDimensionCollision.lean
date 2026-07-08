/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.Dimension
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
  a forced collision: any theory containing an information-dependent quantity collapses
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

open Dimension

@[expose] public section

namespace Physlib.Units.InformationDimensionCollision

/-- **The 6-base → 5-base projection**: forget the information exponent. -/
def forgetInfo (d : Dimension) : Dimension :=
  ⟨d.length, d.time, d.mass, d.charge, d.temperature, 0⟩

@[simp] theorem forgetInfo_length (d : Dimension) : (forgetInfo d).length = d.length := rfl
@[simp] theorem forgetInfo_time (d : Dimension) : (forgetInfo d).time = d.time := rfl
@[simp] theorem forgetInfo_mass (d : Dimension) : (forgetInfo d).mass = d.mass := rfl
@[simp] theorem forgetInfo_charge (d : Dimension) : (forgetInfo d).charge = d.charge := rfl
@[simp] theorem forgetInfo_temperature (d : Dimension) :
    (forgetInfo d).temperature = d.temperature := rfl
@[simp] theorem forgetInfo_information (d : Dimension) : (forgetInfo d).information = 0 := rfl

/-- `forgetInfo` is multiplicative (a group homomorphism on dimensions). -/
theorem forgetInfo_mul (d e : Dimension) :
    forgetInfo (d * e) = forgetInfo d * forgetInfo e := by ext <;> simp

theorem forgetInfo_one : forgetInfo 1 = 1 := by ext <;> simp

/-! ## The guaranteed collision: `forgetInfo` is not injective -/

theorem forgetInfo_I𝓭 : forgetInfo I𝓭 = 1 := by ext <;> simp

theorem I𝓭_ne_one : (I𝓭 : Dimension) ≠ 1 := by
  intro h; have := congrArg Dimension.information h; simp at this

/-- **Shannon entropy collides with a dimensionless number.** `I𝓭` is a non-trivial
element of the kernel of `forgetInfo`: forgetting `[I]`, one bit of information and a
pure number are the same dimension. -/
theorem shannon_collides_dimensionless :
    forgetInfo I𝓭 = forgetInfo (1 : Dimension) ∧ I𝓭 ≠ (1 : Dimension) :=
  ⟨by rw [forgetInfo_I𝓭, forgetInfo_one], I𝓭_ne_one⟩

/-- **Forgetting `[I]` is not injective** — collisions are guaranteed. -/
theorem forgetInfo_not_injective : ¬ Function.Injective forgetInfo := fun hinj =>
  I𝓭_ne_one (hinj (by rw [forgetInfo_I𝓭, forgetInfo_one]))

/-! ## The physically relevant collision: `k_B` vs thermodynamic entropy -/

/-- Energy dimension `E = M·L²·T⁻²`. -/
def energy_dim : Dimension := M𝓭 * L𝓭 ^ (2 : ℚ) * T𝓭 ^ (-2 : ℚ)

/-- Framework Boltzmann constant `[k_B] = E·Θ⁻¹·I⁻¹`. -/
def boltzmann_dim : Dimension := energy_dim * Θ𝓭⁻¹ * I𝓭⁻¹

/-- Thermodynamic (Clausius) entropy `[S] = E·Θ⁻¹`. -/
def thermoEntropy_dim : Dimension := energy_dim * Θ𝓭⁻¹

/-- **Without `[I]`, the Boltzmann constant and thermodynamic entropy collide.** They
agree off the information axis (`forgetInfo k_B = forgetInfo S = E·Θ⁻¹`) but are
distinct dimensions (`k_B` has exponent `-1` on `[I]`, `S` has exponent `0`). So the 5-base SI structure
*cannot* tell `k_B` from an entropy — the Brillouin/Landauer collision, forced. -/
theorem boltzmann_collides_thermoEntropy :
    forgetInfo boltzmann_dim = forgetInfo thermoEntropy_dim ∧
      boltzmann_dim ≠ thermoEntropy_dim := by
  refine ⟨by ext <;> simp [boltzmann_dim, thermoEntropy_dim, energy_dim], fun h => ?_⟩
  have := congrArg Dimension.information h
  simp [boltzmann_dim, thermoEntropy_dim, energy_dim] at this

/-- **The general collision criterion.** Any two dimensions that agree off the
information axis but differ on it collide under `forgetInfo` (same image, distinct
sources) — so every information-dependent quantity has a collision partner once `[I]`
is dropped. -/
theorem collision_of_info_differ {d e : Dimension}
    (hoff : forgetInfo d = forgetInfo e) (hinfo : d.information ≠ e.information) :
    forgetInfo d = forgetInfo e ∧ d ≠ e :=
  ⟨hoff, fun h => hinfo (congrArg Dimension.information h)⟩

/-! ## Collisions orthogonal to `[I]` (your examples) -/

/-- Action `M·L²·T⁻¹`. -/
def action_dim : Dimension := M𝓭 * L𝓭 ^ (2 : ℚ) * T𝓭⁻¹

/-- Angular momentum `r × p = L · (M·L·T⁻¹)`. -/
def angularMomentum_dim : Dimension := L𝓭 * (M𝓭 * L𝓭 * T𝓭⁻¹)

/-- Torque `r × F = L · (M·L·T⁻²)`. -/
def torque_dim : Dimension := L𝓭 * (M𝓭 * L𝓭 * T𝓭 ^ (-2 : ℚ))

/-- **Action and angular momentum collide** — both `M·L²·T⁻¹`. This collision is
information-free, so it is present with *and* without `[I]`: the information axis does
not resolve it. -/
theorem action_eq_angularMomentum : action_dim = angularMomentum_dim := by
  ext <;> norm_num [action_dim, angularMomentum_dim]

/-- **Torque and energy collide** — both `M·L²·T⁻²` — again orthogonal to `[I]`. -/
theorem torque_eq_energy : torque_dim = energy_dim := by
  ext <;> norm_num [torque_dim, energy_dim]

end Physlib.Units.InformationDimensionCollision

end
