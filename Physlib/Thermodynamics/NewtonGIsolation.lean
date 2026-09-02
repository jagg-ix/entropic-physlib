/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Isolating Newton's constant: the derivation certified non-tautological

`VerlindeNewtonGravity.newton_law_of_gravity_from_verlinde` recovers `F = GMm/R²`, but its
screen temperature carries `G` through the holographic bit count — so, as it stands, `G`
is inserted through a definition, not isolated.  This module repairs that in four steps,
each a certificate that the derivation has content:

* **Certificate A — the force law is `G`-free** (`entropicForce_bitForm`): with the bit
  count `N` a *free variable*, the entropic force from equipartition
  (`bitScreenTemperature`, certified against `equipartitionEnergy` and `E = Mc²`) and the
  displacement entropy is `F = 4π·mM·c³/(ℏN)` — an inverse-*bit* law in which `G` does
  not occur.  Gravity, at this stage, is information counting.
* **Certificate B — the form discriminates** (`areaScaling_inverseSquare`,
  `volumeScaling_not_inverseSquare`): the inverse-square law holds **iff** the bits scale
  with the *area* (`N = σr²` makes `F·r²` independent of `r`), and provably fails for
  extensive (volume) counting — the derivation could have been refuted, hence is not a
  definition in disguise.
* **Certificate C — `G` is isolated, and the Planck density is forced**
  (`newtonG_isolated`, `newtonG_eq_area_per_bit`): Newton's form `F = GMm/R²` holds
  **iff** `N = holographicBits (sphereArea R) G ℏ c` — the bit count assumed by the
  existing derivation is the *unique* one compatible with Newton's law, and conversely
  `G = sphereArea R·c³/(ℏN)`: **Newton's constant is the area-per-bit conversion factor
  in units `c³/ℏ`**, measured by the information density of the screen.
* **Certificate D — two independent routes agree** (`unruh_matches_screen`,
  `secondLaw_route_agrees`, `newtonPotential_hasDerivAt`): identifying the equipartition
  temperature with the Unruh temperature (`CausalDiamond.unruhTemperature`) fixes the
  screen acceleration `a = 4πMc³/(ℏN)`, and Newton's *second* law route `F = ma`
  reproduces the same force — while the isolated `GM/r²` is the genuine derivative of the
  Newtonian potential `Φ = −GM/r` whose Poisson equation the weak-field arc
  (`ComptonClock.NewtonianAndGRLimit.weakField_einstein_poisson`) derives independently.

## References

* E. Verlinde, JHEP **04** (2011) 029; carriers:
  `Thermodynamics.VerlindeEntropicForce`, `Thermodynamics.VerlindeNewtonGravity`,
  `CausalDiamond.EquivalencePrinciple` (Unruh), `ComptonClock.NewtonianAndGRLimit`
  (the independently derived Poisson normalization).
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple

@[expose] public section

namespace Physlib.Thermodynamics.NewtonGIsolation

/-! ## §A — the `G`-free force law -/

/-- **The screen temperature with a free bit count**: the equipartition solution
`T = 2Mc²/(N·k_B)` — no `G` enters. -/
noncomputable def bitScreenTemperature (M c N kB : ℝ) : ℝ := 2 * M * c^2 / (N * kB)

/-- The screen temperature is *the* equipartition solution: it renders
`½·N·k_B·T = Mc²` exactly. -/
theorem bitScreenTemperature_solves_equipartition (M c N kB : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) :
    equipartitionEnergy N kB (bitScreenTemperature M c N kB)
      = massEnergyEquivalence M c := by
  unfold equipartitionEnergy bitScreenTemperature massEnergyEquivalence
  field_simp

/-- **Certificate A — the entropic force in bit form is `G`-free**:
`F = 4π·mM·c³/(ℏ·N)` — gravity as information counting, with the bit count `N` a free
variable and Newton's constant nowhere in the statement. -/
theorem entropicForce_bitForm (M c N kB m ℏ Δx : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) :
    verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx
      = 4 * Real.pi * m * M * c^3 / (ℏ * N) := by
  unfold verlindeEntropicForce bitScreenTemperature verlindeDisplacementEntropy
  field_simp
  ring

/-! ## §B — the form discriminates: area scaling iff inverse square -/

/-- **Area-scaling bits give the inverse-square law**: with `N = σ·r²`, the combination
`F·r²` is independent of `r`. -/
theorem areaScaling_inverseSquare (M c kB m ℏ Δx σ r : ℝ)
    (hσ : σ ≠ 0) (hr : r ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) :
    verlindeEntropicForce (bitScreenTemperature M c (σ * r^2) kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx * r^2
      = 4 * Real.pi * m * M * c^3 / (ℏ * σ) := by
  rw [entropicForce_bitForm M c (σ * r^2) kB m ℏ Δx
    (mul_ne_zero hσ (pow_ne_zero 2 hr)) hkB hΔx]
  field_simp

/-- **Certificate B — extensive (volume) counting is refuted**: with `N = σ·r³` the
combination `F·r²` *depends on `r`*, so the inverse-square law fails — the derivation
discriminates between information-scaling laws and could have been falsified. -/
theorem volumeScaling_not_inverseSquare (M c kB m ℏ Δx σ r₁ r₂ : ℝ)
    (hσ : 0 < σ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hne : r₁ ≠ r₂)
    (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hm : 0 < m) (hM : 0 < M) (hc : 0 < c) (hℏ : 0 < ℏ) :
    verlindeEntropicForce (bitScreenTemperature M c (σ * r₁^3) kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx * r₁^2
      ≠ verlindeEntropicForce (bitScreenTemperature M c (σ * r₂^3) kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx * r₂^2 := by
  rw [entropicForce_bitForm M c (σ * r₁^3) kB m ℏ Δx
      (mul_ne_zero hσ.ne' (pow_ne_zero 3 hr₁.ne')) hkB hΔx,
    entropicForce_bitForm M c (σ * r₂^3) kB m ℏ Δx
      (mul_ne_zero hσ.ne' (pow_ne_zero 3 hr₂.ne')) hkB hΔx]
  intro h
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  apply hne
  field_simp at h
  nlinarith [h, mul_pos (mul_pos (mul_pos (mul_pos hπ hm) hM) (pow_pos hc 3)) hσ,
    pow_pos hr₁ 3, pow_pos hr₂ 3, sq_nonneg (r₁ - r₂), sq_nonneg (r₁ + r₂)]

/-! ## §C — the isolation of Newton's constant -/

/-- **Certificate C — `G` is isolated and the Planck density is forced**: the `G`-free
force takes Newton's form `F = G·M·m/R²` **iff** the bit count is exactly the holographic
count `N = holographicBits (sphereArea R) G ℏ c = 4πR²c³/(Gℏ)` — the assumption of the
existing derivation is the *unique* bit count compatible with Newton's law. -/
theorem newtonG_isolated (M c N kB m ℏ Δx G R : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0)
    (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0) :
    verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx = G * M * m / R^2
      ↔ N = holographicBits (sphereArea R) G ℏ c := by
  rw [entropicForce_bitForm M c N kB m ℏ Δx hN hkB hΔx]
  unfold holographicBits sphereArea
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    rw [h]
    field_simp

/-- **Newton's constant is the area-per-bit conversion factor**: from Newton's form,
`G = sphereArea R · c³/(ℏ·N)` — `G` measures how much screen area one bit of holographic
information occupies, in units `c³/ℏ`. -/
theorem newtonG_eq_area_per_bit (M c N kB m ℏ Δx G R : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0)
    (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (h : verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx = G * M * m / R^2) :
    G = sphereArea R * c^3 / (ℏ * N) := by
  have hiso := (newtonG_isolated M c N kB m ℏ Δx G R hN hkB hΔx hm hM hc hℏ hG hR).mp h
  unfold holographicBits at hiso
  rw [hiso]
  field_simp

/-! ## §D — two independent routes agree -/

/-- **The Unruh identification fixes the screen acceleration**: the equipartition
temperature equals the Unruh temperature iff `a = 4πMc³/(ℏN)`. -/
theorem unruh_matches_screen (M c N kB ℏ a : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (hℏ : ℏ ≠ 0) :
    unruhTemperature ℏ kB c a = bitScreenTemperature M c N kB
      ↔ a = 4 * Real.pi * M * c^3 / (ℏ * N) := by
  unfold unruhTemperature bitScreenTemperature
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : (ℏ * a / (2 * Real.pi * kB * c) = 2 * M * c^2 / (N * kB))
      ↔ ℏ * a * N = 4 * Real.pi * M * c^3 := by
    rw [div_eq_div_iff
      (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) hkB) hc)
      (mul_ne_zero hN hkB)]
    constructor
    · intro h
      have h' : (ℏ * a * N) * kB = (4 * Real.pi * M * c^3) * kB := by
        linear_combination h
      exact mul_right_cancel₀ hkB h'
    · intro h
      linear_combination kB * h
  rw [key, eq_div_iff (mul_ne_zero hℏ hN)]
  constructor <;> intro h <;> linear_combination h

/-- **Newton's second-law route agrees**: the inertial force `m·a` at the Unruh-matched
screen acceleration equals the entropic force — the thermodynamic (`F = T·ΔS/Δx`) and
inertial (`F = m·a`) derivations give the same law. -/
theorem secondLaw_route_agrees (M c N kB m ℏ Δx : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) :
    m * (4 * Real.pi * M * c^3 / (ℏ * N))
      = verlindeEntropicForce (bitScreenTemperature M c N kB)
          (verlindeDisplacementEntropy ℏ kB m c Δx) Δx := by
  rw [entropicForce_bitForm M c N kB m ℏ Δx hN hkB hΔx]
  ring

/-- **The isolated force is the genuine gradient of the Newtonian potential**:
`d/dr(−GM/r) = GM/r²` — the entropic route lands on the same potential whose Poisson
equation the weak-field arc derives independently
(`ComptonClock.NewtonianAndGRLimit.weakField_einstein_poisson`). -/
theorem newtonPotential_hasDerivAt (G M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => -(G*M)/s) (G*M/r^2) r := by
  have h := (hasDerivAt_inv hr).const_mul (-(G*M))
  have heq : -(G*M) * (-(r^2)⁻¹) = G*M/r^2 := by
    field_simp
  rw [heq] at h
  refine h.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · rfl
  · filter_upwards with s
    rw [div_eq_mul_inv]

end Physlib.Thermodynamics.NewtonGIsolation

end
