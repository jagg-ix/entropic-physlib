/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.InformationDimensionCollision

/-!
# Dimensional analysis of the gravitational coupling system, with the information axis

The equations of `Thermodynamics.NewtonGIsolation` and
`Thermodynamics.GravitationalCouplingSystem` are stated on `ℝ`, where dimensional
consistency is invisible. This module re-runs the whole system in the 6-base dimension
group `⟨L, T, M, C, Θ, I⟩` of `Units.Dimension` — the base with the information axis
`I𝓭` — and separates what the ordinary 5-base SI analysis sees from what only `[I]`
can see.

The dimension vectors (components `⟨length, time, mass, charge, temperature,
information⟩`):

```
  c   velocity_dim            = ⟨ 1, −1,  0, 0,  0,  0⟩
  ℏ   action_dim              = ⟨ 2, −1,  1, 0,  0,  0⟩
  k_B boltzmann_dim           = ⟨ 2, −2,  1, 0, −1, −1⟩   (framework: per nat)
  S   thermoEntropy_dim       = ⟨ 2, −2,  1, 0, −1,  0⟩   (Clausius)
  G   newtonConstant_dim      = ⟨ 3, −2, −1, 0,  0,  0⟩   (SI)
  N   bit count               = ⟨ 0,  0,  0, 0,  0,  1⟩ = I𝓭
  κ   einsteinCoupling_dim    = ⟨−1,  2, −1, 0,  0,  0⟩   (8πG/c⁴)
  T   stressEnergy_dim        = ⟨−1, −2,  1, 0,  0,  0⟩   (energy density)
  R   curvature_dim           = ⟨−2,  0,  0, 0,  0,  0⟩   (Ricci)
  Φ   gravitationalPotential  = ⟨ 2, −2,  0, 0,  0,  0⟩   (= c²)
```

## §A — the typings `[I]` forces

These are *iff* theorems: the dimension of the unknown is solved for in the group, not
assumed.

* `equipartition_forces_bitCount` — equipartition `E = ½·N·k_B·T` with the framework
  `[k_B] = E·Θ⁻¹·I⁻¹` is consistent **iff `[N] = I𝓭`**: the holographic bit count is
  not a pure number, it carries the information dimension.
* `entropicForce_forces_clausiusEntropy` + `thermoEntropy_eq_boltzmann_mul_info` — the
  Verlinde force `F = T·ΔS/Δx` is a force iff `[ΔS] = E·Θ⁻¹` (Clausius); since
  `E·Θ⁻¹ = [k_B]·I𝓭`, the displacement count `2π·Δx/λ_C` in
  `ΔS = 2π·k_B·Δx/λ_C` **carries `I𝓭`**: displacement in Compton units is a count of
  nats.
* `holographicBits_forces_newton_perBit` — with `[N] = I𝓭` forced, the identification
  `N = A·c³/(G·ℏ)` is consistent iff `[G] = L³M⁻¹T⁻²·I𝓭⁻¹`: dimensionally too,
  **Newton's constant is area-per-bit** — the `[I]`-level counterpart of
  `newtonG_eq_area_per_bit`.
* `weakFieldMetric_forces_potential` — the weak-field metric `g₀₀ = 1 + 2Φ/c²`
  (dimensionless metric) forces `[Φ] = c²`.

## §B — the SI sector: every clause of the master theorem type-checks

Each clause of `newtonG_establishes_gravitationalSystem` is dimensionally an identity
in the group (information exponent `0` throughout — this is the part 5-base SI sees):
screen temperature is a temperature, `G·M·m/R²` is a force, `κ·T` is a curvature (the
Einstein equation), the dust source `κ·ρc²` matches the Poisson source `G·ρ/c²` as
curvatures, `∇²Φ = 4πGρ` balances, and `2GM/c²` is a length. Since the complex EFE's
entropic sector `Λ = κ·S` has `S` on the same stress-energy carrier as `T`, the single
computation `einsteinEquation_dimensional` types both the real (GR) and imaginary
(entropic) sectors.

## §C — what only `[I]` sees: the bit forms carry a uniform one-nat defect

Written G-free through the bit count `N`, the system's formulas are **not**
`I`-balanced: each is off from its SI target by exactly `I𝓭⁻¹` —

* force `4π·m·M·c³/(ℏN)` is `force_dim · I𝓭⁻¹` (`bitFormForce_defect`),
* Newton constant `A·c³/(ℏN)` is `newtonConstant_dim · I𝓭⁻¹` (`bitFormNewton_defect`),
* coupling `8π(A/N)/(ℏc)` is `einsteinCoupling_dim · I𝓭⁻¹` (`bitFormCoupling_defect`),
* Schwarzschild `2McA/(ℏN)` is `L𝓭 · I𝓭⁻¹` (`bitFormSchwarzschild_defect`).

`oneNat_threads_system` packages the point: **a single defect `δ` works for all four**
(`δ = I𝓭⁻¹` — one nat), and `δ` is invisible to the 5-base projection
(`forgetInfo δ = 1` yet `δ ≠ 1`, the collision mechanism of
`InformationDimensionCollision`). One `G` threads the real-number system
(`GravitationalCouplingSystem`); one nat threads its dimensional ledger. Concretely:
every bit-form equation silently converts one unit of information into mechanics, and
the 5-base SI basis cannot detect that it does.

## References

* Carriers: `Units.Dimension` (the 6-base group), `Units.InformationDimensionCollision`
  (`energy_dim`, `boltzmann_dim`, `thermoEntropy_dim`, `action_dim`, `forgetInfo`),
  `Thermodynamics.NewtonGIsolation` and `Thermodynamics.GravitationalCouplingSystem`
  (the `ℝ`-level equations typed here).
* E. Verlinde, *On the origin of gravity and the laws of Newton*, JHEP 04 (2011) 029 —
  equipartition `E = ½Nk_BT`, `ΔS = 2πk_B·Δx/λ_C`, `N = Ac³/(Gℏ)`.
* L. Brillouin (1956); R. Landauer (1961) — the information axis.
-/

set_option autoImplicit false

open Dimension.LTMCTI Physlib.Units.InformationDimensionCollision

@[expose] public section

namespace Physlib.Units.GravitationalCouplingDimensions

/-! ## Dimension LTMCTIDimensionBase vectors of the system's quantities -/

/-- Velocity `[c] = L·T⁻¹`. -/
def velocity_dim : Dimension LTMCTIDimensionBase := L𝓭 * T𝓭⁻¹

/-- Force `[F] = E·L⁻¹ = M·L·T⁻²`. -/
def force_dim : Dimension LTMCTIDimensionBase := energy_dim * L𝓭⁻¹

/-- Area `[A] = L²`. -/
def area_dim : Dimension LTMCTIDimensionBase := L𝓭 ^ (2 : ℚ)

/-- Newton's constant, SI reading: `[G] = L³·M⁻¹·T⁻²`. -/
def newtonConstant_dim : Dimension LTMCTIDimensionBase := L𝓭 ^ (3 : ℚ) * M𝓭⁻¹ * T𝓭 ^ (-2 : ℚ)

/-- Mass density `[ρ] = M·L⁻³`. -/
def massDensity_dim : Dimension LTMCTIDimensionBase := M𝓭 * L𝓭 ^ (-3 : ℚ)

/-- The Einstein coupling `[κ] = [8πG/c⁴] = M⁻¹·L⁻¹·T²`. -/
def einsteinCoupling_dim : Dimension LTMCTIDimensionBase := newtonConstant_dim / velocity_dim ^ (4 : ℚ)

/-- Curvature (Ricci) `[R] = L⁻²`. -/
def curvature_dim : Dimension LTMCTIDimensionBase := L𝓭 ^ (-2 : ℚ)

/-- Stress-energy (energy density) `[T_{μν}] = E·L⁻³`. -/
def stressEnergy_dim : Dimension LTMCTIDimensionBase := energy_dim * L𝓭 ^ (-3 : ℚ)

/-- Gravitational potential `[Φ] = L²·T⁻²` — forced equal to `c²` by the weak-field
metric (`weakFieldMetric_forces_potential`). -/
def gravitationalPotential_dim : Dimension LTMCTIDimensionBase := velocity_dim ^ (2 : ℚ)

/-! ## §A — the typings `[I]` forces -/

/-- **Equipartition forces the bit count onto the information axis.** With the framework
Boltzmann constant `[k_B] = E·Θ⁻¹·I⁻¹`, the equipartition law `E = ½·N·k_B·T`
(`NewtonGIsolation.bitScreenTemperature` is its inversion) is dimensionally consistent
**iff** `[N] = I𝓭`. The holographic bit count is not a dimensionless number: it is
information. -/
theorem equipartition_forces_bitCount (n : Dimension LTMCTIDimensionBase) :
    n * boltzmann_dim * Θ𝓭 = energy_dim ↔ n = I𝓭 := by
  have key : I𝓭 * boltzmann_dim * Θ𝓭 = energy_dim := by
    ext b <;> cases b <;> norm_num [boltzmann_dim, energy_dim]
  exact ⟨fun h => mul_right_cancel (mul_right_cancel (h.trans key.symm)),
    fun h => by rw [h]; exact key⟩

/-- **The entropic force is a force iff the displacement entropy is Clausius.**
`F = T·ΔS/Δx` (`verlindeEntropicForce`) lands on `force_dim` **iff**
`[ΔS] = E·Θ⁻¹ = thermoEntropy_dim`. -/
theorem entropicForce_forces_clausiusEntropy (s : Dimension LTMCTIDimensionBase) :
    Θ𝓭 * s * L𝓭⁻¹ = force_dim ↔ s = thermoEntropy_dim := by
  have key : Θ𝓭 * thermoEntropy_dim * L𝓭⁻¹ = force_dim := by
    ext b <;> cases b <;> norm_num [thermoEntropy_dim, energy_dim, force_dim]
  refine ⟨fun h => ?_, fun h => by rw [h]; exact key⟩
  exact mul_left_cancel (mul_right_cancel (h.trans key.symm))

/-- **Clausius entropy is the Boltzmann constant times one information unit**:
`E·Θ⁻¹ = [k_B]·I𝓭`. Combined with `entropicForce_forces_clausiusEntropy`: in
`ΔS = 2π·k_B·(Δx/λ_C)` the count `2π·Δx/λ_C` must carry `I𝓭` — displacement measured
in Compton units is a count of nats. -/
theorem thermoEntropy_eq_boltzmann_mul_info :
    thermoEntropy_dim = boltzmann_dim * I𝓭 := by
  ext b <;> cases b <;> norm_num [thermoEntropy_dim, boltzmann_dim, energy_dim]

/-- **The holographic identification forces `G` to be area-per-bit dimensionally.** With
`[N] = I𝓭` (forced by `equipartition_forces_bitCount`), the identification
`N·(G·ℏ) = A·c³` — the cross-multiplied `N = holographicBits A G ℏ c` — is consistent
**iff** `[G] = L³·M⁻¹·T⁻²·I𝓭⁻¹`: Newton's constant absorbs one inverse information
unit, the `[I]`-level counterpart of `newtonG_eq_area_per_bit` (`G = A·c³/(ℏN)`). -/
theorem holographicBits_forces_newton_perBit (g : Dimension LTMCTIDimensionBase) :
    I𝓭 * (g * action_dim) = area_dim * velocity_dim ^ (3 : ℚ) ↔
      g = newtonConstant_dim * I𝓭⁻¹ := by
  have key : I𝓭 * ((newtonConstant_dim * I𝓭⁻¹) * action_dim)
      = area_dim * velocity_dim ^ (3 : ℚ) := by
    ext b <;> cases b <;> norm_num [newtonConstant_dim, area_dim, velocity_dim, action_dim]
  exact ⟨fun h => mul_right_cancel (mul_left_cancel (h.trans key.symm)),
    fun h => by rw [h]; exact key⟩

/-- **The information typing has exactly one solution — existence and uniqueness, no
hypotheses.**  The two identities of the holographic chain — equipartition
`E = ½Nk_BT` and the bit count `N·Għ = Ac³` — determine the dimensions of the bit count
and of Newton's constant *simultaneously and uniquely*: the only pair satisfying both is
`([N], [G]) = (I, L³M⁻¹T⁻²·I⁻¹)`.  Nothing is assumed beyond the repository's own
definitions of the dimensions appearing in the identities; the two `∀`-quantified iff
theorems above (`equipartition_forces_bitCount`, `holographicBits_forces_newton_perBit`)
are each a uniqueness statement over a free dimension variable, and this theorem is their
composition into the unique solvability of the system.  The bit count is information and
Newton's constant is area per nat — not as a reading of the formalism, but as the sole
point the constraint system admits. -/
theorem information_typing_unique :
    ∃! p : Dimension LTMCTIDimensionBase × Dimension LTMCTIDimensionBase,
      p.1 * boltzmann_dim * Θ𝓭 = energy_dim ∧
      p.1 * (p.2 * action_dim) = area_dim * velocity_dim ^ (3 : ℚ) := by
  refine ⟨(I𝓭, newtonConstant_dim * I𝓭⁻¹), ⟨?_, ?_⟩, ?_⟩
  · exact (equipartition_forces_bitCount I𝓭).mpr rfl
  · exact (holographicBits_forces_newton_perBit (newtonConstant_dim * I𝓭⁻¹)).mpr rfl
  · rintro ⟨n, g⟩ ⟨h1, h2⟩
    have hn : n = I𝓭 := (equipartition_forces_bitCount n).mp h1
    subst hn
    have hg : g = newtonConstant_dim * I𝓭⁻¹ :=
      (holographicBits_forces_newton_perBit g).mp h2
    rw [hg]

/-- **The weak-field metric forces `[Φ] = c²`.** In `g₀₀ = 1 + 2Φ/c²`
(`NewtonianAndGRLimit`) the metric component is dimensionless, so `[Φ]·[c²]⁻¹ = 1`
**iff** `[Φ] = velocity_dim²`. -/
theorem weakFieldMetric_forces_potential (p : Dimension LTMCTIDimensionBase) :
    p * velocity_dim ^ (-2 : ℚ) = 1 ↔ p = gravitationalPotential_dim := by
  have key : gravitationalPotential_dim * velocity_dim ^ (-2 : ℚ) = 1 := by
    ext b <;> cases b <;> norm_num [gravitationalPotential_dim, velocity_dim]
  exact ⟨fun h => mul_right_cancel (h.trans key.symm), fun h => by rw [h]; exact key⟩

/-! ## §B — the SI sector: every clause of the master theorem type-checks -/

/-- **The screen temperature is a temperature**: `[2Mc²/(N·k_B)] = Θ` with `[N] = I𝓭` —
types `NewtonGIsolation.bitScreenTemperature`. -/
theorem screenTemperature_isTemperature :
    energy_dim * (I𝓭 * boltzmann_dim)⁻¹ = Θ𝓭 := by
  ext b <;> cases b <;> norm_num [boltzmann_dim, energy_dim]

/-- **Newton's force law balances**: `[G·M·m/R²] = force` — types the Newton clause of
the master theorem. -/
theorem newtonForce_isForce :
    newtonConstant_dim * M𝓭 ^ (2 : ℚ) * L𝓭 ^ (-2 : ℚ) = force_dim := by
  ext b <;> cases b <;> norm_num [newtonConstant_dim, force_dim, energy_dim]

/-- **The Einstein field equation balances**: `[κ·T_{μν}] = [Ric] = L⁻²`. Since the
complex EFE's entropic sector `Λ = κ·S` carries `S` on the same stress-energy carrier,
this types the real (GR) and imaginary (entropic) sectors at once. -/
theorem einsteinEquation_dimensional :
    einsteinCoupling_dim * stressEnergy_dim = curvature_dim := by
  ext b <;> cases b <;> norm_num [einsteinCoupling_dim, newtonConstant_dim, velocity_dim,
    stressEnergy_dim, energy_dim, curvature_dim]

/-- **The dust source is a curvature**: `[κ·ρc²] = L⁻²` — types the left side of
`dust_traceReversed_source`. -/
theorem dustSource_isCurvature :
    einsteinCoupling_dim * (massDensity_dim * velocity_dim ^ (2 : ℚ)) = curvature_dim := by
  ext b <;> cases b <;> norm_num [einsteinCoupling_dim, newtonConstant_dim, velocity_dim,
    massDensity_dim, curvature_dim]

/-- **The Poisson source matches**: `[4πGρ/c²] = L⁻²` — types the right side of
`dust_traceReversed_source`, so both sides of the dust reduction are curvatures. -/
theorem poissonSource_isCurvature :
    newtonConstant_dim * massDensity_dim * velocity_dim ^ (-2 : ℚ) = curvature_dim := by
  ext b <;> cases b <;> norm_num [newtonConstant_dim, massDensity_dim, velocity_dim, curvature_dim]

/-- **The Poisson equation balances**: `[∇²Φ] = [4πGρ] = T⁻²` — types
`weakField_einstein_poisson`'s conclusion `∇²Φ = 4πGρ`. -/
theorem poisson_dimensional :
    gravitationalPotential_dim * L𝓭 ^ (-2 : ℚ)
      = newtonConstant_dim * massDensity_dim := by
  ext b <;> cases b <;> norm_num [gravitationalPotential_dim, velocity_dim, newtonConstant_dim,
    massDensity_dim]

/-- **The Schwarzschild radius is a length**: `[2GM/c²] = L` — types the Schwarzschild
clause of the master theorem. -/
theorem schwarzschildRadius_isLength :
    newtonConstant_dim * M𝓭 * velocity_dim ^ (-2 : ℚ) = L𝓭 := by
  ext b <;> cases b <;> norm_num [newtonConstant_dim, velocity_dim]

/-! ## §C — what only `[I]` sees: the uniform one-nat defect of the bit forms -/

/-- **The bit-form force carries the defect `I𝓭⁻¹`**:
`[4π·m·M·c³/(ℏ·N)] = force·I𝓭⁻¹` — the G-free `entropicForce_bitForm` converts one nat
into mechanics. -/
theorem bitFormForce_defect :
    M𝓭 ^ (2 : ℚ) * velocity_dim ^ (3 : ℚ) * (action_dim * I𝓭)⁻¹
      = force_dim * I𝓭⁻¹ := by
  ext b <;> cases b <;> norm_num [velocity_dim, action_dim, force_dim, energy_dim]

/-- **The bit-form Newton constant carries the defect `I𝓭⁻¹`**:
`[A·c³/(ℏ·N)] = [G]·I𝓭⁻¹` — the defect form of `newtonG_eq_area_per_bit`, and the
`forgetInfo`-hidden content of `holographicBits_forces_newton_perBit`. -/
theorem bitFormNewton_defect :
    area_dim * velocity_dim ^ (3 : ℚ) * (action_dim * I𝓭)⁻¹
      = newtonConstant_dim * I𝓭⁻¹ := by
  ext b <;> cases b <;> norm_num [area_dim, velocity_dim, action_dim, newtonConstant_dim]

/-- **The bit-form Einstein coupling carries the defect `I𝓭⁻¹`**:
`[8π·(A/N)/(ℏc)] = [κ]·I𝓭⁻¹` — types `einsteinCoupling_bitForm`. -/
theorem bitFormCoupling_defect :
    area_dim * I𝓭⁻¹ * (action_dim * velocity_dim)⁻¹
      = einsteinCoupling_dim * I𝓭⁻¹ := by
  ext b <;> cases b <;> norm_num [area_dim, action_dim, velocity_dim, einsteinCoupling_dim,
    newtonConstant_dim]

/-- **The bit-form Schwarzschild radius carries the defect `I𝓭⁻¹`**:
`[2·M·c·A/(ℏ·N)] = L·I𝓭⁻¹` — types `schwarzschildRadius_bitForm`. -/
theorem bitFormSchwarzschild_defect :
    M𝓭 * velocity_dim * area_dim * (action_dim * I𝓭)⁻¹ = L𝓭 * I𝓭⁻¹ := by
  ext b <;> cases b <;> norm_num [velocity_dim, area_dim, action_dim]

/-- **One nat threads the system.** A *single* defect `δ` accounts for every bit form at
once — force, Newton constant, Einstein coupling, Schwarzschild radius are each their SI
target times the same `δ` — and `δ` is invisible to the 5-base projection
(`forgetInfo δ = 1`) while being dimensionally real (`δ ≠ 1`). The witness is one
inverse nat, `δ = I𝓭⁻¹`: the dimensional counterpart of the one `G` threading
`newtonG_establishes_gravitationalSystem`, and the reason the defect cannot be seen
without the information axis. -/
theorem oneNat_threads_system :
    ∃ δ : Dimension LTMCTIDimensionBase,
      forgetInfo δ = 1 ∧ δ ≠ 1
      ∧ M𝓭 ^ (2 : ℚ) * velocity_dim ^ (3 : ℚ) * (action_dim * I𝓭)⁻¹ = force_dim * δ
      ∧ area_dim * velocity_dim ^ (3 : ℚ) * (action_dim * I𝓭)⁻¹
          = newtonConstant_dim * δ
      ∧ area_dim * I𝓭⁻¹ * (action_dim * velocity_dim)⁻¹ = einsteinCoupling_dim * δ
      ∧ M𝓭 * velocity_dim * area_dim * (action_dim * I𝓭)⁻¹ = L𝓭 * δ := by
  refine ⟨I𝓭⁻¹, by ext b <;> cases b <;> simp, fun h => ?_,
    bitFormForce_defect, bitFormNewton_defect, bitFormCoupling_defect,
    bitFormSchwarzschild_defect⟩
  have := congrArg (fun d => d.exponent .information) h
  simp at this

end Physlib.Units.GravitationalCouplingDimensions

end
