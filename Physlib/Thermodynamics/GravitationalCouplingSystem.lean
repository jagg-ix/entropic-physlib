/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.NewtonGIsolation
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde

/-!
# The gravitational coupling system: one `G` from the screen to the complex EFE

`NewtonGIsolation` isolated Newton's constant at the screen level.  This module shows the
*system*: the same isolated `G` threads every gravitational equation formalized in the
library, with the dependency structure made explicit.

```
bit count N ──[A: F = 4πmMc³/(ℏN), G-free]──┐
                                            ├──[C: iff]── F = GMm/R²        (Newton)
holographicBits (A/ℓ_P²) ───────────────────┘                 │
      │                                                       │
      └── G = A·c³/(ℏN)  (area per bit)                       │
                │                                             │
                ├── κ = 8πG/c⁴ = 8π(A/N)/(ℏc) (Einstein coupling: 8π Planck areas per ℏc)
                │        │
                │        ├── G_{μν} = κT_{μν}                 (einsteinFieldEquation)
                │        ├── 𝒢 = κ(T + iS), Λ = κS            (CompleteComplexEinsteinFieldEquation)
                │        └── dust: R₀₀ = 4πGρ/c² → ∇²Φ = 4πGρ (weakField_einstein_poisson)
                │
                └── r_s = 2GM/c² = 2McA/(ℏN)                  (schwarzschildRadius)
```

* `einsteinCoupling_bitForm` — the Einstein coupling `κ = 8πG/c⁴` at the isolated `G` is
  `κ = 8π·(A/N)/(ℏc)`: **`8π` times the area-per-bit over `ℏc`** — the EFE normalization
  in pure information terms (`A/N = ℓ_P²`).
* `dust_traceReversed_source` — the dust source `κ·(ρc²/2)` is exactly the `4πGρ/c²` that
  `weakField_einstein_poisson` consumes: the κ-normalized Einstein equation reduces to
  Newton's Poisson equation with the *same* `G` the screen isolated.
* `schwarzschildRadius_bitForm` — the Schwarzschild radius at the isolated `G` is
  `r_s = 2McA/(ℏN)` — the GR horizon scale in bit form.
* `newtonG_establishes_gravitationalSystem` — **the master theorem**: from the single
  identification `N = holographicBits (sphereArea R) G ℏ c` (which Certificate C proved is
  *forced* by Newton's form) follow, simultaneously: Newton's law, the bit-form Einstein
  coupling, the dust reduction feeding the Poisson equation, the bit-form Schwarzschild
  radius, and — for any curvature/matter data satisfying the real and entropic sectors —
  the **complete complex Einstein field equation** at that coupling, whose real sector is
  standard GR (`G = κT`) and whose imaginary sector carries `Λ = κS`.

Every gravitational equation in the library — Newton, Poisson, weak-field metric, EFE,
complex EFE, Schwarzschild — runs on the one constant the screen's information density
determines.

## References

* Carriers: `Thermodynamics.NewtonGIsolation` (certificates A–D),
  `ComplexEinstein.CompleteComplexEinsteinFieldEquations` (the tensor system),
  `ComptonClock.NewtonianAndGRLimit` (`weakField_einstein_poisson`, `g₀₀ = 1+2Φ/c²`),
  `Relativity.SemiClassical.SchwarzschildVerlinde` (`schwarzschildRadius`,
  `holographicBits` bridge).
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.Relativity.SemiClassical

@[expose] public section

namespace Physlib.Thermodynamics.GravitationalCouplingSystem

/-! ## §A — the Einstein coupling in bit form -/

/-- **The Einstein coupling at the isolated `G` is `8π` times the area-per-bit over `ℏc`**:
`κ = 8πG/c⁴ = 8π·(sphereArea R/N)/(ℏc)` when `N = holographicBits (sphereArea R) G ℏ c` —
the EFE normalization as `8π` Planck areas (`A/N = ℓ_P²`) per `ℏc`. -/
theorem einsteinCoupling_bitForm (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hN : N = holographicBits (sphereArea R) G ℏ c) :
    8 * Real.pi * G / c^4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  unfold holographicBits sphereArea at hN
  rw [hN]
  unfold sphereArea
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The dust source of the trace-reversed Einstein equation**: `κ·(ρc²/2) = 4πGρ/c²` —
for dust (`T₀₀ = ρc²`, `T₀₀ − ½Tg₀₀ = ½ρc²`), the κ-normalized right-hand side is exactly
the source `weakField_einstein_poisson` consumes: the Einstein equation at the isolated
coupling reduces to Newton's Poisson equation with the same `G`. -/
theorem dust_traceReversed_source (G c ρ : ℝ) (hc : c ≠ 0) :
    (8 * Real.pi * G / c^4) * (ρ * c^2 / 2) = 4 * Real.pi * G * ρ / c^2 := by
  field_simp
  ring

/-- **The Schwarzschild radius in bit form**: at the isolated `G`,
`r_s = 2GM/c² = 2·M·c·sphereArea R/(ℏ·N)` — the GR horizon scale determined by the
screen's information density. -/
theorem schwarzschildRadius_bitForm (M G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hN : N = holographicBits (sphereArea R) G ℏ c) :
    schwarzschildRadius M G c = 2 * M * c * sphereArea R / (ℏ * N) := by
  unfold schwarzschildRadius
  unfold holographicBits sphereArea at hN
  rw [hN]
  unfold sphereArea
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## §B — the master theorem: the system from one identification -/

/-- **The gravitational coupling system**: from the single identification
`N = holographicBits (sphereArea R) G ℏ c` — the bit count that Certificate C proved is
*forced* by Newton's form — the entire gravitational hierarchy follows with one `G`:

1. **Newton's law**: the `G`-free entropic force takes the form `F = GMm/R²`;
2. **the Einstein coupling in bit form**: `8πG/c⁴ = 8π·(A/N)/(ℏc)`;
3. **the dust reduction**: `κ·(ρc²/2) = 4πGρ/c²` — the source
   `weakField_einstein_poisson` turns into Newton's Poisson equation `∇²Φ = 4πGρ`;
4. **the Schwarzschild radius in bit form**: `r_s = 2McA/(ℏN)`;
5. **the complete complex Einstein field equation** holds at the coupling `κ = 8πG/c⁴`
   for any curvature/matter data whose real sector is standard GR (`G_{μν} = κT_{μν}`)
   and whose entropic sector carries `Λ = κS` with the BCJ split — and conversely its
   real sector *is* standard GR. -/
theorem newtonG_establishes_gravitationalSystem {ι : Type*}
    (M c N kB m ℏ Δx G R ρ : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0)
    (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx = G * M * m / R^2
    ∧ 8 * Real.pi * G / c^4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c)
    ∧ (8 * Real.pi * G / c^4) * (ρ * c^2 / 2) = 4 * Real.pi * G * ρ / c^2
    ∧ schwarzschildRadius M G c = 2 * M * c * sphereArea R / (ℏ * N)
    ∧ ∀ (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
        (m_R m_I S₁ S₂ : ℝ),
        einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c^4)
        → Λ = (8 * Real.pi * G / c^4) • S
        → m_I * c ^ 2 = S₁ + S₂
        → CompleteComplexEinsteinFieldEquation Ric scalarR g Λ T S
            (8 * Real.pi * G / c^4) m_R m_I c S₁ S₂ := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hκ : 8 * Real.pi * G / c^4 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG) (pow_ne_zero 4 hc)
  exact ⟨(newtonG_isolated M c N kB m ℏ Δx G R hN hkB hΔx hm hM hc hℏ hG hR).mpr hbits,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits,
    dust_traceReversed_source G c ρ hc,
    schwarzschildRadius_bitForm M G ℏ c N R hℏ hc hG hR hbits,
    fun Ric scalarR g Λ T S m_R m_I S₁ S₂ hReal hImag hsplit =>
      CompleteComplexEinsteinFieldEquation.of_real_and_entropic hκ hReal hImag hsplit⟩

end Physlib.Thermodynamics.GravitationalCouplingSystem

end
