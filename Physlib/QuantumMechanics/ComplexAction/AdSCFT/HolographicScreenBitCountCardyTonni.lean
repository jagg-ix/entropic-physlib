/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow
public import Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.Relativity.Special.RindlerEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.EntropicTimeMomentumEquation

/-!
# The holographic bit count as the boundary 2D-CFT entropy (area ⟶ Cardy–Tonni)

The bit count `N` in `G = A c³/(N ℏ)` counts cells on the holographic **screen** — a codimension-two surface
whose intrinsic measure is an *area*. That `A` is an area is not incidental: by the holographic principle /
AdS/CFT the screen is the boundary of the bulk, and its information content is the entropy of the **boundary
two-dimensional conformal field theory**. The GKP–Witten path integral
`Z_grav[φ₀] = ⟨e^{∫ φ₀ O}⟩_CFT` (`AdSCFT.GKPWittenAdSCFTDictionary`) is the identity that equates the bulk
screen partition function with the boundary CFT one, so the bit count is the boundary Cardy–Tonni entanglement
entropy `S = (c/6) W` (`ConformalModularEntanglement.cardyTonniEntropy`): `c` the central charge, `W` the width
of the annulus in the CFT's 2D spacetime.  That 2D spacetime carries the Minkowski `(1,1)` signature of the
Nagao–Nielsen mass-shell invariant `(E/c)² − p² = (mc)²`
(`ComptonClock.NewtonianAndGRLimit.einstein_massShell`), so `W` is a proper interval / rapidity there, not a
raw area.

Replacing the area count by the boundary entropy expresses the geometry through the 2D-CFT data:

* `newtonG_from_cardyTonni` — Newton's constant `G = A c³/(N ℏ) = 6 A c³/(c_CFT · W · ℏ)`, the bulk area per
  unit central-charge-weighted 2D interval;
* `area_from_cardyTonni` — the screen area itself, `A = (c_CFT/6) · W · G ℏ / c³`, read off from equating the
  bulk bit count with the boundary Cardy–Tonni entropy.

So the two-dimensionality of `A` is exactly the boundary CFT living on a 2D spacetime: `A` is not a primitive
geometric datum but the central charge times the Minkowskian interval of the dual theory.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.HolographicScreenBitCountCardyTonni

open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave
open Physlib.QuantumMechanics.ComplexAction.ConformalModularEntanglement
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QuantumMechanics.ComplexAction.HolographicGravityFromModularFlow
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular

/-- **Newton's constant from the boundary 2D-CFT entropy.**  Replacing the holographic screen's bit count by
the boundary Cardy–Tonni entanglement entropy `N = (c/6) W`, the holographic Newton constant is
`G = A c³/(N ℏ) = 6 A c³/(c · W · ℏ)`: the bulk area per unit central-charge-weighted 2D interval `W`. -/
theorem newtonG_from_cardyTonni (A cLight ħ cCFT W : ℝ)
    (hcCFT : cCFT ≠ 0) (hW : W ≠ 0) (hħ : ħ ≠ 0) :
    newtonG_holographic A ħ cLight (cardyTonniEntropy cCFT W)
      = 6 * A * cLight ^ 3 / (cCFT * W * ħ) := by
  unfold newtonG_holographic cardyTonniEntropy
  field_simp

/-- **The holographic screen area from the 2D-CFT data.**  Equating the bulk bit count with the boundary
Cardy–Tonni entropy — `holographicBits A G ℏ c = (c_CFT/6) W`, the AdS/CFT (GKP–Witten path-integral)
identification — expresses the screen area through the central charge and the 2D interval:
`A = (c_CFT/6) · W · G ℏ / c³`.  The area is the boundary CFT's `central charge × Minkowskian interval`, not a
primitive geometric datum. -/
theorem area_from_cardyTonni (A G cLight ħ cCFT W : ℝ)
    (hc : cLight ≠ 0) (hG : G ≠ 0) (hħ : ħ ≠ 0)
    (hident : holographicBits A G ħ cLight = cardyTonniEntropy cCFT W) :
    A = cCFT / 6 * W * G * ħ / cLight ^ 3 := by
  unfold holographicBits cardyTonniEntropy at hident
  field_simp at hident ⊢
  linear_combination hident

/-! ### Reintroducing the Cardy–Tonni bit count into the two original equations

The holographic construction is the triangular system in the unknowns `N, G` over the given data:

* the **partition** equation `E = ½ N k_B T` (`equipartitionEnergy`), and
* the **Bekenstein** area law `N = A c³/(G ℏ)` (`holographicBits`).

Substituting the boundary bit count `N = (c_CFT/6) W` (`cardyTonniEntropy`) into each and isolating one
term at a time expresses every physical quantity through the 2D-CFT data `(c_CFT, W)`. -/

/-- **Partition equation with the Cardy–Tonni bit count.**  Distributing the screen energy over the boundary
entropy `N = (c_CFT/6) W` gives `E = ½ N k_B T = c_CFT · W · k_B · T / 12`. -/
theorem partition_energy_cardyTonni (cCFT W kB T : ℝ) :
    equipartitionEnergy (cardyTonniEntropy cCFT W) kB T = cCFT * W * kB * T / 12 := by
  unfold equipartitionEnergy cardyTonniEntropy
  ring

/-- **Screen temperature isolated from the partition equation.**  Given `E = ½ N k_B T` with
`N = (c_CFT/6) W`, the temperature is `T = 12 E/(c_CFT · W · k_B)`. -/
theorem temperature_from_cardyTonni (E cCFT W kB T : ℝ)
    (hcCFT : cCFT ≠ 0) (hW : W ≠ 0) (hkB : kB ≠ 0)
    (hpart : E = equipartitionEnergy (cardyTonniEntropy cCFT W) kB T) :
    T = 12 * E / (cCFT * W * kB) := by
  rw [partition_energy_cardyTonni] at hpart
  rw [hpart]; field_simp

/-- **The central-charge–width product isolated from the partition equation — a `G`-free datum.**  The
partition equation *alone* fixes the boundary CFT combination `c_CFT · W = 12 E/(k_B T)`: no `G` appears, so
the 2D-CFT interval content of the screen is set by its thermodynamics, before Newton's constant enters. -/
theorem centralChargeWidth_from_partition (E cCFT W kB T : ℝ)
    (hkB : kB ≠ 0) (hT : T ≠ 0)
    (hpart : E = equipartitionEnergy (cardyTonniEntropy cCFT W) kB T) :
    cCFT * W = 12 * E / (kB * T) := by
  rw [partition_energy_cardyTonni] at hpart
  rw [hpart]; field_simp

/-- **Central charge isolated from the Bekenstein area law.**  Equating the boundary entropy with the bulk
bit count, `(c_CFT/6) W = A c³/(G ℏ)`, isolates `c_CFT = 6 A c³/(G · W · ℏ)`. -/
theorem centralCharge_from_cardyTonni (A G cLight ħ cCFT W : ℝ)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) (hW : W ≠ 0)
    (hident : cardyTonniEntropy cCFT W = holographicBits A G ħ cLight) :
    cCFT = 6 * A * cLight ^ 3 / (G * W * ħ) := by
  unfold cardyTonniEntropy holographicBits at hident
  field_simp at hident ⊢
  linear_combination hident

/-- **The 2D interval isolated from the Bekenstein area law.**  Symmetrically, `(c_CFT/6) W = A c³/(G ℏ)`
isolates the boundary width `W = 6 A c³/(c_CFT · G · ℏ)`. -/
theorem width_from_cardyTonni (A G cLight ħ cCFT W : ℝ)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) (hcCFT : cCFT ≠ 0)
    (hident : cardyTonniEntropy cCFT W = holographicBits A G ħ cLight) :
    W = 6 * A * cLight ^ 3 / (cCFT * G * ħ) := by
  unfold cardyTonniEntropy holographicBits at hident
  field_simp at hident ⊢
  linear_combination hident

/-- **The partition–Bekenstein system solved in the boundary CFT variables.**  Reintroducing the Cardy–Tonni
bit count into both original equations, the triangular solution is: the **partition** equation fixes the
`G`-free CFT product `c_CFT · W = 12 E/(k_B T)`, and the **Bekenstein** equation then fixes Newton's constant
`G = 6 A c³/(c_CFT · W · ℏ)`.  Solving order `partition → (c_CFT · W) → Bekenstein → G`: the boundary interval
content is determined before `G` enters, so `G` is emergent, not assumed. -/
theorem cardyTonni_partition_bekenstein_solve
    (E T kB A cLight ħ cCFT W G : ℝ)
    (hkB : kB ≠ 0) (hT : T ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hcCFT : cCFT ≠ 0) (hW : W ≠ 0)
    (hpart : E = equipartitionEnergy (cardyTonniEntropy cCFT W) kB T)
    (hbek : cardyTonniEntropy cCFT W = holographicBits A G ħ cLight) :
    cCFT * W = 12 * E / (kB * T) ∧ G = 6 * A * cLight ^ 3 / (cCFT * W * ħ) := by
  refine ⟨centralChargeWidth_from_partition E cCFT W kB T hkB hT hpart, ?_⟩
  unfold cardyTonniEntropy holographicBits at hbek
  field_simp at hbek ⊢
  linear_combination hbek

/-- **The boundary width `W` is a boost interval, not an area.**  Two facts pin `W` to the Minkowski `(1,1)`
spacetime of the boundary CFT: the Cardy–Tonni entropy is **additive** in the interval,
`S(W₁+W₂) = S(W₁) + S(W₂)` — exactly as rapidities add under composition of boosts — while the Nagao–Nielsen
mass-shell anchor is **invariant** under that same rapidity, `(mc·cosh W)² − (mc·sinh W)² = (mc)²`
(`massShell_rapidity_invariant`).  A raw area would neither add linearly under boosts nor leave the rest mass
fixed; so `W` is a proper interval / rapidity of the 2D-CFT, and `N = (c_CFT/6) W` is a central-charge-weighted
interval rather than a geometric area. -/
theorem cardyTonni_interval_is_boost_rapidity (m cLight cCFT W₁ W₂ : ℝ) :
    cardyTonniEntropy cCFT (W₁ + W₂)
        = cardyTonniEntropy cCFT W₁ + cardyTonniEntropy cCFT W₂
      ∧ (m * cLight * Real.cosh (W₁ + W₂)) ^ 2 - (m * cLight * Real.sinh (W₁ + W₂)) ^ 2
        = (m * cLight) ^ 2 := by
  refine ⟨?_, massShell_rapidity_invariant m cLight (W₁ + W₂)⟩
  unfold cardyTonniEntropy
  ring

/-! ### Using the isolated forms: a previously inaccessible quantity, the AdS radius

The isolated central charge `c_CFT = 6 A c³/(G · W · ℏ)` (`centralCharge_from_cardyTonni`) is a *second*
determination of the boundary central charge, alongside the *geometric* Brown–Henneaux value
`c_CFT = 3R/(2G)` (`RyuTakayanagiFormulaAlgebra.brownHenneaux`, `R` the AdS radius).  Both scale as `1/G`, so
equating them **cancels Newton's constant** and fixes the AdS radius from screen data alone — a bulk geometric
length that otherwise requires the full metric. -/

/-- **The AdS radius from the screen area, with `G` cancelled.**  Equating the two determinations of the
boundary central charge — geometric `c_CFT = 3R/(2G)` and thermodynamic `c_CFT = 6 A c³/(G W ℏ)` — the common
`1/G` cancels and the AdS radius is fixed by the screen area and the boundary modular width:
`R = 4 A c³/(W ℏ)`.  No Newton constant, no bulk metric — a previously inaccessible geometric length read off
from the holographic screen and the 2D-CFT interval. -/
theorem adsRadius_from_screen_area (R G A cLight ħ cCFT W : ℝ)
    (hG : G ≠ 0) (hW : W ≠ 0) (hħ : ħ ≠ 0)
    (hBH : cCFT = brownHenneaux R G)
    (hCT : cCFT = 6 * A * cLight ^ 3 / (G * W * ħ)) :
    R = 4 * A * cLight ^ 3 / (W * ħ) := by
  have hBH' : G * cCFT = 3 * R / 2 := by
    rw [hBH]; unfold brownHenneaux; field_simp
  have hCT' : G * cCFT = 6 * A * cLight ^ 3 / (W * ħ) := by
    rw [hCT]; field_simp
  have h : 3 * R / 2 = 6 * A * cLight ^ 3 / (W * ħ) := hBH'.symm.trans hCT'
  field_simp at h ⊢
  linear_combination h / 3

/-! ### Reading the entangling-region geometry off the screen area

The vacuum modular width is the annulus width `W = log(L/ε)` (`vacuum_annulus_width`): `L` the size of the
entangling interval, `ε` the UV cutoff.  So the isolated `width_from_cardyTonni` becomes a statement about the
*physical endpoints* of the boundary interval — the entangling region's extent relative to the cutoff is
fixed by the screen area, a datum otherwise obtained only from the bulk minimal surface. -/

/-- **The entangling interval from the screen area.**  With the modular width realized as the vacuum annulus
width `log L − log ε` (`vacuum_annulus_width`), the Bekenstein identification fixes the regularized interval
`log(L/ε) = 6 A c³/(c_CFT · G · ℏ)`: the entangling-region-to-cutoff ratio is read off the area. -/
theorem entanglingInterval_from_screen_area (A G cLight ħ cCFT L ε : ℝ)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) (hcCFT : cCFT ≠ 0) (hL : L ≠ 0) (hε : ε ≠ 0)
    (hident : cardyTonniEntropy cCFT (Real.log L - Real.log ε) = holographicBits A G ħ cLight) :
    Real.log L - Real.log ε = 6 * A * cLight ^ 3 / (cCFT * G * ħ) := by
  rw [vacuum_annulus_width L ε hL hε] at hident ⊢
  exact width_from_cardyTonni A G cLight ħ cCFT (Real.log (L / ε)) hG hħ hcCFT hident

/-- **The entangling-region ratio is exponential in the area.**  Exponentiating, the interval-to-cutoff ratio
is `L/ε = exp(6 A c³/(c_CFT · G · ℏ))`: the entangling region grows exponentially in the screen area, in
central-charge / coupling units — the geometric extent of the boundary region encoded in the bulk area. -/
theorem entanglingRatio_from_screen_area (A G cLight ħ cCFT L ε : ℝ)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) (hcCFT : cCFT ≠ 0) (hLε : 0 < L / ε)
    (hident : cardyTonniEntropy cCFT (Real.log (L / ε)) = holographicBits A G ħ cLight) :
    L / ε = Real.exp (6 * A * cLight ^ 3 / (cCFT * G * ħ)) := by
  have hW := width_from_cardyTonni A G cLight ħ cCFT (Real.log (L / ε)) hG hħ hcCFT hident
  rw [← hW, Real.exp_log hLε]

/-! ### The accelerating screen: entropy production in Rindler entropic time

Because the modular width `W` is a boost rapidity (`cardyTonni_interval_is_boost_rapidity`), a screen carried
along a uniformly accelerated worldline accumulates rapidity, and its Cardy–Tonni entropy grows *linearly* in
that rapidity.  A `RindlerWorldline` (`Relativity.Special`) supplies the accumulated rapidity sweep and the
entropic time it defines, `τ = (rapidity sweep)/(2π)` (the Bisognano–Wichmann / Unruh modular temperature
`2π`).  Composing gives the screen's entropy production as a function of the accelerated observer's clock. -/

/-- **Entropy production of a boosted screen.**  Under a boost by rapidity `ξ`, the Cardy–Tonni entropy of the
screen increases by `ΔS = (c/6) ξ` — linear and additive in the rapidity, as a proper interval and not an
area would behave. -/
theorem screen_entropy_boost_increment (cCFT W ξ : ℝ) :
    cardyTonniEntropy cCFT (W + ξ) - cardyTonniEntropy cCFT W = cCFT / 6 * ξ := by
  unfold cardyTonniEntropy
  ring

/-- **Entropy production per unit Rindler entropic time.**  For a screen carried along a uniformly accelerated
worldline `Wr`, feeding its accumulated rapidity sweep into the modular width and rewriting the sweep through
`τ = (rapidity sweep)/(2π)` gives `ΔS = (π c/3) · τ`: the boundary CFT entropy produced grows at the fixed
rate `π c/3` per unit of the accelerated observer's entropic time — the Unruh face of the holographic screen,
the modular temperature `2π` converting rapidity into clock time. -/
theorem screen_entropy_production_rindler_time
    (Wr : Physlib.Relativity.Special.RindlerWorldline) (cCFT W₀ : ℝ) :
    cardyTonniEntropy cCFT (W₀ + Wr.rapiditySweep) - cardyTonniEntropy cCFT W₀
      = Real.pi * cCFT / 3 * Wr.entropicTime := by
  rw [Wr.entropicTime_eq_rapiditySweep_over_two_pi]
  unfold cardyTonniEntropy
  field_simp [Real.pi_ne_zero]
  ring

/-! ### The central charge from calorimetry — gravity-free

The `G`-free `centralChargeWidth_from_partition` (`c_CFT · W = 12 E/(k_B T)`) is a determination of the
boundary central charge from *thermodynamic data alone* — the screen energy `E` and temperature `T` — with no
Newton constant, no area, and no bulk metric.  It is the statement that the boundary Cardy–Tonni entropy is
exactly the screen's calorimetric bit count `N = 2E/(k_B T)` (`screenBitCount`), the central charge acting as
the conversion between the 2D interval `W` and the counted quanta.  Contrast the standard Brown–Henneaux route
`c = 3R/2G`, which needs the AdS radius and Newton's constant: the same central charge is here fixed without
either. -/

/-- **Bulk–boundary entropy match, gravity-free.**  When the screen energy is distributed over the boundary
entropy (`partition`), the Cardy–Tonni entanglement entropy equals the screen's thermodynamic bit count,
`(c_CFT/6) W = 2E/(k_B T)` (`screenBitCount`).  Both sides are computed without `G`, area, or metric — the
boundary CFT entropy *is* the calorimetric bit count. -/
theorem boundaryEntropy_eq_screenBitCount (E cCFT W kB T : ℝ)
    (hkB : kB ≠ 0) (hT : T ≠ 0)
    (hpart : E = equipartitionEnergy (cardyTonniEntropy cCFT W) kB T) :
    cardyTonniEntropy cCFT W = screenBitCount E kB T := by
  rw [partition_energy_cardyTonni] at hpart
  unfold cardyTonniEntropy screenBitCount
  rw [hpart]; field_simp; ring

/-- **The central charge from calorimetry.**  Isolating the central charge from the same partition equation,
`c_CFT = 12 E/(W · k_B · T)`: the boundary central charge is fixed by the screen's energy, temperature and
modular width alone.  No `G`, no area, no AdS radius appears — a purely calorimetric determination of the
CFT's central charge, decoupled from the gravitational sector. -/
theorem centralCharge_from_calorimetry (E cCFT W kB T : ℝ)
    (hW : W ≠ 0) (hkB : kB ≠ 0) (hT : T ≠ 0)
    (hpart : E = equipartitionEnergy (cardyTonniEntropy cCFT W) kB T) :
    cCFT = 12 * E / (W * kB * T) := by
  have h := centralChargeWidth_from_partition E cCFT W kB T hkB hT hpart
  field_simp at h ⊢
  linear_combination h

/-! ### Finite temperature: the thermal entangling geometry from the screen area

At boundary inverse temperature `β` the modular width is the **thermal** annulus width
`W_β = log((e^{2πL/β} − 1)/(e^{2πε/β} − 1))` (`thermalEntanglementEntropy`, `thermal_annulus_width`), which is
`cardyTonniEntropy c_CFT W_β` by definition.  Every isolated form therefore extends to finite temperature by
taking `W := W_β`; the results below read the finite-temperature entangling geometry off the screen area and
identify the thermal CFT entropy with the screen's bit count. -/

/-- **The thermal entangling width from the screen area.**  At inverse temperature `β`, the Bekenstein
identification fixes the thermal annulus width `log((e^{2πL/β} − 1)/(e^{2πε/β} − 1)) = 6 A c³/(c_CFT · G · ℏ)`:
the finite-temperature entangling geometry is read off the area, the thermal exponentials deforming the
vacuum `log(L/ε)`. -/
theorem thermalEntanglingWidth_from_screen_area (A G cLight ħ cCFT β L ε : ℝ)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) (hcCFT : cCFT ≠ 0)
    (hL : Real.exp (2 * Real.pi * L / β) - 1 ≠ 0) (hε : Real.exp (2 * Real.pi * ε / β) - 1 ≠ 0)
    (hident : cardyTonniEntropy cCFT
        (Real.log (Real.exp (2 * Real.pi * L / β) - 1) - Real.log (Real.exp (2 * Real.pi * ε / β) - 1))
        = holographicBits A G ħ cLight) :
    Real.log (Real.exp (2 * Real.pi * L / β) - 1) - Real.log (Real.exp (2 * Real.pi * ε / β) - 1)
      = 6 * A * cLight ^ 3 / (cCFT * G * ħ) := by
  rw [thermal_annulus_width β L ε hL hε] at hident ⊢
  exact width_from_cardyTonni A G cLight ħ cCFT
    (Real.log ((Real.exp (2 * Real.pi * L / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1)))
    hG hħ hcCFT hident

/-- **The thermal entangling ratio is exponential in the area.**  Exponentiating, the thermal region-to-cutoff
ratio is `(e^{2πL/β} − 1)/(e^{2πε/β} − 1) = exp(6 A c³/(c_CFT · G · ℏ))` — the finite-temperature analogue of
`L/ε = exp(…)`, recovering the vacuum form as `β → ∞`. -/
theorem thermalEntanglingRatio_from_screen_area (A G cLight ħ cCFT β L ε : ℝ)
    (hG : G ≠ 0) (hħ : ħ ≠ 0) (hcCFT : cCFT ≠ 0)
    (hpos : 0 < (Real.exp (2 * Real.pi * L / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1))
    (hident : cardyTonniEntropy cCFT
        (Real.log ((Real.exp (2 * Real.pi * L / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1)))
        = holographicBits A G ħ cLight) :
    (Real.exp (2 * Real.pi * L / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1)
      = Real.exp (6 * A * cLight ^ 3 / (cCFT * G * ħ)) := by
  have hW := width_from_cardyTonni A G cLight ħ cCFT
    (Real.log ((Real.exp (2 * Real.pi * L / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1)))
    hG hħ hcCFT hident
  rw [← hW, Real.exp_log hpos]

/-- **The thermal CFT entropy is the screen bit count.**  When the screen energy is distributed over the
thermal entanglement entropy (`partition`), that entropy equals the screen's calorimetric bit count
`N = 2E/(k_B T)` (`screenBitCount`) — the finite-temperature bulk–boundary match, `G`-free. -/
theorem thermalEntropy_eq_screenBitCount (E cCFT β L ε kB T : ℝ)
    (hkB : kB ≠ 0) (hT : T ≠ 0)
    (hpart : E = equipartitionEnergy (thermalEntanglementEntropy cCFT β L ε) kB T) :
    thermalEntanglementEntropy cCFT β L ε = screenBitCount E kB T := by
  unfold thermalEntanglementEntropy at hpart ⊢
  exact boundaryEntropy_eq_screenBitCount E cCFT _ kB T hkB hT hpart

/-! ### The dictionary is jointly satisfiable — a concrete witness

Every theorem above is a *conditional* identity, discharged only if its structural antecedents can be met at
once.  To confirm they are not vacuously conditional, one explicit configuration satisfies the partition,
Bekenstein, Brown–Henneaux and annulus-width equations simultaneously.  In natural units
`k_B = T = c = ℏ = G = 1` with unit modular width `W = 1` and central charge `c_CFT = 12`, the equations force
`E = 1`, `A = 2`, `R = 8`, cutoff `ε = 1`, interval `L = e`; every nonzero-denominator side-condition holds.
So the whole hypothesis system is inhabited, and the flagship consequences (AdS radius `R = 8`, calorimetric
`c_CFT = 12`, entangling ratio `L/ε = e`) are determinate values of a realizable configuration, not empty
implications. -/
theorem screenDictionary_jointly_satisfiable :
    ∃ E T kB A cLight ħ cCFT W G R L ε : ℝ,
      E = equipartitionEnergy (cardyTonniEntropy cCFT W) kB T
        ∧ cardyTonniEntropy cCFT W = holographicBits A G ħ cLight
        ∧ cCFT = brownHenneaux R G
        ∧ W = Real.log (L / ε)
        ∧ kB ≠ 0 ∧ T ≠ 0 ∧ ħ ≠ 0 ∧ G ≠ 0 ∧ W ≠ 0 ∧ cCFT ≠ 0 := by
  refine ⟨1, 1, 1, 2, 1, 1, 12, 1, 1, 8, Real.exp 1, 1, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold equipartitionEnergy cardyTonniEntropy; norm_num
  · unfold cardyTonniEntropy holographicBits; norm_num
  · unfold brownHenneaux; norm_num
  · rw [div_one, Real.log_exp]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-! ### High temperature: the extensive Cardy entropy density

The thermal entropy `S_β(L) = (c/6) log((e^{2πL/β} − 1)/(e^{2πε/β} − 1))` is, unlike the vacuum's logarithmic
`(c/6) log(L/ε)`, *extensive* — it grows with the interval size `L`.  Its exact rate is the entropy density
`dS/dL = (π c/3β) · e^{2πL/β}/(e^{2πL/β} − 1) = (π c/3β)/(1 − e^{−2πL/β})`, which decreases to the constant
`π c/3β` as `L → ∞`: the Cardy thermal entropy density.  Its coefficient `π c/3` is exactly the
accelerating-screen entropy-production rate of `screen_entropy_production_rindler_time` — the Unruh
temperature of the boosted screen is the boundary CFT's own temperature. -/

/-- **The exact thermal entropy density.**  Differentiating the thermal entropy in the interval size `L`, the
Cardy–Tonni entropy density is `dS/dL = (π c/3β) · e^{2πL/β}/(e^{2πL/β} − 1)` — the extensive rate at which
boundary entanglement entropy accrues per unit interval at inverse temperature `β`. -/
theorem thermalEntropy_hasDerivAt (cCFT β ε L : ℝ) (hβ : β ≠ 0)
    (hL : Real.exp (2 * Real.pi * L / β) - 1 ≠ 0) (hε : Real.exp (2 * Real.pi * ε / β) - 1 ≠ 0) :
    HasDerivAt (fun x => thermalEntanglementEntropy cCFT β x ε)
      (Real.pi * cCFT / (3 * β)
        * (Real.exp (2 * Real.pi * L / β) / (Real.exp (2 * Real.pi * L / β) - 1))) L := by
  unfold thermalEntanglementEntropy cardyTonniEntropy
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * x / β) (2 * Real.pi / β) L := by
    simpa using ((hasDerivAt_id L).const_mul (2 * Real.pi)).div_const β
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (2 * Real.pi * x / β))
      (Real.exp (2 * Real.pi * L / β) * (2 * Real.pi / β)) L := hlin.exp
  have hdiv : HasDerivAt
      (fun x : ℝ => (Real.exp (2 * Real.pi * x / β) - 1) / (Real.exp (2 * Real.pi * ε / β) - 1))
      (Real.exp (2 * Real.pi * L / β) * (2 * Real.pi / β) / (Real.exp (2 * Real.pi * ε / β) - 1)) L :=
    (hexp.sub_const 1).div_const _
  have hlog := hdiv.log (div_ne_zero hL hε)
  have hfin := hlog.const_mul (cCFT / 6)
  rw [div_div_div_cancel_right₀ hε] at hfin
  have heq : Real.pi * cCFT / (3 * β)
        * (Real.exp (2 * Real.pi * L / β) / (Real.exp (2 * Real.pi * L / β) - 1))
      = cCFT / 6 * (Real.exp (2 * Real.pi * L / β) * (2 * Real.pi / β)
          / (Real.exp (2 * Real.pi * L / β) - 1)) := by
    field_simp
    ring
  rw [heq]
  exact hfin

/-- **The extensive Cardy entropy density.**  As the interval grows (`L → ∞`) the thermal entropy density
approaches the constant `π c/3β`: the boundary CFT entropy is *extensive*, accruing at the fixed Cardy rate
`π c/3` per unit interval and inverse temperature — the same `π c/3` as the accelerating-screen
production rate `screen_entropy_production_rindler_time`, so the Unruh temperature of the boosted screen is the
boundary CFT temperature. -/
theorem thermalEntropyDensity_tendsto (cCFT β : ℝ) (hβ : 0 < β) :
    Filter.Tendsto
      (fun L => Real.pi * cCFT / (3 * β)
        * (Real.exp (2 * Real.pi * L / β) / (Real.exp (2 * Real.pi * L / β) - 1)))
      Filter.atTop (nhds (Real.pi * cCFT / (3 * β))) := by
  have hu : Filter.Tendsto (fun L : ℝ => 2 * Real.pi * L / β) Filter.atTop Filter.atTop := by
    simpa using (Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      Filter.tendsto_id).atTop_div_const hβ
  have hexp : Filter.Tendsto (fun L : ℝ => Real.exp (2 * Real.pi * L / β)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hu
  have hfac : Filter.Tendsto
      (fun L : ℝ => Real.exp (2 * Real.pi * L / β) / (Real.exp (2 * Real.pi * L / β) - 1))
      Filter.atTop (nhds 1) := by
    have hneg : Filter.Tendsto (fun L : ℝ => (-1 : ℝ) * (2 * Real.pi * L / β))
        Filter.atTop Filter.atBot := Filter.Tendsto.const_mul_atTop_of_neg (by norm_num) hu
    have hexpneg : Filter.Tendsto (fun L : ℝ => Real.exp ((-1 : ℝ) * (2 * Real.pi * L / β)))
        Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
    have hden : Filter.Tendsto (fun L : ℝ => 1 - Real.exp ((-1 : ℝ) * (2 * Real.pi * L / β)))
        Filter.atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hexpneg
    rw [sub_zero] at hden
    have hinv1 : Filter.Tendsto (fun L : ℝ => (1 - Real.exp ((-1 : ℝ) * (2 * Real.pi * L / β)))⁻¹)
        Filter.atTop (nhds (1 : ℝ)⁻¹) := hden.inv₀ (by norm_num)
    rw [inv_one] at hinv1
    refine hinv1.congr' ?_
    filter_upwards [hexp.eventually_gt_atTop 1] with L hL1
    have hne : Real.exp (2 * Real.pi * L / β) - 1 ≠ 0 := ne_of_gt (by linarith)
    have hpos : Real.exp (2 * Real.pi * L / β) ≠ 0 := (Real.exp_pos _).ne'
    rw [neg_one_mul, Real.exp_neg]
    field_simp
  simpa using hfac.const_mul (Real.pi * cCFT / (3 * β))

/-! ### One rate: the boosted screen's Unruh temperature is the boundary CFT temperature

The accelerating screen and the boundary thermal state produce Cardy–Tonni entropy at the same rate `c/6` per
unit rapidity.  Converted to each one's extensive clock — Rindler entropic time `τ` for the screen, interval
size `L` for the thermal state — the rates are `π c/3` (`accelerating_screen_rate`) and `π c/3β`
(`thermalEntropyDensity_tendsto`).  They coincide exactly at `β = 1`, the inverse temperature at which the
thermal state accumulates rapidity per unit length at the same `2π` rate that the boosted screen accumulates
it per unit entropic time.  That common value is the single production rate: the boosted screen's Unruh
temperature is the boundary CFT's own temperature. -/

/-- **The accelerating-screen entropy-production rate.**  Per unit Rindler entropic time, the boosted screen
produces boundary entropy at the fixed rate `π c/3` — `screen_entropy_production_rindler_time` divided by the
elapsed entropic time. -/
theorem accelerating_screen_rate (Wr : Physlib.Relativity.Special.RindlerWorldline) (cCFT W₀ : ℝ)
    (hτ : Wr.entropicTime ≠ 0) :
    (cardyTonniEntropy cCFT (W₀ + Wr.rapiditySweep) - cardyTonniEntropy cCFT W₀) / Wr.entropicTime
      = Real.pi * cCFT / 3 := by
  rw [screen_entropy_production_rindler_time, mul_div_assoc, div_self hτ, mul_one]

/-- **The two rates coincide exactly at the matched temperature.**  The accelerating-screen rate `π c/3` and
the thermal entropy-density limit `π c/3β` agree if and only if the boundary inverse temperature is `β = 1`:
the boosted screen and the thermal state produce entropy at one rate precisely when their temperatures
coincide — the boosted screen's Unruh temperature is the boundary CFT's own. -/
theorem boosted_screen_temperature_is_cft_temperature (cCFT β : ℝ) (hcCFT : cCFT ≠ 0) (hβ : β ≠ 0) :
    Real.pi * cCFT / 3 = Real.pi * cCFT / (3 * β) ↔ β = 1 := by
  rw [div_eq_div_iff (by norm_num : (3 : ℝ) ≠ 0) (mul_ne_zero (by norm_num) hβ)]
  constructor
  · intro h
    have h3 : (3 : ℝ) * β = 3 := mul_left_cancel₀ (mul_ne_zero Real.pi_ne_zero hcCFT) h
    linarith
  · rintro rfl
    ring

/-- **One rate.**  At the matched inverse temperature `β = 1`, the thermal entropy density converges, as the
interval grows, to exactly the accelerating-screen entropy-production rate per unit Rindler entropic time.
The thermal state's Cardy entropy production and the boosted screen's Unruh entropy production are the single
rate `π c/3` — the boundary CFT temperature is the Unruh temperature of the boosted screen. -/
theorem thermalDensity_tendsto_boostedScreenRate
    (Wr : Physlib.Relativity.Special.RindlerWorldline) (cCFT W₀ : ℝ) (hτ : Wr.entropicTime ≠ 0) :
    Filter.Tendsto
      (fun L => Real.pi * cCFT / 3
        * (Real.exp (2 * Real.pi * L) / (Real.exp (2 * Real.pi * L) - 1)))
      Filter.atTop
      (nhds ((cardyTonniEntropy cCFT (W₀ + Wr.rapiditySweep) - cardyTonniEntropy cCFT W₀)
        / Wr.entropicTime)) := by
  rw [accelerating_screen_rate Wr cCFT W₀ hτ]
  simpa using thermalEntropyDensity_tendsto cCFT 1 one_pos

/-! ### Linking to the quantized time and quantized gravity of the modular flow

The boundary Cardy–Tonni bit count is the same holographic bit count that `HolographicGravityFromModularFlow`
quantizes.  There, one Tomita–Takesaki modular flow yields **both** faces:

* **quantized gravity** — the Bekenstein–Hawking horizon entropy `S = A c³/(4Gℏ)` counts area in Compton cells
  `A/(4λ_C²)` at the holographic `G = ℏc/m²`, whose coupling is `ℏ·(c/m²)` (`holographicG_div_hbar`), so
  gravity is *intrinsically* `ℏ`-linear rather than a field quantized on top of `ℏ`;
* **quantized time** — the modular generator is `iℏ` times the von Neumann state rate,
  `δ_H = (iℏ)·(dρ/dt)` (`modularGenerator_eq_smul_vonNeumannGen`), the operator face of the same
  time–energy quantum `ℏ` carried by the Fujiwara CCR `[T,H] = iℏ`.

The boundary Cardy–Tonni entropy is `holographicBits` (the Bekenstein bit count) and its production is clocked
by that modular flow, so it links to both. -/

/-- **The boundary Cardy–Tonni entropy counts the horizon area in quantum-gravity Compton cells.**  When the
boundary bit count is the holographic bit count at the quantized-gravity value `G = ℏc/m²`, the Cardy–Tonni
entropy equals the horizon area measured in Compton cells `λ_C² = ℏ²/(m²c²)` — four times the
Bekenstein–Hawking entropy `A/(4λ_C²)` (`bekensteinHawking_holographicG_eq_comptonCells`), the boundary CFT
form of the quantized-gravity horizon count. -/
theorem cardyTonni_counts_comptonCells (A m cLight ħ cCFT W : ℝ)
    (hm : m ≠ 0) (hc : cLight ≠ 0) (hħ : ħ ≠ 0)
    (hident : cardyTonniEntropy cCFT W = holographicBits A (holographicG m cLight ħ) ħ cLight) :
    cardyTonniEntropy cCFT W = A / comptonWavelength m cLight ħ ^ 2 := by
  rw [hident]
  unfold holographicBits holographicG comptonWavelength
  field_simp

/-- **The boundary Cardy–Tonni bit count links the modular flow's quantized time and quantized gravity.**  One
Tomita–Takesaki modular flow carries both: the modular generator is `iℏ` times the von Neumann state rate
(`δ_H = (iℏ)·(dρ/dt)` — the quantized-time face, the operator form of `[T,H] = iℏ`), and the boundary
Cardy–Tonni entropy counts the horizon area in Compton cells (the quantized-gravity face,
`4×` Bekenstein–Hawking).  The same boundary bit count that quantizes the area is clocked by the modular time
that quantizes the flow. -/
theorem cardyTonni_links_quantized_time_and_gravity
    {n : Type*} [Fintype n] [DecidableEq n] (ℏc : ℂ) (hℏc : ℏc ≠ 0) (H ρ : Matrix n n ℂ)
    (A m cLight ħ cCFT W : ℝ) (hm : m ≠ 0) (hc : cLight ≠ 0) (hħ : ħ ≠ 0)
    (hident : cardyTonniEntropy cCFT W = holographicBits A (holographicG m cLight ħ) ħ cLight) :
    modularGenerator H ρ = (Complex.I * ℏc) • PeriodicQHermitian.Basic.vonNeumannGen ℏc H ρ
      ∧ cardyTonniEntropy cCFT W = A / comptonWavelength m cLight ħ ^ 2 :=
  ⟨(modularFlow_holographicG_gravity_synthesis ℏc hℏc H ρ A m cLight ħ hm hc hħ).1,
    cardyTonni_counts_comptonCells A m cLight ħ cCFT W hm hc hħ hident⟩

/-! ### Three rapidity clocks, one Cardy rate

Three physically distinct clocks have appeared in this arc, each an *additive rapidity*: the **Rindler boost
sweep** of an accelerated screen (`RindlerWorldline.rapiditySweep`), the **dilaton-flow rapidity** between
turbulent epochs (`EntropicTimeMomentumEquation.clockRapidity`, `w = log(Ω₁/Ω₂)`), and the **modular scale
width** of the GKP–Witten annulus (`W = log(L/ε)`, `vacuum_annulus_width`).  The boundary CFT prices all three
at the *single* Cardy rate `c/6` per unit rapidity: the entropy increment along a boost, along the dilaton
flow, and across a scale interval are the same functional (`three_rapidity_clocks_one_cardy_rate`).  One
structure, three groups — Lorentz boost, dilation, scale — one rate. -/

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.EntropicTimeMomentumEquation

/-- **Three rapidity clocks, one Cardy rate.**  The boundary entropy increment is `c/6` per unit rapidity for
all three clocks: (i) the Rindler boost sweep, `S(W₀+ξ) − S(W₀) = (c/6)·ξ`; (ii) the dilaton flow between
turbulent epochs, `S(w₁₃) − S(w₁₂) = S(w₂₃)` — the increment is itself a Cardy entropy of the incremental
rapidity; (iii) the modular scale width, `S(log L) − S(log ε) = S(log(L/ε))`.  Boost, dilation, and scale are
charged by the boundary at the one rate. -/
theorem three_rapidity_clocks_one_cardy_rate
    (Wr : Physlib.Relativity.Special.RindlerWorldline) (cCFT W₀ Ω₁ Ω₂ Ω₃ L ε : ℝ)
    (h₁ : Ω₁ ≠ 0) (h₂ : Ω₂ ≠ 0) (h₃ : Ω₃ ≠ 0) (hL : L ≠ 0) (hε : ε ≠ 0) :
    cardyTonniEntropy cCFT (W₀ + Wr.rapiditySweep) - cardyTonniEntropy cCFT W₀
        = cCFT / 6 * Wr.rapiditySweep
      ∧ cardyTonniEntropy cCFT (clockRapidity Ω₁ Ω₃) - cardyTonniEntropy cCFT (clockRapidity Ω₁ Ω₂)
        = cardyTonniEntropy cCFT (clockRapidity Ω₂ Ω₃)
      ∧ cardyTonniEntropy cCFT (Real.log L) - cardyTonniEntropy cCFT (Real.log ε)
        = cardyTonniEntropy cCFT (Real.log (L / ε)) := by
  refine ⟨screen_entropy_boost_increment cCFT W₀ Wr.rapiditySweep, ?_, ?_⟩
  · have h := cardyTonni_clockRapidity_additive cCFT Ω₁ Ω₂ Ω₃ h₁ h₂ h₃
    linarith
  · unfold cardyTonniEntropy
    rw [Real.log_div hL hε]
    ring

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.HolographicScreenBitCountCardyTonni

end
