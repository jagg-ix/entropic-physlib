/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Ryu–Takayanagi holographic entanglement entropy

The core of Ryu–Takayanagi (*Holographic Derivation of Entanglement Entropy from AdS/CFT*, Phys. Rev. Lett. 96
(2006) 181602): the **area law**

`S_A = Area(γ_A) / (4 G_N)`,

where `γ_A` is the minimal bulk surface ending on `∂A` — the Bekenstein–Hawking (holographic) form of the
entanglement entropy `S_A = −tr(ρ_A log ρ_A)`.

* the RT formula `S_A = Area/4G` (`holographicEE`) and the Brown–Henneaux central charge `c = 3R/2G`
  (`brownHenneaux`), with `c/3 = R/2G`;
* the geodesic → CFT match (AdS₃/CFT₂): the minimal-geodesic length reproduces the Calabrese–Cardy CFT₂ result
  `S_A = (c/3) log((L/πa) sin(πl/L))` (`rt_cft_match`, `cftEntropy`);
* the finite-temperature (BTZ) entanglement entropy `S_A(β) = (c/3) log((β/πa) sinh(πl/β))` (`cftEntropyFiniteT`).

References: S. Ryu, T. Takayanagi, arXiv:hep-th/0603001 (2006); J.D. Brown, M. Henneaux (1986); P. Calabrese,
J. Cardy (2004). No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

namespace Physlib.Holography.RyuTakayanagi

/-- **[Ryu–Takayanagi] The holographic entanglement entropy** `S_A = Area(γ_A) / (4 G_N)` — the Bekenstein–Hawking
form of the entanglement entropy, the minimal-surface area over `4 G_N`. -/
noncomputable def holographicEE (area G : ℝ) : ℝ := area / (4 * G)

/-- **The Brown–Henneaux central charge** `c = 3R/(2G)` of `AdS₃`. -/
noncomputable def brownHenneaux (R G : ℝ) : ℝ := 3 * R / (2 * G)

/-- **The holographic entropy is non-negative** (the area is non-negative). -/
theorem holographicEE_nonneg (area G : ℝ) (ha : 0 ≤ area) (hG : 0 < G) :
    0 ≤ holographicEE area G := by
  unfold holographicEE; positivity

/-- **The central-charge prefactor** `c/3 = R/2G` of the CFT entanglement entropy. -/
theorem brownHenneaux_third (R G : ℝ) (hG : G ≠ 0) : brownHenneaux R G / 3 = R / (2 * G) := by
  unfold brownHenneaux; field_simp

/-- **[Calabrese–Cardy] The CFT₂ entanglement entropy** `S_A = (c/3) log((L/πa) sin(πl/L))`. -/
noncomputable def cftEntropy (c l L a : ℝ) : ℝ :=
  (c / 3) * Real.log (L / (π * a) * Real.sin (π * l / L))

/-- **The geodesic-length entropy reproduces the CFT result.** In the large-cutoff limit the minimal-geodesic
length gives `S_A = (R/4G) log(e^{2ρ₀} sin²(πl/L))`, which equals the Calabrese–Cardy `(c/3) log(e^{ρ₀} sin(πl/L))`
with `c = 3R/2G` — the holographic derivation of the entanglement entropy. -/
theorem rt_cft_match (R G ρ₀ l L : ℝ) (hG : G ≠ 0) :
    holographicEE (R * Real.log (Real.exp (2 * ρ₀) * Real.sin (π * l / L) ^ 2)) G
      = (brownHenneaux R G / 3) * Real.log (Real.exp ρ₀ * Real.sin (π * l / L)) := by
  unfold holographicEE brownHenneaux
  rw [show Real.exp (2 * ρ₀) * Real.sin (π * l / L) ^ 2
        = (Real.exp ρ₀ * Real.sin (π * l / L)) ^ 2 by
    rw [mul_pow]; congr 1; rw [two_mul, Real.exp_add, sq]]
  rw [Real.log_pow]
  push_cast; field_simp; ring

/-- **[BTZ] The finite-temperature entanglement entropy** `S_A(β) = (c/3) log((β/πa) sinh(πl/β))` — the thermal
(AdS black hole / BTZ) holographic dual of an interval's entanglement entropy. -/
noncomputable def cftEntropyFiniteT (c l β a : ℝ) : ℝ :=
  (c / 3) * Real.log (β / (π * a) * Real.sinh (π * l / β))

end Physlib.Holography.RyuTakayanagi

end
