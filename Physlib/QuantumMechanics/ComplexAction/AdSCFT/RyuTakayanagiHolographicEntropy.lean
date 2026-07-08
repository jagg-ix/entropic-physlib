/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularAdS

/-!
# Ryu–Takayanagi holographic entanglement entropy

Formalizes the core of *S. Ryu, T. Takayanagi, "Holographic Derivation of Entanglement Entropy from
AdS/CFT", arXiv:hep-th/0603001v2* (Phys. Rev. Lett. 96 (2006) 181602): the **area law**

  `S_A = Area(γ_A) / (4 G_N)`   (Eq. 1.5),

where `γ_A` is the minimal bulk surface in `AdS_{d+2}` ending on `∂A` — the holographic
(Bekenstein–Hawking, Eq. 1.1) form of the entanglement entropy `S_A = −tr(ρ_A log ρ_A)` (Eq. 1.2). This
joins the modular-flow / AdS-CFT bridge `PTSymmetricQFT.ModularAdS`: the entanglement entropy is the
expectation of the **modular Hamiltonian** `K = −log ρ_A` (whose flow is the
`PTSymmetricQFT.ModularFlowBoundedOp.modularGenerator`), and the RT area is the modular-flow invariant.

* **§A — the RT formula and the Brown–Henneaux central charge** (`holographicEE`, `brownHenneaux`,
  `holographicEE_nonneg`, `brownHenneaux_third`). `S_A = Area/4G`; `c = 3R/2G` (Eq. 2.1) with
  `c/3 = R/2G`.
* **§B — the geodesic → CFT match (`d = 1`, AdS₃/CFT₂)** (`rt_cft_match`, `cftEntropy`). The geodesic length
  `L_{γ_A}` with `cosh(L/R) = 1 + 2 sinh²ρ₀ sin²(πl/L)` (Eq. 2.4) gives, in the large-cutoff limit,
  `S_A = (R/4G) log(e^{2ρ₀} sin²(πl/L)) = (c/3) log(e^{ρ₀} sin(πl/L))` (Eq. 2.5) — exactly the known CFT
  result `S_A = (c/3) log((L/πa) sin(πl/L))` (Eq. 1.3) under the UV cutoff `e^{ρ₀} ~ L/a` (Eq. 2.3).
* **§C — finite temperature** (`cftEntropyFiniteT`). `S_A(β) = (c/3) log((β/πa) sinh(πl/β))` (Eq. 2.9), the
  thermal (BTZ) entanglement entropy.
* **§D — link to the modular flow** (`rt_area_timeReversal_invariant`). The RT area is the modular-flow
  horizon area `W²` of `PTSymmetricQFT.ModularAdS`, which is **time-reversal invariant**, so the RT
  entropy is invariant under the antiunitary time reversal — the holographic entropy is a modular invariant.

## References

* S. Ryu, T. Takayanagi, arXiv:hep-th/0603001v2 (2006) — the holographic entanglement entropy area law.
* J. D. Brown, M. Henneaux (1986) — the central charge `c = 3R/2G` of `AdS₃`. P. Calabrese, J. Cardy
  (2004) — the CFT entanglement entropy `(c/3) log(...)`.
* Repo dependencies: `PTSymmetricQFT.ModularAdS` (`adSComplexCoord`, `conjFactor`,
  `adS_area_timeReversal_invariant` — the modular-flow horizon area);
  `PTSymmetricQFT.ModularFlowBoundedOp` (`modularGenerator`, the modular Hamiltonian flow).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy

open Real
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularAdS
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum

/-! ## §A — the Ryu–Takayanagi formula and the Brown–Henneaux central charge -/

/-- **[Ryu–Takayanagi Eq. 1.5] The holographic entanglement entropy** `S_A = Area(γ_A) / (4 G_N)` — the
Bekenstein–Hawking form (Eq. 1.1) of the entanglement entropy, the area of the minimal bulk surface `γ_A`
over `4 G_N`. -/
noncomputable def holographicEE (area G : ℝ) : ℝ := area / (4 * G)

/-- **[Eq. 2.1] The Brown–Henneaux central charge** `c = 3R/(2G)` of `AdS₃`. -/
noncomputable def brownHenneaux (R G : ℝ) : ℝ := 3 * R / (2 * G)

/-- The holographic entropy is non-negative (the area is non-negative). -/
theorem holographicEE_nonneg (area G : ℝ) (ha : 0 ≤ area) (hG : 0 < G) :
    0 ≤ holographicEE area G := by
  unfold holographicEE; positivity

/-- `c/3 = R/2G` — the central-charge prefactor of the CFT entanglement entropy. -/
theorem brownHenneaux_third (R G : ℝ) (hG : G ≠ 0) : brownHenneaux R G / 3 = R / (2 * G) := by
  unfold brownHenneaux; field_simp

/-! ## §B — the geodesic → CFT match (AdS₃/CFT₂) -/

/-- **[Calabrese–Cardy Eq. 1.3] The CFT₂ entanglement entropy** `S_A = (c/3) log((L/πa) sin(πl/L))`. -/
noncomputable def cftEntropy (c l L a : ℝ) : ℝ :=
  (c / 3) * Real.log (L / (π * a) * Real.sin (π * l / L))

/-- **[Ryu–Takayanagi Eqs. 2.4–2.5 → 1.3] The geodesic-length entropy reproduces the CFT result.** In the
large-cutoff limit the minimal-geodesic length gives `S_A = (R/4G) log(e^{2ρ₀} sin²(πl/L))`, which equals
the Calabrese–Cardy `(c/3) log(e^{ρ₀} sin(πl/L))` with `c = 3R/2G` — the holographic derivation of the
entanglement entropy. -/
theorem rt_cft_match (R G ρ₀ l L : ℝ) (hG : G ≠ 0) :
    holographicEE (R * Real.log (Real.exp (2 * ρ₀) * Real.sin (π * l / L) ^ 2)) G
      = (brownHenneaux R G / 3) * Real.log (Real.exp ρ₀ * Real.sin (π * l / L)) := by
  unfold holographicEE brownHenneaux
  rw [show Real.exp (2 * ρ₀) * Real.sin (π * l / L) ^ 2
        = (Real.exp ρ₀ * Real.sin (π * l / L)) ^ 2 by
    rw [mul_pow]; congr 1; rw [two_mul, Real.exp_add, sq]]
  rw [Real.log_pow]
  push_cast; field_simp; ring

/-! ## §C — finite temperature -/

/-- **[Eq. 2.9] The finite-temperature (BTZ) entanglement entropy** `S_A(β) = (c/3) log((β/πa) sinh(πl/β))`
— the thermal entanglement entropy of an interval, the AdS-black-hole (BTZ) holographic dual. -/
noncomputable def cftEntropyFiniteT (c l β a : ℝ) : ℝ :=
  (c / 3) * Real.log (β / (π * a) * Real.sinh (π * l / β))

/-! ## §D — link to the modular flow: the RT area is a modular invariant -/

/-- **[Link] The Ryu–Takayanagi entropy is a modular invariant.** The RT area is the modular-flow horizon
area `W² = ‖adSComplexCoord W θ‖²` of `PTSymmetricQFT.ModularAdS`, which is **time-reversal invariant**
(`adS_area_timeReversal_invariant`); hence the holographic entanglement entropy `S_A = W²/4G` is unchanged
by the antiunitary time reversal — the holographic entropy is a modular-flow / entanglement (RT) invariant. -/
theorem rt_area_timeReversal_invariant (W θ G : ℝ) :
    holographicEE (Complex.normSq (conjFactor true (adSComplexCoord W θ))) G
      = holographicEE (W ^ 2) G := by
  rw [adS_area_timeReversal_invariant]

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy

end
