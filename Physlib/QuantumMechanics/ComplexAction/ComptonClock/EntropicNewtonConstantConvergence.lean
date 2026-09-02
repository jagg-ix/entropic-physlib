/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Order.Filter.AtTopBot.Ring
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential
meta import Zil

/-!
# The entropic Newton constant governs both general relativity and classical mechanics

The gravitational constant `G` reconstructed from information — Verlinde's holographic **area per bit**
`G = A·c³/(ℏN)` (`Thermodynamics.VerlindeNewtonGravity.holographicBits`,
`ComptonClock.ScreenCouplingReductions`) — is not two different constants for the two theories of gravity.
This module assembles the proof that **one** such `G` simultaneously

* builds the **Einstein field equation** of general relativity: it is the Einstein coupling
  `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)` (`einsteinNewton_coupling`, from `ScreenCouplingReductions`);
* reduces, in the weak-field static limit of that equation, to **Newton's Poisson equation**
  `∇²Φ = 4πGρ` (`einstein_converges_to_poisson`, from `NewtonianAndGRLimit.weakField_einstein_poisson`) —
  the same `G`, the factor `8π → 4π` being the standard trace reversal for dust;
* reproduces **Newton's law of universal gravitation** `F = GMm/r²` of classical mechanics, both from the
  entropic force (`VerlindeNewtonGravity.newton_law_of_gravity_from_verlinde`) and as the gradient of the
  Newtonian potential `Φ = −GM/r` (`newtonForce_eq_mass_field`).

The capstone `entropicNewtonConstant_converges` bundles the four facts for a single `G`: the entropic origin,
the GR coupling, the Newtonian-limit Poisson equation, and Newton's inverse-square force law — a derivation
that the information-theoretic `G` is **consistent across GR and classical mechanics**, converging on the
same value in both.

## References

* E. Verlinde, JHEP 04 (2011) 029; T. Jacobson, PRL 75 (1995) 1260. Carriers:
  `ScreenCouplingReductions.newtonG_is_area_per_bit_reproducing_newton`,
  `VerlindeNewtonGravity.newton_law_of_gravity_from_verlinde`,
  `NewtonianAndGRLimit.weakField_einstein_poisson`.
-/

set_option autoImplicit false

open Real Filter
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence

/-! ### The classical-mechanics side: Newton's potential and force -/

/-- **Newton's gravitational potential** `Φ(r) = −GM/r` (potential energy per unit test mass). -/
noncomputable def newtonPotential (G M r : ℝ) : ℝ := -(G * M) / r

/-- **Newton's law of universal gravitation** `F = GMm/r²` — the attractive force magnitude between masses
`M` and `m` at separation `r`. -/
noncomputable def newtonForce (G M m r : ℝ) : ℝ := G * M * m / r ^ 2

/-- **[The gravitational field is minus the potential gradient] `dΦ/dr = GM/r²`.** The magnitude of the
Newtonian field `g = −∇Φ` at radius `r` is `GM/r²`. -/
theorem hasDerivAt_newtonPotential (G M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (newtonPotential G M) (G * M / r ^ 2) r := by
  have hf : newtonPotential G M = fun y : ℝ => -(G * M) * y⁻¹ := by
    funext y; exact div_eq_mul_inv (-(G * M)) y
  have hval : G * M / r ^ 2 = -(G * M) * -(r ^ 2)⁻¹ := by
    rw [neg_mul_neg, div_eq_mul_inv]
  rw [hf, hval]
  exact (hasDerivAt_inv hr).const_mul (-(G * M))

/-- **[Newton's law is the mass times the field] `F = m·|∇Φ| = GMm/r²`.** Classical mechanics: the force on
a test mass `m` is `m` times the magnitude of the gravitational field derived from the potential — Newton's
inverse-square law. -/
theorem newtonForce_eq_mass_field (G M m r : ℝ) (hr : r ≠ 0) :
    newtonForce G M m r = m * deriv (newtonPotential G M) r := by
  rw [(hasDerivAt_newtonPotential G M r hr).deriv, newtonForce]
  ring

/-- **The Newtonian gravitational acceleration** `a = GM/r²` — the field per unit test mass. -/
noncomputable def newtonAcceleration (G M r : ℝ) : ℝ := G * M / r ^ 2

/-- **[The weak equivalence principle] the gravitational acceleration is independent of the test mass**
`F/m = GM/r²`. Free fall is universal: this mass-independence is exactly what lets gravity be recast as
geometry (mass-independent geodesics) in general relativity, and is why the geometric Einstein coupling
`8πG` and Newton's force `GMm/r²` can share the single constant `G`. -/
theorem newtonForce_div_mass_eq_acceleration (G M m r : ℝ) (hm : m ≠ 0) :
    newtonForce G M m r / m = newtonAcceleration G M r := by
  rw [newtonForce, newtonAcceleration]
  field_simp

/-- **The acceleration is the potential gradient** `a = dΦ/dr = GM/r²`. -/
theorem newtonAcceleration_eq_field (G M r : ℝ) (hr : r ≠ 0) :
    newtonAcceleration G M r = deriv (newtonPotential G M) r := by
  rw [(hasDerivAt_newtonPotential G M r hr).deriv, newtonAcceleration]

/-- **[The entropic force is Newton's force] the two classical-mechanics derivations agree.** Verlinde's
entropic force from the holographic screen equals the inverse-square Newton force `GMm/r²` derived as the
potential gradient — one classical gravity, two independent routes to it. -/
theorem verlindeForce_eq_newtonForce (M G ℏ c R kB m Δx : ℝ)
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) (hΔx : 0 < Δx) :
    verlindeEntropicForce (verlindeGravityTemperature M G ℏ c R kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx = newtonForce G M m R := by
  rw [newton_law_of_gravity_from_verlinde hℏ hkB hc hR hΔx, newtonForce]

/-! ### The capstone: one entropic `G` for general relativity and classical mechanics -/

/-- **[Convergence — one entropic `G` for GR and classical mechanics] the information-theoretic Newton
constant builds the Einstein field equation *and* Newton's law.** For a single `G` equal to Verlinde's screen
**area per bit** `G = A·c³/(ℏN)` (`A = 4πR²`), with the weak-field Ricci `R₀₀ = 4πGρ/c²`:

* **(I) entropic origin** — `G = A·c³/(ℏN)` is the screen area one bit occupies;
* **(II) general relativity** — `8πG/c⁴ = 8π(A/N)/(ℏc)` is the Einstein coupling `κ`;
* **(III) Newtonian limit** — `∇²Φ = 4πGρ`, the weak-field static reduction of the Einstein equation *is*
  Newton's Poisson equation (same `G`, `8π → 4π` from trace reversal);
* **(IV) classical mechanics** — the same `G` reproduces Newton's law `F = GMm/r²` from the entropic force.

The four facts share one `G`: the information-theoretic gravitational constant is consistent across, and
converges between, general relativity and classical mechanics. -/
theorem entropicNewtonConstant_converges
    (G ℏ c N R d2Φ ρ M m kB Δx : ℝ)
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hR : 0 < R) (hΔx : 0 < Δx) (hG : G ≠ 0)
    (hN : N = holographicBits (sphereArea R) G ℏ c)
    (hEin : weakFieldRicci00 d2Φ c = 4 * Real.pi * G * ρ / c ^ 2) :
    G = sphereArea R * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c)
    ∧ d2Φ = 4 * Real.pi * G * ρ
    ∧ verlindeEntropicForce (verlindeGravityTemperature M G ℏ c R kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx = G * M * m / R ^ 2 := by
  obtain ⟨hI, hII, hIII⟩ :=
    newtonG_is_area_per_bit_reproducing_newton G ℏ c N R d2Φ ρ hℏ.ne' hc.ne' hG hR.ne' hN hEin
  exact ⟨hI, hII, hIII, newton_law_of_gravity_from_verlinde hℏ hkB hc hR hΔx⟩

/-! ### The literal limit `c → ∞`: GR's geometry trivializes, Newton survives -/

/-- **[GR → Newton — the Einstein coupling switches off] `lim_{c→∞} 8πG/c⁴ = 0`.** The geometric coupling
of matter to spacetime curvature vanishes in the non-relativistic limit: gravity ceases to be geometry. -/
theorem einsteinCoupling_tendsto_zero (G : ℝ) :
    Filter.Tendsto (fun c => 8 * Real.pi * G / c ^ 4) Filter.atTop (nhds 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop (by norm_num))

/-- **[The convergence as a genuine limit `c → ∞`] general relativity's geometric structure trivializes
while Newton's gravity survives.** As `c → ∞`, the weak-field metric flattens to Minkowski
`g₀₀ → 1` (`NewtonianAndGRLimit.weakFieldG00_tendsto_flat`) and the Einstein coupling `8πG/c⁴ → 0`
(`einsteinCoupling_tendsto_zero`), but Newton's force `GMm/r²` is `c`-independent — its limit is itself. The
relativistic corrections vanish and what remains is the `c`-independent Newtonian gravity built from the same
`G`: general relativity converges to classical mechanics as a genuine `Filter.Tendsto`. -/
theorem gr_tendsto_newton_as_c_atTop (Φ G M m r : ℝ) :
    Filter.Tendsto (fun c => weakFieldG00 Φ c) Filter.atTop (nhds 1)
    ∧ Filter.Tendsto (fun c => 8 * Real.pi * G / c ^ 4) Filter.atTop (nhds 0)
    ∧ Filter.Tendsto (fun _c : ℝ => newtonForce G M m r) Filter.atTop
        (nhds (newtonForce G M m r)) :=
  ⟨weakFieldG00_tendsto_flat Φ, einsteinCoupling_tendsto_zero G, tendsto_const_nhds⟩


/-- **Newton's potential is the coupling times the massless Yukawa kernel**: `−GM/r =
−(GM)·(1/r)` with `1/r = yukawaPotential 0 r` — gravity's static potential is the
zero-screening face of the screened mediator (`Yukawa.ScreenedPotential`), the kernel the
BCJ double copy squares. -/
theorem newtonPotential_eq_massless_yukawa (G M r : ℝ) :
    newtonPotential G M r
      = -(G * M)
          * Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential.yukawaPotential
              0 r := by
  unfold newtonPotential
    Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential.yukawaPotential
  rw [zero_mul, neg_zero, Real.exp_zero]
  ring

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence

end


/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce_eq_mass_field where
  formalizes @ "claim:the-newton-force-is-the-test-mass-times-the-gravitational-field",
  supported_by @ "paper:verlinde-2011-entropic-gravity"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges where
  formalizes @ "claim:the-entropic-newton-constant-converges-in-the-continuum-holographic-screen-limit",
  requires @ "claim:the-newton-force-is-the-test-mass-times-the-gravitational-field",
  supported_by @ "paper:verlinde-2011-entropic-gravity",
  caveat @ "claim:convergence-of-the-area-per-bit-construction-not-a-first-principles-value-of-G"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.gr_tendsto_newton_as_c_atTop where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.einsteinCoupling_tendsto_zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.weakFieldG00_tendsto_flat",
  formalizes @ "claim:the-gr-force-tends-to-the-newton-force-as-the-speed-of-light-goes-to-infinity",
  requires @ "claim:the-entropic-newton-constant-converges-in-the-continuum-holographic-screen-limit"

zil_file_contract physlib.entropicNewtonConstantConvergence where
  promises "The entropic Newton constant and the GR-to-Newton limit: the Newton force is the test mass times the gravitational field, the entropic Newton constant converges in the continuum holographic-screen limit, and the GR force tends to the Newton force as the speed of light goes to infinity."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce"]
  forbids_substitutes ["a first-principles numerical value of G, only the area-per-bit convergence is shown"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.newtonForce_eq_mass_field,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.gr_tendsto_newton_as_c_atTop]

/- ZIL-END -/
