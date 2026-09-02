/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant

/-!
# The weak equivalence principle: universality of free fall from the Fisher-information mass

The keystone that binds the three papers of this arc. Caticha and Cafaro (arXiv:0710.1071) obtain the
inertial mass — the coefficient of acceleration in Newton's `m·a = F` — as the position-uncertainty
Fisher information `m = 1/σ₀²` (`EntropicMassNewtonianDynamics.inferenceMass`, `= gMuMu σ₀`). In the
gravitational force `F = G M m/R²` the *same* `m` is the gravitational charge. Entropic dynamics
produces the mass exactly once, so **inertial mass and gravitational mass are the one object**; the
`m` cancels in the acceleration and free fall is universal:

  `a = F/m = G M/R²`   for every test particle, whatever its uncertainty `σ₀`.

This is the **weak equivalence principle** — the universality of free fall — and it is the fact
Blume's derivation of general relativity rests on: the geodesic velocity field `∇_u u = 0`
(`VelocityDivergenceFieldEquation`) is the free-fall motion whose universality lets Newton's and
Einstein's field equations be *the same* velocity-field divergence equation.

Unexpectedly, in the Verlinde area-per-bit form the free-fall acceleration is

  `a = G M/R² = 4π M c³/(ℏ N)`   (`N = holographicBits (sphereArea R) G ℏ c`),

depending only on the **source mass `M` and the screen bit count `N`** — the test particle has
vanished, and the `ℏ` of the quantum (bit) description **cancels** against the `ℏ` of the Planck area
`ℓ_P² = Gℏ/c³` in `N`, leaving the classical `G M/R²`. Gravity couples to Fisher information, inertia
*is* Fisher information, and their equality is why the fall is free.

* **§A** `a = F/m = G M/R²`: the test mass cancels.
* **§B** universality: the acceleration is independent of the test particle's uncertainty `σ₀`.
* **§C** the bit form `a = 4π M c³/(ℏ N)`: source and bit count only, `ℏ` cancels.
* **§D** the weak equivalence principle: universality together with the bit form.

The Einstein (thermodynamic) face of the equivalence principle — a uniformly accelerated observer's
proper acceleration equal to the horizon surface gravity, `unruhTemperature = hawkingTemperature` — is
`CausalDiamond.EquivalencePrinciple.equivalence_principle`; this module is its Newtonian (inertial)
partner. Free fall as force-free geodesic motion of the entropic particle is
`GaussianEntropicMotionGeodesic.fisherRao_mu_firstIntegral`.

## References

* A. Caticha, C. Cafaro, arXiv:0710.1071 — the inertial mass `m = 1/σ₀²`.
* E. Verlinde, JHEP 04 (2011) 029 — the area-per-bit `G` and the screen acceleration.
* F. Blume, J. Appl. Math. Phys. 10 (2022) 1461 — the equivalence of inertial and gravitational mass
  as the ground of the Newton→GR transition.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.Thermodynamics

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.FreeFallUniversalityFisherMass

@[expose] public section

/-! ## A. The test mass cancels: `a = F/m = G M/R²` -/

/-- **[Free-fall acceleration, the test mass cancels]** The gravitational force `F = G M m/R²` on a
test particle of inference mass `m = inferenceMass σ₀ = 1/σ₀²` gives, by Newton's second law
`a = F/m`, the acceleration `a = G M/R²`: the inertial mass in `F = m a` and the gravitational mass in
`F = G M m/R²` are the same `inferenceMass σ₀`, so they cancel. -/
theorem freeFall_acceleration (G M σ₀ R : ℝ) (hσ : σ₀ ≠ 0) (hR : R ≠ 0) :
    G * M * inferenceMass σ₀ / R ^ 2 / inferenceMass σ₀ = G * M / R ^ 2 := by
  rw [inferenceMass]
  field_simp

/-! ## B. Universality: independent of the test particle's uncertainty -/

/-- **[Universality of free fall]** Two test particles with different position uncertainties `σ₀` and
`σ₀'` — hence different inference masses `1/σ₀²` and `1/σ₀'²` — fall with the *same* acceleration
`G M/R²` in the field of the source `M`. The acceleration does not depend on the test particle at all;
this is the weak equivalence principle. -/
theorem universality_of_free_fall (G M σ₀ σ₀' R : ℝ)
    (hσ : σ₀ ≠ 0) (hσ' : σ₀' ≠ 0) (hR : R ≠ 0) :
    G * M * inferenceMass σ₀ / R ^ 2 / inferenceMass σ₀
      = G * M * inferenceMass σ₀' / R ^ 2 / inferenceMass σ₀' := by
  rw [freeFall_acceleration G M σ₀ R hσ hR, freeFall_acceleration G M σ₀' R hσ' hR]

/-! ## C. The bit form: source and bit count only, `ℏ` cancels -/

/-- **[The free-fall acceleration in bit form]** `a = G M/R² = 4π M c³/(ℏ N)` at the holographic bit
count `N = holographicBits (sphereArea R) G ℏ c`. The acceleration depends only on the source mass `M`
and the screen's bit count `N`; the test particle has vanished (equivalence principle), and the `ℏ` of
the bit description cancels against the `ℏ` in `N ∝ 1/(G ℏ)`, recovering the classical `G M/R²`. -/
theorem freeFall_acceleration_bitForm (G M ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    G * M / R ^ 2 = 4 * Real.pi * M * c ^ 3 / (ℏ * N) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hbits]
  unfold holographicBits sphereArea
  field_simp

/-! ## D. The weak equivalence principle -/

/-- **[The weak equivalence principle from information geometry]** From the single identification
`N = holographicBits (sphereArea R) G ℏ c`, the free-fall acceleration of an inference-mass test
particle is (1) **universal** — the same for any two uncertainties `σ₀`, `σ₀'` — and (2) equal to the
bit form `4π M c³/(ℏ N)`, which contains neither the test mass nor (after the `ℏ` cancellation) any
quantum scale. Inertial mass and gravitational mass are the one Fisher-information mass; that identity
is the equivalence principle, and it is what makes Newton's and Einstein's field equations the same
velocity-field divergence equation (`VelocityDivergenceFieldEquation`). -/
theorem weak_equivalence_principle (G M ℏ c N R σ₀ σ₀' : ℝ)
    (hσ : σ₀ ≠ 0) (hσ' : σ₀' ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    G * M * inferenceMass σ₀ / R ^ 2 / inferenceMass σ₀
        = G * M * inferenceMass σ₀' / R ^ 2 / inferenceMass σ₀'
    ∧ G * M * inferenceMass σ₀ / R ^ 2 / inferenceMass σ₀ = 4 * Real.pi * M * c ^ 3 / (ℏ * N) := by
  refine ⟨universality_of_free_fall G M σ₀ σ₀' R hσ hσ' hR, ?_⟩
  rw [freeFall_acceleration G M σ₀ R hσ hR]
  exact freeFall_acceleration_bitForm G M ℏ c N R hℏ hc hG hR hbits

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.FreeFallUniversalityFisherMass
