/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.AlphaOrderGaussianCurvature

/-!
# Entropic motion on the Gaussian statistical manifold: the geodesic and its first integral

Caticha's entropic dynamics identifies the *expected* trajectory of a system between two
distributions with the **geodesic** of the information metric (Gassner-Cafaro 2019, §IV): each
macrovariable `θ^k(τ)` solves the geodesic equation

  `d²θ^k/dτ² + Γ^k_{ij} (dθ^i/dτ)(dθ^j/dτ) = 0`   (Eq. 28),

with the Levi-Civita connection of `FisherRaoGaussianLeviCivita` / `AlphaOrderGaussianCurvature`. On
the Gaussian manifold `(μ, σ)` the metric does not depend on `μ`, so translation in `μ` is a Killing
symmetry and the `μ`-equation has a **first integral**: the mean's conjugate momentum is conserved.

* **§A** the Fisher-Rao first integral: a motion with `μ̇ = A σ²` (`A = μ̇/σ²` conserved) solves the
  `μ`-geodesic equation `μ̈ + 2 Γ^μ_{μσ} μ̇ σ̇ = 0` (Gassner-Cafaro Eqs. 31-32).
* **§B** substituting `μ̇ = A σ²` into the `σ`-geodesic equation reduces the entropic motion to the
  single ordinary differential equation `σ σ̈ − σ̇² + (A²/2) σ⁴ = 0` (Gassner-Cafaro Eq. 33).
* **§C** the α-order first integral: there the conserved momentum is `μ̇ = A σ³` (Eq. 54); the extra
  power of `σ` is exactly the change in the metric's scaling from `1/σ²` to `1/σ³`.

The conservation `μ̇/σ^p = const` (`p = 2` Fisher-Rao, `p = 3` α-order) is the momentum of the
expected trajectory of entropic inference, tied directly to the connection coefficients derived in the
companion modules.

## References

* S. Gassner, C. Cafaro, arXiv:1903.11190 — §IV (Entropic Motion): the geodesic equation (Eq. 28), the
  `μ`-first integral `μ̇ = A σ²` / `A σ³` (Eqs. 31-32, 53-54) and the reduced `σ`-ODE (Eq. 33).
* A. Caticha, *Entropic Dynamics*, Entropy 17 (2015) 6110 — the expected trajectory is the geodesic of
  the information metric.
-/

set_option autoImplicit false

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianEntropicMotionGeodesic

@[expose] public section

open Physlib.QuantumMechanics.ComplexAction.EntropicTime

/-! ## A. The Fisher-Rao first integral of entropic motion -/

/-- **[The Fisher-Rao μ-geodesic first integral]** A trajectory whose mean velocity satisfies
`μ̇ = A σ²` (equivalently `A = μ̇/σ²` is conserved) has mean acceleration `μ̈ = 2A σ σ̇` and therefore
solves the `μ`-geodesic equation `μ̈ + 2 Γ^μ_{μσ} μ̇ σ̇ = 0` (Gassner-Cafaro Eqs. 31-32), with
`Γ^μ_{μσ} = −1/σ` the Fisher-Rao connection coefficient (`FisherRaoGaussianLeviCivita`). The mean is a
cyclic coordinate: its conjugate momentum is conserved along entropic motion. -/
theorem fisherRao_mu_firstIntegral (σ : ℝ → ℝ) (A τ σ' : ℝ)
    (hσ : HasDerivAt σ σ' τ) (hσ0 : σ τ ≠ 0) :
    deriv (fun t => A * (σ t * σ t)) τ
      + 2 * FisherRaoGaussianLeviCivita.christoffel_Mu_MuSi (σ τ) * (A * (σ τ * σ τ)) * σ' = 0 := by
  have hv : HasDerivAt (fun t => A * (σ t * σ t)) (A * (σ' * σ τ + σ τ * σ')) τ :=
    (hσ.mul hσ).const_mul A
  rw [hv.deriv, FisherRaoGaussianLeviCivita.christoffel_Mu_MuSi_eq (σ τ) hσ0]
  field_simp; ring

/-! ## B. Reduction of the entropic motion to a single ODE -/

/-- **[The σ-geodesic equation under the first integral, Gassner-Cafaro Eq. 33]** With the Fisher-Rao
connection `Γ^σ_{μμ} = 1/(2σ)`, `Γ^σ_{σσ} = −1/σ`, feeding the first integral `μ̇ = A σ²` into the
`σ`-geodesic equation `σ̈ + Γ^σ_{μμ} μ̇² + Γ^σ_{σσ} σ̇² = 0` and clearing the `1/σ` gives the single
ordinary differential equation `σ σ̈ − σ̇² + (A²/2) σ⁴ = 0` for the entropic motion. -/
theorem fisherRao_sigma_ode (s A sdot sddot : ℝ) (hs : s ≠ 0) :
    s * (sddot + FisherRaoGaussianLeviCivita.christoffel_Si_MuMu s * (A * s ^ 2) ^ 2
          + FisherRaoGaussianLeviCivita.christoffel_Si_SiSi s * sdot ^ 2)
      = s * sddot - sdot ^ 2 + (A ^ 2 / 2) * s ^ 4 := by
  rw [FisherRaoGaussianLeviCivita.christoffel_Si_MuMu_eq s hs,
    FisherRaoGaussianLeviCivita.christoffel_Si_SiSi_eq s hs]
  field_simp; ring

/-! ## C. The α-order first integral of entropic motion -/

/-- **[The α-order μ-geodesic first integral, Gassner-Cafaro Eq. 54]** For the α-order metric the
conserved mean momentum is `μ̇ = A σ³`: such a motion has `μ̈ = 3A σ² σ̇` and solves
`μ̈ + 2 Γ^μ_{μσ} μ̇ σ̇ = 0` with `Γ^μ_{μσ} = −3/(2σ)` (`AlphaOrderGaussianCurvature`). The extra power
of `σ` compared with the Fisher-Rao value `σ²` mirrors the change of the metric's scale exponent from
`1/σ²` to `1/σ³`. -/
theorem alpha_mu_firstIntegral (σ : ℝ → ℝ) (A τ σ' : ℝ)
    (hσ : HasDerivAt σ σ' τ) (hσ0 : σ τ ≠ 0) :
    deriv (fun t => A * (σ t * (σ t * σ t))) τ
      + 2 * AlphaOrderGaussianCurvature.christoffel_Mu_MuSi (σ τ) * (A * (σ τ * (σ τ * σ τ))) * σ'
        = 0 := by
  have hv : HasDerivAt (fun t => A * (σ t * (σ t * σ t)))
      (A * (σ' * (σ τ * σ τ) + σ τ * (σ' * σ τ + σ τ * σ'))) τ :=
    (hσ.mul (hσ.mul hσ)).const_mul A
  rw [hv.deriv, AlphaOrderGaussianCurvature.christoffel_Mu_MuSi_eq (σ τ) hσ0]
  field_simp; ring

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianEntropicMotionGeodesic
