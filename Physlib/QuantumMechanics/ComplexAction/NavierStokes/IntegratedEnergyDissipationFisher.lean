/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.ViscousDissipationFisherInformation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The integrated energy-dissipation identity: `∫u·Δu = −∫|∇u|² = −(Fisher information)`

Promotes the *pointwise* carré du champ of `NavierStokes.ViscousDissipationFisherInformation`
(`f·f'' = ½(f²)'' − (f')²`) to the **integrated** Dirichlet form `⟨Δf, f⟩_{L²} = −‖∇f‖²_{L²}` by an actual
integration by parts (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`). This is the exact step that turns
the Landau–Lifshitz–Navier–Stokes viscous term into the dissipation `‖∇u‖²` of the Leray energy inequality
(B. Gess, D. Heydecker, Z. Wu, arXiv:2311.02223, Eq. 1.3, `dE/dt = −ν‖∇u‖²`), and it is the same integration
by parts that `Schrodinger.BadialiQuantitativeHTheorem` names as its deferred Sobolev target when it assumes
the **de Bruijn identity** `dH/dt = D·I(φ)` (entropy production = Fisher information) as a hypothesis. Here
the step is machine-checked, on a period `[a, b]` with the closed-domain boundary condition
`f(b)·f'(b) = f(a)·f'(a)` (satisfied on a torus, `f`, `f'` periodic).

* **§A — the integrated Dirichlet form** (`laplacian_dirichletForm`): `∫ₐᵇ f·f'' = −∫ₐᵇ (f')²`, integration
  by parts with the boundary term killed by periodicity.
* **§B — Leray's dissipation sign** (`integratedDissipation_nonneg`, `laplacian_dirichletForm_nonpos`):
  `∫(f')² ≥ 0` (the `H¹` seminorm / total enstrophy is non-negative) so `∫f·f'' ≤ 0` — the viscous term only
  removes energy (Eq. 1.3), and `enstrophy_dissipation_from_integratedFisher` feeds it to the NS enstrophy
  dissipation.
* **§C — the total dissipation is the total Fisher information** (`integratedDissipation_eq_fisher`):
  `∫(f')² = ¼·∫ fisherDensity(f²)` — the integrated viscous dissipation `‖∇u‖²` equals a quarter of the total
  Fisher information of the Madelung transform, the integrated form of
  `ViscousDissipationFisherInformation.dissipationDensity_eq_fisher`.
* **§D — assembled** (`integrated_dissipation_is_fisher`).

Reuses (GREP-first, no duplication) `NavierStokes.ViscousDissipationFisherInformation`
(`dissipationDensity_eq_fisher`, `fisherDensity`, `enstrophyDissipationRate`,
`enstrophyDissipationRate_nonpos`) and Mathlib's interval-integral integration by parts.

## References

* B. Gess, D. Heydecker, Z. Wu, arXiv:2311.02223, Eq. 1.3 (Leray energy inequality, `‖∇u‖²` dissipation);
  J. Leray, Acta Math. 63 (1934) 193; Stam 1959 / de Bruijn (the integration-by-parts kernel of
  `dH/dt = D·I`, the target deferred by `Schrodinger.BadialiQuantitativeHTheorem`). Carriers:
  `NavierStokes.ViscousDissipationFisherInformation`, Mathlib
  `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.IntegratedEnergyDissipationFisher

open Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungTransformFisherPotential
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.ViscousDissipationFisherInformation
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy

/-! ### §A The integrated Dirichlet form of the viscous Laplacian (integration by parts) -/

/-- **[The integrated Dirichlet form] `∫ₐᵇ f·f'' = −∫ₐᵇ (f')²`.** Integration by parts on a period `[a, b]`
with the closed-domain boundary condition `f(b)·f'(b) = f(a)·f'(a)` (the torus condition: `f`, `f'` periodic)
kills the boundary term. This is `⟨Δf, f⟩_{L²} = −‖∇f‖²_{L²}`, the exact identity that produces the viscous
dissipation `‖∇u‖²` of the Navier–Stokes Leray energy inequality (Eq. 1.3) and the integration-by-parts
kernel of the de Bruijn identity `dH/dt = D·I` assumed by `BadialiQuantitativeHTheorem`. -/
theorem laplacian_dirichletForm (f f' f'' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'c : Continuous f') (hf''c : Continuous f'')
    (hbc : f b * f' b = f a * f' a) :
    ∫ x in a..b, f x * f'' x = -∫ x in a..b, (f' x) ^ 2 := by
  have hby := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hf x) (fun x _ => hf' x)
    (hf'c.intervalIntegrable a b) (hf''c.intervalIntegrable a b)
  rw [hby, hbc, sub_self, zero_sub]
  congr 1
  exact intervalIntegral.integral_congr (fun x _ => (pow_two (f' x)).symm)

/-! ### §B Leray's dissipation sign -/

/-- **[The dissipation is non-negative] `0 ≤ ∫ₐᵇ (f')²`** for `a ≤ b`. The `H¹` seminorm / total enstrophy /
integrated dissipation is non-negative — the integrand `(f')²` is a square. -/
theorem integratedDissipation_nonneg (f' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    0 ≤ ∫ x in a..b, (f' x) ^ 2 :=
  intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg (f' x))

/-- **[Leray's energy-inequality sign] `∫ₐᵇ f·f'' ≤ 0`.** Pairing the viscous Laplacian against the field can
only remove energy: the integrated Dirichlet form is minus a non-negative dissipation — the sign that makes
the Leray energy balance (Eq. 1.3) a decay. -/
theorem laplacian_dirichletForm_nonpos (f f' f'' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'c : Continuous f') (hf''c : Continuous f'') (hab : a ≤ b)
    (hbc : f b * f' b = f a * f' a) :
    ∫ x in a..b, f x * f'' x ≤ 0 := by
  rw [laplacian_dirichletForm f f' f'' a b hf hf' hf'c hf''c hbc]
  exact neg_nonpos_of_nonneg (integratedDissipation_nonneg f' a b hab)

/-- **[The integrated dissipation drives the NS enstrophy down]
`enstrophyDissipationRate ν (∫(f')²) ≤ 0`.** The non-negative integrated dissipation, fed as the palinstrophy
of `VorticityCoadjointEnstrophy.enstrophyDissipationRate`, gives a non-positive enstrophy rate. -/
theorem enstrophy_dissipation_from_integratedFisher (ν : ℝ) (f' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hν : 0 ≤ ν) :
    enstrophyDissipationRate ν (∫ x in a..b, (f' x) ^ 2) ≤ 0 :=
  enstrophyDissipationRate_nonpos ν _ hν (integratedDissipation_nonneg f' a b hab)

/-! ### §C The total viscous dissipation is the total Fisher information -/

/-- **[The integrated dissipation is the total Fisher information] `∫ₐᵇ (f')² = ¼·∫ₐᵇ fisherDensity(f²)`.**
The integrated form of `dissipationDensity_eq_fisher`: the total viscous dissipation `‖∇u‖²` of the
Navier–Stokes energy inequality equals a quarter of the total Fisher information of the Madelung density
`ρ = f²` (requires `f ≠ 0` on `[a, b]`, so the density is strictly positive). -/
theorem integratedDissipation_eq_fisher (f f' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hne : ∀ x ∈ Set.uIcc a b, f x ≠ 0) :
    ∫ x in a..b, (f' x) ^ 2 = 1 / 4 * ∫ x in a..b, fisherDensity (fun y => (f y) ^ 2) x := by
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr
    (fun x hx => dissipationDensity_eq_fisher f f' hf x (hne x hx))

/-! ### §D The integrated viscous dissipation is the Fisher information, assembled -/

/-- **[The integrated Navier–Stokes dissipation is the Fisher information, assembled].** On a period `[a, b]`
(`a ≤ b`, boundary term `f(b)f'(b) = f(a)f'(a)`, `f ≠ 0` on `[a, b]`):

* **(Dirichlet form)** `∫ f·f'' = −∫ (f')²` — integration by parts, `⟨Δf, f⟩ = −‖∇f‖²`;
* **(Leray sign)** `∫ f·f'' ≤ 0` — the viscous term only removes energy (Eq. 1.3);
* **(dissipation = Fisher)** `∫ (f')² = ¼·∫ fisherDensity(f²)` — the total viscous dissipation is the total
  Fisher information of the Madelung transform.

The `‖∇u‖²` that the Landau–Lifshitz–Navier–Stokes viscous term dissipates, and against which the paper's
large deviations must fight, is — integrated over the domain — the Fisher information of the Madelung density,
through the one Laplacian both share. -/
theorem integrated_dissipation_is_fisher (f f' f'' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'c : Continuous f') (hf''c : Continuous f'') (hab : a ≤ b)
    (hbc : f b * f' b = f a * f' a) (hne : ∀ x ∈ Set.uIcc a b, f x ≠ 0) :
    ∫ x in a..b, f x * f'' x = -∫ x in a..b, (f' x) ^ 2
      ∧ ∫ x in a..b, f x * f'' x ≤ 0
      ∧ ∫ x in a..b, (f' x) ^ 2 = 1 / 4 * ∫ x in a..b, fisherDensity (fun y => (f y) ^ 2) x :=
  ⟨laplacian_dirichletForm f f' f'' a b hf hf' hf'c hf''c hbc,
    laplacian_dirichletForm_nonpos f f' f'' a b hf hf' hf'c hf''c hab hbc,
    integratedDissipation_eq_fisher f f' a b hf hne⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.IntegratedEnergyDissipationFisher

end
