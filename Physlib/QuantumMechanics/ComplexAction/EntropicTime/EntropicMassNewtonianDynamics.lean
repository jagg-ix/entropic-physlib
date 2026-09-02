/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita
meta import Zil

/-!
# From information geometry to Newtonian dynamics: mass as position uncertainty

Caticha and Cafaro (arXiv:0710.1071) derive Newtonian dynamics from information geometry alone: a
particle is a probability distribution on configuration space, the configuration space carries the
Fisher-Rao information metric, and the expected trajectory is its geodesic. For spherically symmetric
Gaussians with variance `σ₀²` the information metric is the conformally flat
`g_ij = (Φ/σ₀²) δ_ij` (Eq. 14). Reparametrising the geodesic by the intrinsic time `t` gives the
equation of motion `(1/σ₀²) d²x/dt² = ∂Φ/∂x` (Eq. 20), and a change of notation turns it into
Newton's law.

The pivotal identification is **Eq. 22**: with

  `m = 1/σ₀²`   and   `Φ(x) = −φ(x) + E`,

the geodesic equation of motion becomes Newton's `m d²x/dt² = −∂φ/∂x` (Eq. 23) and its first integral
becomes energy conservation `½ m v² + φ = E` (Eq. 24). The **mass is the reciprocal of the
irreducible position-uncertainty variance** — it is a feature of the underlying statistical manifold,
not a separate postulate. In the many-particle case each particle's uncertainty
`σ₁ = [Φ(x₁,x₂) m₁]^{-1/2}` (Eq. 41) depends on the location of the others, and that dependence is the
interaction.

* **§A** `inferenceMass σ₀ = 1/σ₀²` and the mass-variance product `m σ₀² = 1` (Eq. 22).
* **§B** the mass is the Fisher-Rao metric component `inferenceMass σ₀ = gMuMu σ₀` — the Gaussian
  location Fisher information `1/σ₀²` of `FisherRaoGaussianLeviCivita`, so inertial mass, Fisher
  information and (through `FisherRaoGaussianBohmQuantumPotential`) the Bohm quantum potential are the
  same object.
* **§C** the reparametrised geodesic equation of motion is Newton's law (Eqs. 20, 22, 23).
* **§D** energy conservation `½ m v² + φ = E` from the geodesic first integral `Φ = T_t` (Eqs. 21, 24).
* **§E** the position uncertainty modulated by the conformal factor `σ₁² = 1/(Φ m₁)` (Eq. 41): the
  coupling of the particles.

## References

* A. Caticha, C. Cafaro, *From Information Geometry to Newtonian Dynamics*, AIP Conf. Proc. 954 (2007)
  165 (arXiv:0710.1071) — Eqs. 13, 14, 20, 22, 23, 24, 41.
* A. Caticha, *Entropic Dynamics*, AIP Conf. Proc. 617 (2002) 302 — the expected trajectory is the
  geodesic of the information metric.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics

@[expose] public section

/-- **[Caticha-Cafaro inertial mass, Eq. 22]** `m = 1/σ₀²`: the inertial mass of a particle is the
reciprocal of the variance `σ₀²` of its irreducible position uncertainty. It enters Newtonian dynamics
as the conformal scale `1/σ₀²` of the Fisher-Rao information metric `g_ij = (1/σ₀²) δ_ij` (Eq. 13). -/
noncomputable def inferenceMass (σ₀ : ℝ) : ℝ := (σ₀ ^ 2)⁻¹

/-! ## A. The mass is the reciprocal position-uncertainty variance -/

/-- **[Eq. 22]** `inferenceMass σ₀ = 1/σ₀²`. -/
lemma inferenceMass_eq (σ₀ : ℝ) : inferenceMass σ₀ = 1 / σ₀ ^ 2 := by
  rw [inferenceMass, one_div]

/-- **[The mass-variance product, Eq. 22]** `m σ₀² = 1`: mass and position variance are reciprocal, so
their product is dimensionless unity. -/
lemma mass_variance_product (σ₀ : ℝ) (hσ : σ₀ ≠ 0) : inferenceMass σ₀ * σ₀ ^ 2 = 1 := by
  rw [inferenceMass]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hσ)

/-! ## B. The mass is the Fisher-Rao metric component (Gaussian Fisher information) -/

/-- **[Mass is the Fisher-Rao metric component]** `inferenceMass σ₀ = gMuMu σ₀`. The Caticha-Cafaro
inertial mass coincides with the `μ`-`μ` component of the Fisher-Rao metric of the Gaussian
(`FisherRaoGaussianLeviCivita`), which is the location Fisher information `1/σ₀²`
(`gMuMu_is_gaussian_fisher_info`). Thus inertial mass *is* Fisher information; through
`FisherRaoGaussianBohmQuantumPotential` the same `1/σ₀²` is the datum of the Bohm quantum potential.
Mass, information metric and quantum potential are three readings of the one position uncertainty. -/
lemma mass_is_fisherRao_metric (σ₀ : ℝ) : inferenceMass σ₀ = gMuMu σ₀ := by
  rw [inferenceMass, gMuMu]

/-! ## C. The reparametrised geodesic equation of motion is Newton's law -/

/-- **[The geodesic equation of motion is Newton's law, Eqs. 20, 22, 23]** The reparametrised geodesic
equation of motion `(1/σ₀²) a = ∂Φ/∂x` (Eq. 20), with the conformal factor split as `Φ = −φ + E` so
its gradient is `∂Φ/∂x = −∂φ/∂x` (`hΦ`), becomes Newton's second law `m a = −∂φ/∂x` (Eq. 23) with the
inertial mass `m = inferenceMass σ₀`. Here `a` is the coordinate acceleration `d²x/dt²`, `gradΦ` the
force per unit `1/σ₀²` from the metric, and `gradφ` the gradient of the Newtonian potential. -/
theorem geodesic_eom_is_newton (σ₀ a gradφ gradΦ : ℝ)
    (hΦ : gradΦ = -gradφ) (hgeo : (σ₀ ^ 2)⁻¹ * a = gradΦ) :
    inferenceMass σ₀ * a = -gradφ := by
  rw [inferenceMass, hgeo]; exact hΦ

/-! ## D. Energy conservation from the geodesic first integral -/

/-- **[Energy conservation, Eqs. 21, 24]** The geodesic first integral `Φ = T_t` with the kinetic term
`T_t = (1/2σ₀²) v²` and the split `Φ = −φ + E` gives `E − φ = (1/2σ₀²) v²` (`hΦ`), i.e. the conserved
Newtonian energy `½ m v² + φ = E` with the inertial mass `m = inferenceMass σ₀`. The constant `E` is
the freedom to add a constant to the potential. -/
theorem entropic_energy_conservation (σ₀ v φ E : ℝ)
    (hΦ : E - φ = (σ₀ ^ 2)⁻¹ * v ^ 2 / 2) :
    (1 / 2) * inferenceMass σ₀ * v ^ 2 + φ = E := by
  rw [inferenceMass]; linear_combination -hΦ

/-! ## E. Interaction: the position uncertainty modulated by the conformal factor -/

/-- **[The uncertainty couples the particles, Eq. 41]** `σ₁² = 1/(Φ m₁) ↔ Φ m₁ σ₁² = 1`. The position
uncertainty `σ₁` of particle 1 is set by the conformal factor `Φ(x₁, x₂)`, which depends on the
location of particle 2; that dependence is the interaction. Higher `Φ` (deeper potential) means lower
uncertainty. -/
theorem uncertainty_couples_particles (Φ m₁ σ₁ : ℝ) (hΦ : Φ ≠ 0) (hm : m₁ ≠ 0) :
    σ₁ ^ 2 = (Φ * m₁)⁻¹ ↔ Φ * m₁ * σ₁ ^ 2 = 1 := by
  rw [inv_eq_one_div, eq_div_iff (mul_ne_zero hΦ hm)]
  constructor <;> intro h <;> linear_combination h

/-! ## F. The intrinsic time: the reparametrisation that makes the universe its own clock -/

/-- **[The intrinsic time turns the geodesic kinetic energy into the conformal factor, Eqs. 19, 21]**
The reparametrisation `dt = (T_λ/Φ)^{1/2} dλ` of the timeless Jacobi geodesic (Eq. 19), i.e.
`(dλ/dt)² = Φ/T_λ`, gives `T_t := T_λ (dλ/dt)² = Φ` (Eq. 21): the kinetic energy measured in the
intrinsic time `t` equals the conformal factor. With `Φ = −φ + E` this is exactly the `Φ = T_t` fed to
`entropic_energy_conservation`. This is the step where the timeless inference principle acquires a
Newtonian time — the universe is its own clock; time is not postulated but read off the change of the
system. -/
theorem reparametrized_kinetic_is_conformal (Tlam Φ dlamdt : ℝ) (hT : Tlam ≠ 0)
    (hrep : dlamdt ^ 2 = Φ / Tlam) :
    Tlam * dlamdt ^ 2 = Φ := by
  rw [hrep]; field_simp

/-! ## G. The conformal metric: the local Fisher information -/

/-- **[The local Fisher information is the conformal factor times the inference mass, Eq. 14]** The
information metric `g_ij = (Φ/σ₀²) δ_ij` has variance field `σ(x)² = σ₀²/Φ(x)`, so the local position
Fisher information is `1/σ(x)² = Φ · inferenceMass σ₀`: the base inference mass `1/σ₀²` scaled by the
conformal factor. Equivalently `σ(x)² = 1/(Φ · m)`, the many-particle uncertainty of Eq. 41 — the
metric that curves configuration space, the inertia, and the interaction are one field. -/
theorem local_fisher_is_conformal_mass (σ₀ σ Φ : ℝ)
    (hconf : σ ^ 2 = σ₀ ^ 2 / Φ) :
    1 / σ ^ 2 = Φ * inferenceMass σ₀ := by
  rw [inferenceMass, hconf, one_div, inv_div, div_eq_mul_inv]

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.mass_variance_product where
  formalizes @ "claim:the-caticha-cafaro-inertial-mass-and-the-position-uncertainty-variance-are-reciprocal-their-product-mass-times-variance-is-dimensionless-unity",
  supported_by @ "paper:caticha-cafaro-arxiv-0710-1071-from-information-geometry-to-newtonian-dynamics"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.geodesic_eom_is_newton where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-reparametrised-fisher-rao-geodesic-equation-of-motion-is-newtons-second-law-inference-mass-times-acceleration-equals-minus-the-gradient-of-the-newtonian-potential",
  requires @ "claim:the-caticha-cafaro-inertial-mass-and-the-position-uncertainty-variance-are-reciprocal-their-product-mass-times-variance-is-dimensionless-unity"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.entropic_energy_conservation where
  formalizes @ "claim:the-geodesic-first-integral-gives-the-conserved-newtonian-energy-half-inference-mass-times-velocity-squared-plus-potential-equals-a-constant"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.reparametrized_kinetic_is_conformal where
  formalizes @ "claim:the-reparametrisation-by-the-intrinsic-time-turns-the-timeless-jacobi-geodesic-kinetic-energy-into-the-conformal-factor-the-step-where-the-timeless-inference-principle-acquires-a-newtonian-time"

zil_file_contract physlib.entropicMassNewtonianDynamics where
  promises "Caticha and Cafaro (arXiv:0710.1071) derive Newtonian dynamics from information geometry alone: a particle is a probability distribution on configuration space carrying the Fisher-Rao information metric, and the expected trajectory is its geodesic. The inertial mass is the reciprocal position-uncertainty variance, so mass times variance is unity (mass_variance_product); reparametrising the timeless Jacobi geodesic by the intrinsic time turns its kinetic energy into the conformal factor (reparametrized_kinetic_is_conformal), the step where the timeless inference principle acquires a Newtonian time. The reparametrised geodesic equation of motion is then Newton's second law m a = -grad phi (geodesic_eom_is_newton) and the geodesic first integral is the conserved Newtonian energy 1/2 m v^2 + phi = E (entropic_energy_conservation). Mass, information metric, and Newtonian dynamics are three readings of the one position uncertainty."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita.gMuMu"]
  forbids_substitutes ["the derivation of the Fisher-Rao geodesic and the conformally-flat information metric g = (Phi/sigma0^2) delta, which are the cited information-geometry inputs summarized by the geodesic hypotheses",
    "any relativistic or field-theoretic dynamics, only the Newtonian (nonrelativistic) equation of motion and energy conservation are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.mass_variance_product,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.geodesic_eom_is_newton,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.entropic_energy_conservation,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.reparametrized_kinetic_is_conformal]

/- ZIL-END -/
