/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral

/-!
# The geometric (and information-theoretic) origin of mass: `m² = V''(v₀)`

Formalizes the **exact** content of the "geometric origin of mass" reasoning (`tau`,
`m = δ²F/δv²`): the **mass is the curvature (Hessian) of a symmetry-breaking potential at its broken
minimum**. This is the framework-neutral **Landau–Ginzburg** statement — no electroweak / Standard-Model
input is required, only a symmetric double-well order-parameter potential. For

  `V(v) = a (v² − v₀²)²`   (`landauPotential`, `a > 0`, a quartic double well),

the broken-symmetry minimum (order parameter / vacuum) is at `v = v₀` (`landauPotential_vacuum`,
`V'(v₀) = 0`), and the **mass squared is the second derivative of the potential there**:

  `m² = V''(v₀) = 8 a v₀²`   (`vacuumMassSq`, `vacuumMassSq_eq`),

strictly positive for `a > 0`, `v₀ ≠ 0` (`vacuumMassSq_pos`) — spontaneous symmetry breaking gives the
fluctuation field a mass (the excitation gap / stiffness about the minimum). This is the literal
**geometric origin of mass** (curvature `=` geometry of the potential) and the **information-theoretic
origin** (the Hessian `δ²F/δv²` of a free-energy/action functional `F` is the Fisher-information metric,
`Physlib.StatisticalMechanics.FisherInformationCoercivity`): the mass is the Fisher-information curvature
of the action at the vacuum.

The order parameter `v₀` is the broken-symmetry vacuum value — a generic condensate amplitude (it
specialises to the electroweak scale, but the result is framework-neutral).

* **§A — the symmetry-breaking potential and its derivatives** (`landauPotential`, `landauPotentialDeriv`,
  `hasDerivAt_landauPotential`, `landauPotential_deriv`, `landauPotential_vacuum`,
  `hasDerivAt_landauPotentialDeriv`, `landauPotential_secondDeriv`).
* **§B — the mass as the curvature at the vacuum** (`vacuumMassSq`, `vacuumMassSq_eq`, `vacuumMassSq_pos`,
  `geometric_origin_of_mass`).

## References

* The Landau–Ginzburg mechanism: the mass is the curvature of the effective potential at the
  broken-symmetry minimum. Source note (`tau`): `m = δ²F/δv²` (mass = Hessian of the
  free-energy functional). Carriers: `Physlib.StatisticalMechanics.FisherInformationCoercivity`
  (the Hessian = Fisher information).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginOfMass


/-- **The Landau–Ginzburg / double-well symmetry-breaking potential** `V(v) = a(v² − v₀²)²` (`a > 0`), with
degenerate broken-symmetry minima (vacua) at `v = ±v₀`. -/
noncomputable def landauPotential (a v₀ : ℝ) : ℝ → ℝ := fun v => a * (v ^ 2 - v₀ ^ 2) ^ 2

/-- **The potential gradient** `V'(v) = 4a·v·(v² − v₀²)` — the restoring "force" (vanishing at the vacua). -/
noncomputable def landauPotentialDeriv (a v₀ : ℝ) : ℝ → ℝ := fun v => 4 * a * (v * (v ^ 2 - v₀ ^ 2))

/-- **[`V'(v) = 4a·v·(v² − v₀²)`]** the first derivative of the potential. -/
lemma hasDerivAt_landauPotential (a v₀ v : ℝ) :
    HasDerivAt (landauPotential a v₀) (landauPotentialDeriv a v₀ v) v := by
  have hg : HasDerivAt (fun x : ℝ => x ^ 2 - v₀ ^ 2) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).sub_const (v₀ ^ 2)
  have h := (hg.pow 2).const_mul a
  unfold landauPotential landauPotentialDeriv
  exact h.congr_deriv (by ring)

/-- **The derivative of the potential is the gradient** `V' = landauPotentialDeriv`. -/
lemma landauPotential_deriv (a v₀ : ℝ) :
    deriv (landauPotential a v₀) = landauPotentialDeriv a v₀ := by
  funext v; exact (hasDerivAt_landauPotential a v₀ v).deriv

/-- **[The vacuum is a critical point] `V'(v₀) = 0`.** The order parameter sits at the broken-symmetry
minimum `v = v₀`. -/
lemma landauPotential_vacuum (a v₀ : ℝ) : landauPotentialDeriv a v₀ v₀ = 0 := by
  unfold landauPotentialDeriv; ring

/-- **[`V''(v) = 4a·(3v² − v₀²)`]** the second derivative (curvature) of the potential. -/
lemma hasDerivAt_landauPotentialDeriv (a v₀ v : ℝ) :
    HasDerivAt (landauPotentialDeriv a v₀) (4 * a * (3 * v ^ 2 - v₀ ^ 2)) v := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 v := hasDerivAt_id' v
  have h1 : HasDerivAt (fun x : ℝ => x * (x ^ 2 - v₀ ^ 2)) (3 * v ^ 2 - v₀ ^ 2) v := by
    have h := hid.mul ((hasDerivAt_pow 2 v).sub_const (v₀ ^ 2))
    exact h.congr_deriv (by ring)
  have h := h1.const_mul (4 * a)
  unfold landauPotentialDeriv
  simpa using h

/-- **[The second derivative of the potential] `V''(v) = 4a·(3v² − v₀²)`.** -/
lemma landauPotential_secondDeriv (a v₀ v : ℝ) :
    deriv (deriv (landauPotential a v₀)) v = 4 * a * (3 * v ^ 2 - v₀ ^ 2) := by
  rw [landauPotential_deriv]
  exact (hasDerivAt_landauPotentialDeriv a v₀ v).deriv


/-- **The mass squared** `m² = V''(v₀)` — the curvature (Hessian) of the potential at the broken-symmetry
vacuum, the geometric/information-theoretic origin of mass. -/
noncomputable def vacuumMassSq (a v₀ : ℝ) : ℝ := deriv (deriv (landauPotential a v₀)) v₀

/-- **[The mass is the curvature at the vacuum] `m² = V''(v₀) = 8a v₀²`.** The mass squared is the second
derivative of the symmetry-breaking potential at the vacuum `v₀` — the curvature of the double well. -/
lemma vacuumMassSq_eq (a v₀ : ℝ) : vacuumMassSq a v₀ = 8 * a * v₀ ^ 2 := by
  rw [vacuumMassSq, landauPotential_secondDeriv]; ring

/-- **[Symmetry breaking gives a positive mass] `m² > 0`** for `a > 0`, `v₀ ≠ 0`. -/
lemma vacuumMassSq_pos (a v₀ : ℝ) (ha : 0 < a) (hv : v₀ ≠ 0) : 0 < vacuumMassSq a v₀ := by
  rw [vacuumMassSq_eq]; positivity

/-- **[The geometric origin of mass, assembled].** For the symmetry-breaking potential `V(v) = a(v² − v₀²)²`
(`a > 0`, `v₀ ≠ 0`):

* the vacuum `v₀` is a critical point, `V'(v₀) = 0`;
* the **mass squared is the curvature there**, `m² = V''(v₀) = 8a v₀²`;
* it is strictly positive — spontaneous symmetry breaking gives the field a mass.

The mass is the curvature (Hessian) of the potential at the vacuum: the geometric origin of mass (curvature
`=` geometry) and, since the Hessian of the free-energy functional is the Fisher-information metric, the
information-theoretic origin too. The order parameter `v₀` is the broken-symmetry vacuum value. -/
lemma geometric_origin_of_mass (a v₀ : ℝ) (ha : 0 < a) (hv : v₀ ≠ 0) :
    landauPotentialDeriv a v₀ v₀ = 0
      ∧ vacuumMassSq a v₀ = 8 * a * v₀ ^ 2
      ∧ 0 < vacuumMassSq a v₀ :=
  ⟨landauPotential_vacuum a v₀, vacuumMassSq_eq a v₀, vacuumMassSq_pos a v₀ ha hv⟩

end Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginOfMass

end
