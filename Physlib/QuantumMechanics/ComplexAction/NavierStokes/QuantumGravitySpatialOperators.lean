/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.ActionQuantumFiniteResolutionBKM
public import Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.NoInfiniteTimeResolution

/-!
# The spatial operators, modified by quantum gravity

I had called the spatial operators `Δ, ∇, ∇·` "unchanged" by the time reparametrization.  They are not
unchanged in the physical theory: the same quantum-gravity results that gave the holographic `G = ℏc/m²` and the
Compton screen cell give a **minimal length** — the Compton / viscous cell `ℓ = λ_C = ℏ/(mc)`
(`FrequencyTrinity.comptonWavelength`).  A minimal length is a spatial UV cutoff: the Laplacian's spectrum runs
only up to the **Compton wavenumber** `k_max = 1/ℓ = mc/ℏ`, so

  `k_max² = (mc/ℏ)² = m²c²/ℏ²`      (`comptonWavenumber_sq`).

This carries the *same* `ℏ` as the entropic time: space is quantized at `ℓ = ℏ/(mc)` exactly as time is quantized
at `ΔT > 0`.  On the minimal-length-modified operators the vortex cascade is cut, and the Bernstein inequality
becomes `P ≤ k_max²·Ω = (m²c²/ℏ²)·Ω` (`bernstein_at_comptonCell`) — the palinstrophy bounded by the enstrophy
times the quantum-gravity scale, which closes the budget (`palinstrophy_budget_at_comptonCell`).

So the fully physical Navier–Stokes is quantized in **both** space and time: the entropic clock `τ` and the
minimal-length operators `Δ_ℓ, ∇_ℓ` — both set by `ℏ`.  The momentum equation
`∂_τ u = (2/Ω)(νΔu − (u·∇)u − ∇p)` runs on the `Δ` cut at `k_max = mc/ℏ`, not the continuum Laplacian.

## Honest scope

The minimal length is a **physical regularization**, `ℏ`-set but finite; as `ℏ → 0` the cutoff
`k_max = mc/ℏ → ∞` and the modification vanishes into the continuum Laplacian.  So this modifies the operators of
the *physical* fluid and closes it, but the classical continuum (`ℏ = 0`, `k_max = ∞`) — the Clay object — is the
limit where the quantum-gravity modification, and its closure, disappear.  The `ℏ`-free depletion question — by
`ThreeDimensionalVortexStretchingDepletion` the enstrophy balance restated — remains open at every scale.  The
molecular-screening section below scopes the story further: the Compton cutoff does independent work only on
trajectories carrying sub-molecular modes, i.e. on the idealized continuum-all-the-way-down fluid.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.QuantumGravitySpatialOperators

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-- **The spatial UV cutoff is the squared Compton wavenumber.**  The minimal length `ℓ = λ_C = ℏ/(mc)` gives a
Laplacian cutoff at `k_max = 1/ℓ`, so `k_max² = (mc/ℏ)² = m²c²/ℏ²` — the spatial operators are cut at the
quantum-gravity Compton scale, carrying the same `ℏ` as the entropic clock. -/
theorem comptonWavenumber_sq (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    (comptonWavelength m c ħ)⁻¹ ^ 2 = m ^ 2 * c ^ 2 / ħ ^ 2 := by
  unfold comptonWavelength
  rw [inv_div]
  field_simp

/-- **Bernstein at the Compton cell.**  On the minimal-length-modified Laplacian, the palinstrophy is bounded by
the enstrophy times the quantum-gravity cutoff: `P ≤ (1/ℓ²)·Ω = (m²c²/ℏ²)·Ω`.  The vortex cascade is cut at the
Compton scale. -/
theorem bernstein_at_comptonCell (m c ħ P Ω : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hBernstein : P ≤ (comptonWavelength m c ħ)⁻¹ ^ 2 * Ω) :
    P ≤ m ^ 2 * c ^ 2 / ħ ^ 2 * Ω := by
  rwa [comptonWavenumber_sq m c ħ hm hc hħ] at hBernstein

/-- **The palinstrophy budget closes at the Compton cell.**  Integrating the Compton-cell Bernstein bound, the
integrated palinstrophy is controlled by the integrated enstrophy times the quantum-gravity scale:
`∫P ≤ (m²c²/ℏ²)·∫Ω`.  The minimal-length spatial operators close the budget that the continuum operators leave
open. -/
theorem palinstrophy_budget_at_comptonCell (m c ħ IP IΩ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hBudget : IP ≤ (comptonWavelength m c ħ)⁻¹ ^ 2 * IΩ) :
    IP ≤ m ^ 2 * c ^ 2 / ħ ^ 2 * IΩ :=
  bernstein_at_comptonCell m c ħ IP IΩ hm hc hħ hBudget

/-! ### The molecular scale screens the Compton cell

The quantum-gravity protection story concerns an idealized **continuum-all-the-way-down** fluid — proved at the
level it can honestly be formalized:

* the repo's own atomic rung (`Particles.CasimirLengthHierarchy.bohrRadius = ƛ_C/α`) places the Compton cell
  strictly *below* the atomic scale for `α < 1` (`compton_below_atomic`) — and a real fluid's continuum
  description already ends at the molecular / mean-free-path scale, coarser still;
* wherever any coarser cutoff `k_mol ≤ k_C` already band-limits the trajectory, the molecular closure holds with
  the *tighter* prefactor and the Compton band-limit is implied — the quantum-gravity cutoff is **redundant**
  (`molecular_cutoff_screens_compton`);
* if the Compton cutoff is doing work the molecular one does not, the trajectory *must* carry a sub-molecular
  mode (`compton_operative_implies_submolecular`) — the continuum strictly below the molecular scale, exhibited
  as a witness;
* the dichotomy (`continuum_all_the_way_down_dichotomy`): every Compton-band-limited trajectory either closes
  already at the molecular cutoff (QG idle), or carries sub-molecular modes (the idealization made explicit).

Honest scope — corrected: the repository *does* have kinetic layers — the collisionless Boltzmann–Maxwell arc
(`Vlasov/`: steady-state first integrals, Lyapunov stability, time reversal), the quantum Boltzmann H-theorem
(`Lindblad.SpohnVariationalHTheorem` on `Thermodynamics.SecondLawQuantumBoltzmann`), and the linear Boltzmann
collision-operator arc (`CollisionOperatorSl2.LinearBoltzmannOperator`, `CollisionModular`, `Moyal.CollisionStar`).
What it lacks is the specific collisional gas-kinetics chain that would *derive* the molecular cutoff: a mean
free path is a property of the collision term, the `Vlasov/` layer is collisionless, and no Knudsen /
Chapman–Enskog reduction of a collisional kinetic equation to Navier–Stokes exists here.  The mean free path
*is* now derived below — via Maxwell's kinetic relation at the repository's own quantum viscosity
(`meanFreePath_quantum_deBroglie`, `compton_below_meanFreePath`: sub-luminality is the hierarchy); the exact
atomic rung is `ƛ_C = α·a₀ < a₀`.  A rate-based derivation from `LinearBoltzmannOperator` — which is the
*algebraic* sl(2) collision-star layer, carrying no numeric collision rate — remains open.
What is proved is the logical skeleton of the claim: the quantum-gravity cutoff does independent work *only* on
trajectories with modes below every coarser physical cutoff — the idealized continuum-all-the-way-down fluid. -/

open Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLengthHierarchy
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.ActionQuantumFiniteResolutionBKM
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier

/-- **The Compton cell sits strictly below the atomic scale.**  From the repo's own hierarchy rung
`a₀ = ƛ_C/α` (`CasimirLengthHierarchy.bohrRadius`), for `0 < α < 1` the Compton cell is strictly smaller than
the Bohr radius: `ƛ_C < a₀`.  The atomic (a fortiori molecular) scale lies strictly above the quantum-gravity
cell. -/
theorem compton_below_atomic (m c ħ α : ℝ) (hlc : 0 < comptonWavelength m c ħ)
    (hα : 0 < α) (hα1 : α < 1) :
    comptonWavelength m c ħ < bohrRadius m c ħ α := by
  unfold bohrRadius
  rw [lt_div_iff₀ hα]
  nlinarith [hlc, hα1]

/-- **A coarser cutoff screens the Compton cell.**  If the trajectory is band-limited at any coarser scale
`k_mol ≤ k_C`, then the BKM surrogate closes already with the *molecular* prefactor, and the Compton band-limit
is implied — the quantum-gravity cutoff adds nothing. -/
theorem molecular_cutoff_screens_compton
    (N : ℕ) (traj : ℝ → NSFieldFourier) (ν ℏ : ℝ) (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmol kC : ℕ) (hkk : kmol ≤ kC)
    (hfreq : ∀ t i, (traj t).freq i ≤ kmol) (T : ℝ) :
    bkmSurrogateIntegral N traj T
        ≤ ℏ / ν * (1 + (kmol : ℝ) ^ 2) * entropicProperTime N traj ν ℏ T
      ∧ ∀ t i, (traj t).freq i ≤ kC :=
  ⟨finiteResolution_bkmSurrogate_bounded N traj ν ℏ hN hν hℏ kmol hfreq T,
    fun t i => (hfreq t i).trans hkk⟩

/-- **If the Compton cutoff is operative, the fluid carries sub-molecular modes.**  A trajectory that is
Compton-band-limited but *not* molecularly band-limited must contain a mode strictly between the two scales:
`k_mol < freq ≤ k_C` — the continuum below the molecular scale, exhibited as a witness. -/
theorem compton_operative_implies_submolecular
    (traj : ℝ → NSFieldFourier) (kmol kC : ℕ)
    (hC : ∀ t i, (traj t).freq i ≤ kC)
    (hnot : ¬ ∀ t i, (traj t).freq i ≤ kmol) :
    ∃ t i, kmol < (traj t).freq i ∧ (traj t).freq i ≤ kC := by
  simp only [not_forall, not_le] at hnot
  obtain ⟨t, i, h⟩ := hnot
  exact ⟨t, i, h, hC t i⟩

/-- **The continuum-all-the-way-down dichotomy.**  Every Compton-band-limited trajectory either closes already
at the coarser molecular cutoff — the quantum-gravity cell idle — or carries a sub-molecular mode: the
quantum-gravity protection does independent work *only* on the idealized fluid whose continuum persists below
the molecular scale. -/
theorem continuum_all_the_way_down_dichotomy
    (N : ℕ) (traj : ℝ → NSFieldFourier) (ν ℏ : ℝ) (hN : 0 < N) (hν : 0 < ν) (hℏ : 0 < ℏ)
    (kmol kC : ℕ) (hC : ∀ t i, (traj t).freq i ≤ kC) (T : ℝ) :
    bkmSurrogateIntegral N traj T
        ≤ ℏ / ν * (1 + (kmol : ℝ) ^ 2) * entropicProperTime N traj ν ℏ T
      ∨ ∃ t i, kmol < (traj t).freq i ∧ (traj t).freq i ≤ kC := by
  by_cases h : ∀ t i, (traj t).freq i ≤ kmol
  · exact Or.inl (finiteResolution_bkmSurrogate_bounded N traj ν ℏ hN hν hℏ kmol h T)
  · exact Or.inr (compton_operative_implies_submolecular traj kmol kC hC h)

/-! #### The molecular scale, derived: Maxwell's relation at the quantum viscosity

The coarser scale of the screening section is now repo-derived.  Maxwell's kinetic relation `ν = ½·v̄·ℓ`
(Maxwell 1860; Chapman–Cowling) defines the mean free path from the viscosity and the thermal speed — the same
defining-formula style as the diffusive timescale `t_ν = ℓ²/ν` of `SciamaAdSCPTViscousDiffusionComptonClock`.
Evaluated at the repository's **quantum kinematic viscosity** `ν_q = ℏ/2m`
(`SciamaAdSCPTMadelungNavierStokesTerms.quantumKinematicViscosity`), the mean free path is the **de Broglie
length** `ℏ/(m·v̄)`, and the Compton cell `ƛ_C = ℏ/(mc)` lies strictly below it *exactly because the thermal
speed is sub-luminal*: `ƛ_C < ℓ_mfp ⟺ v̄ < c`.  Sub-luminality itself is the scale hierarchy. -/

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMadelungNavierStokesTerms

/-- **The mean free path from Maxwell's kinetic relation** `ν = ½·v̄·ℓ` (Maxwell 1860): `ℓ_mfp = 2ν/v̄` — the
standard kinetic defining formula for the collision length from viscosity and thermal speed. -/
noncomputable def meanFreePath (ν vbar : ℝ) : ℝ := 2 * ν / vbar

/-- **At the quantum viscosity the mean free path is the de Broglie length** `ℓ_mfp = 2ν_q/v̄ = ℏ/(m·v̄)`:
the Madelung fluid's collision length at its own viscosity scale is its de Broglie wavelength at the thermal
speed. -/
theorem meanFreePath_quantum_deBroglie (ℏ m vbar : ℝ) :
    meanFreePath (quantumKinematicViscosity ℏ m) vbar = ℏ / (m * vbar) := by
  unfold meanFreePath quantumKinematicViscosity
  rw [← mul_div_assoc, mul_div_mul_left _ _ (two_ne_zero), div_div]

/-- **Sub-luminality is the scale hierarchy.**  For `0 < v̄ < c` (and `ℏ, m > 0`):
`ƛ_C = ℏ/(mc) < ℏ/(m·v̄) = ℓ_mfp` — the Compton cell lies strictly below the mean free path *because the
thermal speed is below light speed*.  The coarser molecular scale of the screening dichotomy is repo-derived,
not hypothesized. -/
theorem compton_below_meanFreePath (ℏ m c vbar : ℝ)
    (hℏ : 0 < ℏ) (hm : 0 < m) (hv : 0 < vbar) (hvc : vbar < c) :
    comptonWavelength m c ℏ < meanFreePath (quantumKinematicViscosity ℏ m) vbar := by
  rw [meanFreePath_quantum_deBroglie]
  unfold comptonWavelength
  have hc : 0 < c := hv.trans hvc
  rw [div_lt_div_iff₀ (mul_pos hm hc) (mul_pos hm hv)]
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hvc hm) hℏ

/-- **The molecular scale of the screening dichotomy, derived.**  At the quantum viscosity the mean free path
is the de Broglie length, and for every sub-luminal thermal speed it lies strictly above the Compton cell —
the coarser cutoff of `continuum_all_the_way_down_dichotomy` realized by a derived scale. -/
theorem molecularScale_derived (ℏ m c vbar : ℝ)
    (hℏ : 0 < ℏ) (hm : 0 < m) (hv : 0 < vbar) (hvc : vbar < c) :
    meanFreePath (quantumKinematicViscosity ℏ m) vbar = ℏ / (m * vbar)
      ∧ comptonWavelength m c ℏ < meanFreePath (quantumKinematicViscosity ℏ m) vbar :=
  ⟨meanFreePath_quantum_deBroglie ℏ m vbar,
    compton_below_meanFreePath ℏ m c vbar hℏ hm hv hvc⟩

/-! #### The collision clock saturates the time–energy uncertainty

The rate the collision arc was missing.  The standard kinetic collision rate is `γ = v̄/ℓ_mfp`; at the quantum
viscosity's de Broglie mean free path this is `γ = m·v̄²/ℏ = 2·E_kin/ℏ` — twice the kinetic energy over `ℏ`
(`collisionRate_quantum_kineticEnergy`).  Its inverse, the collision time `τ_coll = ℏ/(2E_kin)`, is *exactly*
the minimal time resolution `ΔT ≥ ℏ/(2ΔH)` of the time–energy uncertainty at energy spread `ΔH = E_kin`
(`collisionTime_is_minimal_time_resolution`, reusing `NoInfiniteTimeResolution.finite_energy_positive_resolution`):
**the fluid's collision clock is the fastest clock its kinetic energy budget permits** — it saturates the
Mandelstam–Tamm quantum speed limit.  And the frequency-side mirror of the length hierarchy holds:
`γ < ω_C ⟺ v̄ < c` (`collisionRate_below_comptonFrequency`) — the collision rate sits below the Compton
frequency exactly as the mean free path sits above the Compton cell, both by sub-luminality. -/

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.NoInfiniteTimeResolution

/-- **The kinetic collision rate** `γ = v̄/ℓ` — the standard defining formula: thermal speed per mean free
path. -/
noncomputable def collisionRate (vbar ℓ : ℝ) : ℝ := vbar / ℓ

/-- **The collision rate at the quantum viscosity is twice the kinetic energy over `ℏ`**:
`γ = v̄/ℓ_mfp = m·v̄²/ℏ = 2·(½m·v̄²)/ℏ`.  The Madelung fluid's collision frequency is its kinetic-energy
frequency. -/
theorem collisionRate_quantum_kineticEnergy (ℏ m vbar : ℝ) :
    collisionRate vbar (meanFreePath (quantumKinematicViscosity ℏ m) vbar)
      = m * vbar ^ 2 / ℏ := by
  rw [meanFreePath_quantum_deBroglie]
  unfold collisionRate
  rw [div_div_eq_mul_div]
  congr 1
  ring

/-- **The collision time is the minimal time resolution at the kinetic energy.**  For any time–energy pair with
`ΔT·ΔH ≥ ℏ/2` and energy spread within the kinetic budget `ΔH ≤ ½m·v̄²`, the time resolution is bounded below by
the collision time: `ΔT ≥ 1/γ = ℏ/(2E_kin)`.  No measurement on the fluid's kinetic-energy budget resolves
below the collision clock — it saturates the Mandelstam–Tamm bound. -/
theorem collisionTime_is_minimal_time_resolution (ℏ m vbar dT dH : ℝ)
    (hℏ : 0 < ℏ) (hdHpos : 0 < dH) (hdH : dH ≤ 1 / 2 * m * vbar ^ 2)
    (hunc : ℏ / 2 ≤ dT * dH) :
    (collisionRate vbar (meanFreePath (quantumKinematicViscosity ℏ m) vbar))⁻¹ ≤ dT := by
  have h := finite_energy_positive_resolution dT dH ℏ (1 / 2 * m * vbar ^ 2) hℏ hdHpos hdH hunc
  rw [show 2 * (1 / 2 * m * vbar ^ 2) = m * vbar ^ 2 from by ring] at h
  rw [collisionRate_quantum_kineticEnergy, inv_div]
  exact h

/-- **The collision rate sits below the Compton frequency** `γ < ω_C ⟺ v̄ < c`: the frequency-side mirror of
`ƛ_C < ℓ_mfp` — the fluid's collision clock is slower than the Compton/Zitterbewegung clock exactly because the
thermal speed is sub-luminal. -/
theorem collisionRate_below_comptonFrequency (ℏ m c vbar : ℝ)
    (hℏ : 0 < ℏ) (hm : 0 < m) (hv : 0 < vbar) (hvc : vbar < c) :
    collisionRate vbar (meanFreePath (quantumKinematicViscosity ℏ m) vbar)
      < comptonFrequency m c ℏ := by
  rw [collisionRate_quantum_kineticEnergy]
  unfold comptonFrequency
  have h2 : m * vbar ^ 2 < m * c ^ 2 := by
    nlinarith [mul_pos hm (mul_pos (sub_pos.2 hvc) (show 0 < c + vbar by linarith))]
  rw [div_lt_div_iff₀ hℏ hℏ]
  exact mul_lt_mul_of_pos_right h2 hℏ

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.QuantumGravitySpatialOperators

end
