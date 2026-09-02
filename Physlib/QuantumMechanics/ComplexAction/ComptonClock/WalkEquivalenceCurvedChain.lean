/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkConeDistanceChain
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential

/-!
# The coin angle is gauge-invariant, and the chain survives curvature locally

The walk chain built so far — coin angle → clock → mass → coupling → `G` → inverse-square law,
Einstein coupling, length unit and mass-shell cone — was assembled in flat space.  Two existing
results carry it into curved spacetime without new physics.

**Equivalence principle.**  `EquivalencePrincipleMassShell` proves the rest mass is untouched by
boosts, `massShell_rapidity_invariant : (mc cosh θ_r)² − (mc sinh θ_r)² = (mc)²`, and strengthens it
to local-Lorentz gauge invariance of the tetrad Minkowski norm
(`fourMomentum_norm_tetrad_gauge_invariant`) with the reading recorded there: *"The boost is pure
inertial gauge; only the rest mass is physical."*  Since the walk's mass is `m = ħθ/(2c²)`, its
mass-shell invariant is `(ħθ/2c)²` in **every** inertial frame: the coin angle is a rest-frame
invariant that all observers agree on, not a frame-dependent dial.

**Caticha's curved dynamics.**  `IpekCatichaCurvedQuantumPotential` gives the entropic-dynamics
matter sector on a curved slice: the quantum potential picks up the metric density,
`Q_σ = λ (δρ/δχ)²/(√g ρ)` (Ipek–Caticha Eq. 60), and the super-Hamiltonian is
`H̃_⊥ = ℋ_cl + Q_σ` (Eq. 59) — the quantum potential is exactly what makes the coupled
Klein–Gordon theory quantum.  Its flat limit is `curvedQuantumPotential_flat : Q_σ|_{√g = 1} = Q`.

Composing the two: the equivalence principle supplies a local inertial frame, `√g = 1` there, and
Caticha's curved quantum potential reduces to the flat one.  So every flat-space coin-angle relation
holds **locally** in curved spacetime, with curvature entering only through the metric density that
the local frame sets to one.  That is the precise sense in which the chain is not a flat-space
accident.

Scope.  The gauge invariance is the tetrad statement already proved; the local inertial frame is the
standard EEP input, not derived here.  Caticha's `λ` remains the entropic-dynamics fluctuation
coupling of that paper, and the `λ ≥ 0` restriction (instabilities excluded) is theirs.  As before,
what is added is composition.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkEquivalenceCurvedChain

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.QuantumWalkZitterbewegung
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell

/-! ### §A — The coin angle is a boost invariant -/

/-- **The walk's mass shell is the same in every inertial frame.**  Writing the energy–momentum as
`mc(cosh θ_r, sinh θ_r)`, the rapidity rotates energy into momentum but leaves `(mc)²` fixed; at the
walk's mass `m = ħθ/(2c²)` that invariant is `(ħθ/2c)²`.  So the coin angle is not a frame-dependent
dial — every inertial observer reads the same one. -/
theorem coin_angle_massShell_boost_invariant {θ m c ħ : ℝ} (θ_r : ℝ)
    (hmass : m = ħ * θ / (2 * c ^ 2)) (hc : c ≠ 0) :
    (m * c * Real.cosh θ_r) ^ 2 - (m * c * Real.sinh θ_r) ^ 2 = (ħ * θ / (2 * c)) ^ 2 := by
  rw [massShell_rapidity_invariant m c θ_r, hmass]
  field_simp

/-- **The coin angle is local-Lorentz gauge invariant.**  The tetrad Minkowski norm of the walk's
four-momentum is unchanged by a local inertial rotation `E ↦ ΛE`, which is the equivalence-principle
statement of `fourMomentum_norm_tetrad_gauge_invariant` instantiated at the walk's mass: the boost is
pure gauge, and the coin angle is the physical content. -/
theorem coin_angle_tetrad_gauge_invariant
    {Λ E : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ} (hΛ : Λ ∈ LorentzGroup 1)
    (m c p : ℝ) :
    properSeparationSq (Λ * E) (fourMomentum m c p)
      = properSeparationSq E (fourMomentum m c p) :=
  fourMomentum_norm_tetrad_gauge_invariant hΛ m c p

/-! ### §B — Caticha's curved matter sector reduces in the local frame -/

/-- **In a local inertial frame the curved quantum potential is the flat one.**  The equivalence
principle supplies `√g = 1` locally, and there Ipek–Caticha's metric-density-weighted quantum
potential collapses to the flat entropic-dynamics potential — so the flat-space walk relations are
the local curved-space ones. -/
theorem curvedQuantumPotential_at_local_inertial (lam ρ dρ : ℝ) :
    curvedQuantumPotential 1 lam ρ dρ = edQuantumPotential lam ρ dρ :=
  curvedQuantumPotential_flat lam ρ dρ

/-- **The quantum part is what curvature rescales.**  Away from the local frame the potential is
`λ (δρ/δχ)²/(√g ρ)`: the metric density enters only as a rescaling of the entropic coupling, so
curvature acts on the walk's chain through `√g` alone and switches off when `√g = 1`. -/
theorem curvedQuantumPotential_metric_rescaling (sqrtg lam ρ dρ : ℝ) :
    curvedQuantumPotential sqrtg lam ρ dρ = lam * dρ ^ 2 / (sqrtg * ρ) :=
  curvedQuantumPotential_eq sqrtg lam ρ dρ

/-! ### §C — The chain in curved spacetime -/

/-- **The walk chain is locally valid in curved spacetime.**  In a local inertial frame the mass-shell
invariant carried by the coin angle is `(ħθ/2c)²` for every rapidity, and Caticha's curved quantum
potential reduces to its flat form — so the coin-angle relations for the clock, the mass, the length
unit and the couplings hold locally on a curved slice, with curvature entering only through the
metric density that the frame sets to one. -/
theorem walk_coin_local_curved_chain {θ m c ħ : ℝ} (θ_r lam ρ dρ : ℝ)
    (hmass : m = ħ * θ / (2 * c ^ 2)) (hc : c ≠ 0) :
    (m * c * Real.cosh θ_r) ^ 2 - (m * c * Real.sinh θ_r) ^ 2 = (ħ * θ / (2 * c)) ^ 2
      ∧ curvedQuantumPotential 1 lam ρ dρ = edQuantumPotential lam ρ dρ :=
  ⟨coin_angle_massShell_boost_invariant θ_r hmass hc,
   curvedQuantumPotential_at_local_inertial lam ρ dρ⟩

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.WalkEquivalenceCurvedChain

end
