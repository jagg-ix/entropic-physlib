/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The local-time Fokker–Planck equations (Ipek–Abedi–Caticha, Appendix A)

Formalizes the **local-time Fokker–Planck (LTFP) equations** of Ipek–Abedi–Caticha (*Reconstructing Quantum Field
Theory in Curved Space-time*, arXiv:1803.07493, Eqs. 16, 18, A.8). The probability `ρ_σ[χ]` flows as the surface
`σ` is deformed, obeying a diffusion (Fokker–Planck) equation written as a continuity equation in configuration
space. In the drift–diffusion form (Eq. A.8),

`δρ/δξ⊥ = (η/√g)[ −∂_χ(ρ ∂_χφ) + ½ ∂²_χ ρ ]`,

and in the equivalent current form (Eq. 16),

`δρ/δξ⊥ = −(1/√g) ∂_χ(ρ ∂_χΦ)`, with the **current potential** `Φ = φ − ½ log ρ`.

The equivalence of the two forms is the osmotic decomposition: the current velocity `∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ` is
the phase drift `∂_χφ` minus the osmotic velocity `½(∂_χρ)/ρ`, and the continuity flux `ρ ∂_χΦ = ρ∂_χφ − ½∂_χρ`
then differentiates to `∂_χ(ρ∂_χφ) − ½∂²_χρ`, so the current form reproduces the drift–diffusion form with its
diffusion term.

* the **current potential and osmotic velocity** `Φ = φ − ½ log ρ`, `∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ`
 (`currentPotential`, `currentPotential_hasDerivAt`) — the current velocity is the phase drift minus the osmotic
 velocity (Eq. 16);
* the **current flux is drift minus the osmotic current** `ρ ∂_χΦ = ρ∂_χφ − ½∂_χρ` (`ltfp_currentVelocity_flux`) —
 the continuity flux decomposes into the drift current and the diffusion (osmotic) current;
* the **continuity form equals the drift–diffusion form** — the flux `ρ∂_χφ − ½∂_χρ` differentiates to
 `∂_χ(ρ∂_χφ) − ½∂²_χρ` (`ltfp_flux_hasDerivAt`, reusing `fokkerPlanck_current_hasDerivAt`), so
 `−∂_χ(ρ∂_χΦ) = −∂_χ(ρ∂_χφ) + ½∂²_χρ`: the diffusion term `½∂²_χρ` emerges from the osmotic `−½∂_χρ` (Eqs. 16 ⟺ A.8);
* the **local-time / curved-space scaling** `δρ/δξ⊥ = −(1/√g)∂_χ(flux)` (`ltfpLocalRate`) reduces to the flat
 Fokker–Planck continuity equation `∂ρ/∂t = −∂_χ(flux)` at `√g = 1` (`ltfpLocalRate_flat`, Eq. 18).

So the LTFP equations are a Fokker–Planck continuity equation in configuration space, with current velocity the
gradient of the current potential `Φ = φ − ½ log ρ` (phase minus osmotic); the diffusion term is the osmotic part
of the current, and the `1/√g` factor is the curved-space local-time clock.

* **§A — the current potential and osmotic velocity** (`currentPotential`, `currentPotential_hasDerivAt`).
* **§B — the current flux is drift minus osmotic** (`ltfp_currentVelocity_flux`).
* **§C — the continuity/drift–diffusion equivalence** (`ltfp_flux_hasDerivAt`).
* **§D — the local-time scaling and flat limit** (`ltfpLocalRate`, `ltfpLocalRate_flat`).

The current potential and its derivative, the flux decomposition, the drift–diffusion flux
derivative, and the local-time scaling are exact one-dimensional (pointwise, functional-derivative → ordinary
derivative) calculus, reusing `fokkerPlanckCurrent`/`fokkerPlanck_current_hasDerivAt` and `HasDerivAt.log`. The full
functional derivation (Appendix A: the test-functional expansion, the singular transition kernel) is the referenced
content. No new axioms.

## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §3 & Appendix A (Eqs. 16, 18, A.8). Repo structure:
 `EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian` (`fokkerPlanckCurrent`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck

/-! ## §A — the current potential and osmotic velocity -/

/-- **The current potential** `Φ = φ − ½ log ρ` (Ipek–Abedi–Caticha Eq. 16) — the drift potential `φ` minus the
osmotic contribution `½ log ρ`; its gradient is the current velocity of the probability flow. -/
noncomputable def currentPotential (φ ρ : ℝ) : ℝ := φ - (1 / 2) * Real.log ρ

/-- **[The current velocity is the drift minus the osmotic velocity] `∂_χΦ = ∂_χφ − ½(∂_χρ)/ρ`.** The gradient of
the current potential `Φ = φ − ½ log ρ` is the phase drift `∂_χφ` minus the osmotic velocity `½(∂_χρ)/ρ` — the
current velocity of the local-time Fokker–Planck flow. -/
theorem currentPotential_hasDerivAt (φ ρ : ℝ → ℝ) (φ' ρ' x : ℝ) (hφ : HasDerivAt φ φ' x)
    (hρ : HasDerivAt ρ ρ' x) (hpos : ρ x ≠ 0) :
    HasDerivAt (fun y => currentPotential (φ y) (ρ y)) (φ' - (1 / 2) * (ρ' / ρ x)) x := by
  have hlog : HasDerivAt (fun y => Real.log (ρ y)) (ρ' / ρ x) x := hρ.log hpos
  unfold currentPotential
  exact hφ.sub (hlog.const_mul (1 / 2))

/-! ## §B — the current flux is drift minus osmotic -/

/-- **[The current flux is drift minus the osmotic current] `ρ ∂_χΦ = ρ∂_χφ − ½∂_χρ`.** The continuity flux
`ρ · (current velocity)` decomposes into the drift current `ρ∂_χφ` minus the osmotic (diffusion) current `½∂_χρ`,
since `ρ · ½(∂_χρ)/ρ = ½∂_χρ`. -/
theorem ltfp_currentVelocity_flux (ρ φ' ρ' : ℝ) (hρ : ρ ≠ 0) :
    ρ * (φ' - (1 / 2) * (ρ' / ρ)) = ρ * φ' - (1 / 2) * ρ' := by
  field_simp

/-! ## §C — the continuity/drift–diffusion equivalence -/

/-- **[The continuity flux differentiates to the drift–diffusion form].** The local-time Fokker–Planck current flux
`ρ∂_χφ − ½∂_χρ` (drift current minus osmotic current) has spatial derivative
`∂_χ(ρ∂_χφ) − ½∂²_χρ` — so the continuity form `−∂_χ(ρ∂_χΦ)` reproduces the drift–diffusion form
`−∂_χ(ρ∂_χφ) + ½∂²_χρ` (Ipek–Abedi–Caticha Eqs. 16 ⟺ A.8): the diffusion term `½∂²_χρ` emerges from the osmotic
current, reusing `fokkerPlanck_current_hasDerivAt` for the drift current. -/
theorem ltfp_flux_hasDerivAt (ρ dφ dρ : ℝ → ℝ) (ρ' dφ' ρ'' x : ℝ) (hρ : HasDerivAt ρ ρ' x)
    (hdφ : HasDerivAt dφ dφ' x) (hdρ : HasDerivAt dρ ρ'' x) :
    HasDerivAt (fun y => fokkerPlanckCurrent ρ dφ y - (1 / 2) * dρ y)
      (ρ' * dφ x + ρ x * dφ' - (1 / 2) * ρ'') x :=
  (fokkerPlanck_current_hasDerivAt ρ dφ ρ' dφ' x hρ hdφ).sub (hdρ.const_mul (1 / 2))

/-! ## §D — the local-time scaling and flat limit -/

/-- **The local-time Fokker–Planck rate** `δρ/δξ⊥ = −(1/√g) ∂_χ(flux)` — the flow rate of the probability per unit
local proper time `δξ⊥`, with the curved-space density `√g` (Ipek–Abedi–Caticha Eq. 16). -/
noncomputable def ltfpLocalRate (rootg fluxDeriv : ℝ) : ℝ := -(1 / rootg) * fluxDeriv

/-- **[The flat limit is the standard Fokker–Planck continuity equation] `∂ρ/∂t = −∂_χ(flux)`.** At a flat surface
(`√g = 1`, `δξ⊥ = dt`) the local-time rate is the standard Fokker–Planck continuity equation (Eq. 18). -/
theorem ltfpLocalRate_flat (fluxDeriv : ℝ) : ltfpLocalRate 1 fluxDeriv = -fluxDeriv := by
  unfold ltfpLocalRate
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck

end
