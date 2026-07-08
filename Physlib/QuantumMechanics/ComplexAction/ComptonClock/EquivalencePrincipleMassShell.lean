/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell

/-!
# The Einstein equivalence principle for the Compton clock: the rest mass is the Lorentz invariant

The doubly-boosted Compton clock of `ComptonClock.EntanglementReparametrization`,
`ω = (cosh θ · cosh η) ω_C`, splits into a *frame/entanglement-dependent* boost (`cosh θ` from the
momentum rapidity, `cosh η` from the Schmidt rapidity) times an *invariant* rest frequency
`ω_C = mc²/ℏ`. The **Einstein equivalence principle** — physics is locally the same in every inertial
(local Lorentz) frame — is exactly the statement that this `ω_C` is a Lorentz scalar: the boost is pure
inertial gauge, only the rest mass is physical.

This is the energy–momentum counterpart of the tetrad gauge invariance of
`CanonicalTetradGravity.ComptonVacuumBell`, where the *spatial* proper separation `xᵀ g x`
(`properSeparationSq`) is unchanged by the local Lorentz frame rotation `E ↦ ΛE`, `Λ ∈ SO(1,3)`
(`properSeparationSq_lorentz_gauge`).

* **§A — the mass-shell invariant.** `einstein_massShell` (`(E/c)² − p² = (mc)²`) and
 `massShell_rapidity_invariant` (`(mc·cosh θ)² − (mc·sinh θ)² = (mc)²`): the rest mass `mc` is the
 Minkowski invariant of the full Einstein energy–momentum `(E/c, p)`, unchanged by the kinematic boost
 `cosh θ` — the value of the invariant that includes the Compton rest frequency `ω_C`.
* **§B — the tetrad local-Lorentz-gauge invariance.** `fourMomentum_norm_tetrad_gauge_invariant`: the
 same tetrad Minkowski form `properSeparationSq` that gauges the spatial separation, applied to the
 energy–momentum 4-vector `(E/c, p)`, is unchanged by `E ↦ ΛE` — the equivalence-principle statement that
 the rest-mass invariant (hence `ω_C`) is frame-independent.

`§A` is exact scalar algebra. `§B` reuses `properSeparationSq_lorentz_gauge` on the
energy–momentum vector, so its Minkowski norm is a Lorentz-gauge scalar; that this norm *equals* the
`§A` value `(mc)²` is the (heavier) explicit `minkowskiMatrix` quadratic-form computation, indicated in
prose rather than performed here. The reading of the boost as an inertial-gauge / equivalence-principle
statement is the interpretive framework.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell

/-! ## §A — the mass-shell invariant `(E/c)² − p² = (mc)²` -/

/-- **The energy–momentum invariant is the rest mass** `(E/c)² − p² = (mc)²`: for the full Einstein energy
`E = √((mc²)²+(pc)²)`, the Minkowski norm of the 4-momentum `(E/c, p)` is the rest mass `(mc)²`,
independent of the momentum `p` — the invariant encoded in the Compton rest frequency `ω_C = mc²/ℏ`. -/
theorem einstein_massShell (m c p : ℝ) (hc : c ≠ 0) :
    (einsteinEnergy m c p / c) ^ 2 - p ^ 2 = (m * c) ^ 2 := by
  rw [div_pow, einsteinEnergy_sq]
  field_simp
  ring

/-- **The rest mass is invariant under the kinematic boost** `(mc·cosh θ)² − (mc·sinh θ)² = (mc)²`: writing
`(E/c, p) = mc·(cosh θ, sinh θ)` (`einsteinEnergy_eq_rest_cosh_rapidity`), the momentum rapidity `θ` rotates
energy into momentum hyperbolically but leaves the rest mass — hence `ω_C` — fixed. -/
theorem massShell_rapidity_invariant (m c θ : ℝ) :
    (m * c * Real.cosh θ) ^ 2 - (m * c * Real.sinh θ) ^ 2 = (m * c) ^ 2 := by
  linear_combination ((m * c) ^ 2) * Real.cosh_sq_sub_sinh_sq θ

/-! ## §B — the tetrad local-Lorentz-gauge invariance of the 4-momentum norm -/

/-- **The energy–momentum 4-vector** `(E/c, p)` with `E = √((mc²)²+(pc)²)` the full Einstein energy — the
timelike partner of the spacelike separation vector of `CanonicalTetradGravity.ComptonVacuumBell`. -/
noncomputable def fourMomentum (m c p : ℝ) : Fin 1 ⊕ Fin 1 → ℝ :=
  Sum.elim (fun _ => einsteinEnergy m c p / c) (fun _ => p)

/-- **[Equivalence principle] the 4-momentum's tetrad Minkowski norm is local-Lorentz-gauge invariant**:
`properSeparationSq (ΛE) P = properSeparationSq E P`. The same tetrad Minkowski form that leaves the
spatial proper separation invariant (`properSeparationSq_lorentz_gauge`) leaves the energy–momentum norm —
the rest-mass invariant `(mc)²` of §A, with the Compton rest frequency `ω_C` — unchanged under the
local inertial-frame rotation `E ↦ ΛE`. The boost is pure inertial gauge; only the rest mass is physical. -/
theorem fourMomentum_norm_tetrad_gauge_invariant
    {Λ E : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ} (hΛ : Λ ∈ LorentzGroup 1) (m c p : ℝ) :
    properSeparationSq (Λ * E) (fourMomentum m c p) = properSeparationSq E (fourMomentum m c p) :=
  properSeparationSq_lorentz_gauge hΛ (fourMomentum m c p)

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell

end
