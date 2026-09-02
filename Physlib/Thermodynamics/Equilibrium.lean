/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.Thermodynamics.FirstLaw
public import Physlib.Thermodynamics.SecondLaw
public import Physlib.Thermodynamics.FreeEnergy
public import Physlib.ClassicalMechanics.Noether.DissipativeBalance
public import Physlib.QuantumMechanics.FrozenLimit

/-!
# Thermodynamic equilibrium ⇔ frozen LRF, and the recovery theorem

Phase 5 of the counterpart program (C2 + C4).

* **C2 — `thermalEquilibrium_implies_frozen_metric`** records the
  forward identification:  if two density matrices are equal (the
  entropic-side definition of thermodynamic equilibrium) then the
  dimensional entropic proper-time metric `entropicProperTimeMetric`
  vanishes between them.  This is the thermodynamic-equilibrium
  reading of `entropicProperTimeMetric_self`.

* **C4 — `equilibrium_recovery_capstone`** packages the entire
  Phase-1/2/4 equality-case library:  *given* an
  `EntropyArrowWorldline` that is reversible, an
  `EntropicNoetherWorldline`-style `NoetherBalance` with zero
  integrated defect, a `ThermodynamicWorldline` with zero net
  (heat − work), and a `HelmholtzWorldline` at equilibrium, *then*
  Clausius equality, internal-energy conservation, Noether charge
  conservation, and Helmholtz free-energy conservation all hold
  simultaneously.

This is the thermodynamic-side analog of `Physlib.QuantumMechanics.
FrozenLimit.frozen_limit_recovers_standard_physics`: a single
top-level theorem asserting *everything reverts* at the frozen LRF.

the recovery theorem is a structural assembly of the
already-proven equality-case theorems.


## References

- **Gibbs 1902** — *Elementary Principles in Statistical Mechanics*
- **Boltzmann 1872** — *Weitere Studien über das Wärmegleichgewicht (H-theorem)*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.Equilibrium

open Physlib.Thermodynamics.SecondLaw
open Physlib.Thermodynamics.FirstLaw
open Physlib.Thermodynamics.FreeEnergy
open Physlib.ClassicalMechanics.Noether.DissipativeBalance
open QuantumInfo.Finite

variable {d : Type*} [Fintype d] [DecidableEq d]


/-- **Thermal equilibrium between two states** (entropic-side definition):
the two states coincide.  This matches the standard statistical-mechanics
notion that two subsystems at equilibrium share an identical (Gibbs)
density matrix at the common temperature. -/
def IsThermalEquilibrium {d : Type*} [Fintype d] [DecidableEq d]
    (ρ σ : MState d) : Prop := ρ = σ

/-- **C2 — Thermal equilibrium implies the frozen-LRF metric.** Given
two density matrices in thermal equilibrium (`ρ = σ`), the dimensional
entropic proper-time metric `entropicProperTimeMetric` vanishes between
them for *any* choice of entropic-time units.

The reverse direction (`entropicProperTimeMetric = 0 ⇒ ρ = σ`) is the
quantum *Klein* inequality, which requires non-degeneracy hypotheses
on the relative entropy and is a separate development; it is left to
upstream `QuantumInfo` infrastructure. -/
lemma thermalEquilibrium_implies_frozen_metric
    (U : EntropicTimeUnits) (ρ σ : MState d)
    (h : IsThermalEquilibrium ρ σ) :
    entropicProperTimeMetric U ρ σ = 0 := by
  rw [h]; exact entropicProperTimeMetric_self U σ

/-- **Symmetric counterpart**: thermal equilibrium implies the
*complex* proper-time metric is purely real and equals the geometric
Minkowski interval. -/
lemma thermalEquilibrium_implies_complex_real_at_frozen
    (U : EntropicTimeUnits) {sd : ℕ}
    (q p : SpaceTime sd) (ρ σ : MState d)
    (h : IsThermalEquilibrium ρ σ) :
    complexProperTimeMetric U q p ρ σ = (geometricInterval q p : ℂ) := by
  rw [h]; exact complexProperTimeMetric_at_frozen U q p σ


/-- **C4 — Equilibrium recovery (record form).**  At thermal
equilibrium / frozen LRF, *every* Phase-1/2/4 equality-case theorem
holds simultaneously.  Each field is a Phase-K equality:

* `clausiusEquality_holds` — Clausius equality (Phase 1, B1).
* `internalEnergyConserved` — first-law conservation (Phase 2, B3).
* `noetherChargeConserved` — Noether charge conservation (A2).
* `helmholtzFree_constant` — Helmholtz free energy conservation (B4).

The fields are the *outputs* of the already-proven equality-case
theorems; the carrier records that they all hold for a single
equilibrium tuple. -/
structure EquilibriumRecovery
    (Warr : EntropyArrowWorldline)
    (Nbal : NoetherBalance)
    (TW   : ThermodynamicWorldline)
    (HW   : HelmholtzWorldline)
    (t₁ t₂ : ℝ) : Prop where
  /-- Clausius equality (entropic-time gap vanishes). -/
  clausiusEquality_holds :
    Warr.τ_ent_along t₂ - Warr.τ_ent_along t₁ = 0
  /-- Internal energy conserved over the interval. -/
  internalEnergyConserved : TW.U t₂ = TW.U t₁
  /-- Noether charge conserved over the interval. -/
  noetherChargeConserved : Nbal.Q t₂ = Nbal.Q t₁
  /-- Helmholtz free energy conserved over the interval. -/
  helmholtzFree_constant : HW.helmholtz t₁ = HW.helmholtz t₂

/-- **C4 — Equilibrium recovery (constructive form).**  Given
the equality-case hypotheses (reversible entropy arrow, zero integrated
Noether defect, zero net heat-minus-work, frozen `U` and `S` on the
Helmholtz worldline), build an `EquilibriumRecovery` record where all
four equality-case theorems hold simultaneously.

This is the load-bearing "everything reverts at the frozen LRF"
theorem on the thermodynamic side, mirroring `frozen_limit_recovers_standard_physics`
in `Physlib.QuantumMechanics.FrozenLimit`. -/
lemma equilibrium_recovery_capstone
    (Warr : EntropyArrowWorldline)
    (Nbal : NoetherBalance)
    (TW   : ThermodynamicWorldline)
    (HW   : HelmholtzWorldline)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂)
    (hRev   : Warr.IsReversible)
    (hQzero : ∫ t in t₁..t₂, Nbal.defect t = 0)
    (hHWzero : ∫ t in t₁..t₂, (TW.dQ_dt t - TW.dW_dt t) = 0)
    (hU_const : ∀ s₁ s₂ : ℝ, HW.U s₁ = HW.U s₂)
    (hS_const : ∀ s₁ s₂ : ℝ, HW.S s₁ = HW.S s₂) :
    EquilibriumRecovery Warr Nbal TW HW t₁ t₂ where
  clausiusEquality_holds := Warr.clausius_equality_at_frozen hRev
  internalEnergyConserved :=
    ((TW.internalEnergy_conserved_iff_zero_net_heatWork h).mpr hHWzero)
  noetherChargeConserved :=
    ((Nbal.charge_conserved_iff_zero_integrated_defect h).mpr hQzero)
  helmholtzFree_constant :=
    HW.helmholtzFreeEnergy_constant_at_equilibrium hU_const hS_const t₁ t₂


/-- **Combined entropic chain theorem — quantum-frozen and thermal-equilibrium
recovery simultaneously.**  Given a `FrozenContext` `C` (quantum side: `H_I = 0`
and any diagonal state `ρ`) together with the four equality-case witnesses on
the thermodynamic side (reversible entropy arrow, zero integrated Noether
defect, zero net heat-minus-work, frozen internal energy and entropy on the
Helmholtz worldline), *both* recovery records hold simultaneously:

* on the **quantum side** the full `FrozenRecovery` record holds — total
  proper time reduces to geometric proper time, the complex Hamiltonian
  reduces to the reversible generator, entropy-production and norm-decay
  rates vanish, etc.;
* on the **thermodynamic side** the full `EquilibriumRecovery` record holds —
  Clausius equality, first-law conservation, Noether-charge conservation,
  and Helmholtz-free-energy conservation.

This packages the load-bearing "everything reverts at the frozen LRF" content
on both sides of the entropic chain into a single composed theorem.  No new
axioms; it is the simultaneous application of
`frozen_limit_recovers_standard_physics` and `equilibrium_recovery_capstone`. -/
lemma thermalEquilibrium_at_quantumFrozenLimit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    {sd : ℕ}
    (C : Physlib.QuantumMechanics.FrozenLimit.FrozenContext (H := H) (d := d) (sd := sd))
    (q p : SpaceTime sd) (ψ : H) (x : SpaceTime sd) (Γ_inf : ℝ)
    (Warr : EntropyArrowWorldline) (Nbal : NoetherBalance)
    (TW   : ThermodynamicWorldline) (HW   : HelmholtzWorldline)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂)
    (hRev    : Warr.IsReversible)
    (hQzero  : ∫ t in t₁..t₂, Nbal.defect t = 0)
    (hHWzero : ∫ t in t₁..t₂, (TW.dQ_dt t - TW.dW_dt t) = 0)
    (hU_const : ∀ s₁ s₂ : ℝ, HW.U s₁ = HW.U s₂)
    (hS_const : ∀ s₁ s₂ : ℝ, HW.S s₁ = HW.S s₂) :
    Physlib.QuantumMechanics.FrozenLimit.FrozenRecovery C q p ψ x Γ_inf
    ∧ EquilibriumRecovery Warr Nbal TW HW t₁ t₂ :=
  ⟨Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics
      C q p ψ x Γ_inf,
   equilibrium_recovery_capstone Warr Nbal TW HW h hRev hQzero hHWzero hU_const hS_const⟩

end Physlib.Thermodynamics.Equilibrium

end
