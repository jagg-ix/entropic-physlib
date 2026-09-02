/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3
meta import Zil

/-!
# Discharging three conditionals of the entropic-dynamics thesis

The thesis theorem `Physlib.Meta.EntropicDynamicsThesis.entropicDynamics_derives_physics` is
explicitly conditional. Three of its flagged caveats are discharged here by *existing derivations*
already in the repository, composed into one synthesis:

* **IV — analytic `Γ → ∞` frozen limit.** The thesis reduces the frozen sector exactly at the premise
  `H_I = 0`; it "is not an analytic `Γ → ∞` convergence theorem". `suppression_tendsto_one` supplies
  exactly that: the entropic path-integral weight `exp(−S_I/ℏ) → 1` as the rapidity `η → ∞`.
* **V-a — non-circular screen-coupling identity.** The thesis solves
  `G = 𝒜c³/(ℏN)` only after
  assuming `N = holographicBits(…,G,…)`, which already contains `G`. `newtonG_from_positionVariance`
  gives the same area-per-cell expression with `N = comptonCellBits` and value
  `ℏc·σ₀⁴`, without
  putting `G` in the count. `gaussianFisherScreenCoupling_eq` further constructs the reciprocal
  variance from the Gaussian score integral and uniquely characterizes the effective count by
  `N λ² = A`. This discharges the mathematical circularity, not the separate claim that the
  constructed screen coupling is the Newton constant measured in gravitational experiments.
* **V-b — the Einstein source is a consequence of the Poisson law.** The thesis takes the complex
  Einstein source as an explicit premise. `weakFieldRicci00_at` shows the weak-field `R₀₀` component
  equals `4πGρ/c²` *as a consequence of* the field's Poisson law, i.e. the Newtonian Einstein source
  is a conclusion, not an independent assumption.

This is a composition of audited derivations; it does not claim to have removed *every* conditional of
the thesis (the Born-weight premise II remains).  The separate
`EntropicDynamicsFullEinsteinSource` module subsequently discharges the full nonlinear source inside
the explicit electrogravitic field-equation structure.
-/

set_option autoImplicit false

open Filter Topology
open Physlib.QuantumMechanics.ComplexAction.ComptonClock
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.Thermodynamics

@[expose] public section

namespace Physlib.Meta.EntropicDynamicsThesisConditionals

/-- **[Three mathematical gaps in the entropic-dynamics thesis, discharged].**
Composes three existing
derivations that each remove a mathematical gap of `entropicDynamics_derives_physics`:
**(IV)** the analytic `η → ∞` frozen-limit convergence `exp(−S_I/ℏ) → 1`;
**(V-a)** the *non-circular* area-per-cell screen coupling `𝒜c³/(ℏN) = ℏc·σ₀⁴` with
the `G`-free effective count `N = comptonCellBits`; and
**(V-b)** the weak-field Einstein `R₀₀` source `= 4πGρ/c²` as a consequence of the Poisson law. -/
@[zil_level physical_theorem]
theorem entropicDynamics_thesisConditionals_discharged
    (ħ σ₀ c η cE : ℝ) (hσ : σ₀ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hK : Real.log (schmidtNumber η) ≠ 0)
    (F : StaticPoissonField3) (x : StaticPotentialSpace3) :
    -- IV. the analytic `η → ∞` frozen limit the thesis lacked.
    Tendsto (fun τ : ℝ => Real.exp (-(entropicAction ħ τ / ħ))) atTop (𝓝 1)
    -- V-a. the holographic Newton identity, non-circular: `N = comptonCellBits` is `G`-free.
      ∧ sphereArea (entropicProperDistance (inferenceMass σ₀) c ħ η) * c ^ 3
          / (ħ * comptonCellBits (inferenceMass σ₀) c ħ η) = ħ * c * σ₀ ^ 4
    -- V-b. the weak-field Einstein `R₀₀` source as a consequence of the Poisson law.
      ∧ weakFieldRicci00 (laplacianAt3 F.potential x) cE
          = 4 * Real.pi * F.newtonConstant * F.density x / cE ^ 2 :=
  ⟨suppression_tendsto_one ħ,
   newtonG_from_positionVariance σ₀ c ħ η hσ hc hħ hK,
   weakFieldRicci00_at F cE x⟩

end Physlib.Meta.EntropicDynamicsThesisConditionals

end

/- ZIL-BEGIN -/

zil attach Physlib.Meta.EntropicDynamicsThesisConditionals.entropicDynamics_thesisConditionals_discharged where
  formalizes @ "claim:three-mathematical-gaps-of-the-entropic-dynamics-thesis-theorem-\
are-discharged-by-existing-derivations-the-analytic-rapidity-to-infinity-frozen-limit-\
suppression-tends-to-one-the-non-circular-area-per-cell-screen-coupling-with-the-g-free-\
effective-count-and-the-weak-field-einstein-r00-source-as-a-consequence-of-the-poisson-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.weakFieldRicci00_at",
  caveat @ "epistemic:the-screen-coupling-is-constructed-without-g-in-its-count-but-\
identifying-it-with-the-empirically-measured-newton-constant-remains-a-separate-physical-claim",
  caveat @ "claim:the-born-weight-premise-two-remains-and-the-full-nonlinear-source-is-discharged-separately-inside-the-explicit-electrogravitic-field-equation-structure"

zil_file_contract physlib.entropicDynamicsThesisConditionals where
  promises "Three mathematical gaps of the entropic-dynamics thesis theorem entropicDynamics_derives_physics are discharged by existing repository derivations, composed into one synthesis. IV: the analytic rapidity-to-infinity frozen limit exp(-S_I/hbar) tends to one (suppression_tendsto_one), supplying the Gamma-to-infinity convergence the thesis lacked (it reduced the frozen sector only exactly at H_I = 0). V-a: the non-circular area-per-cell screen coupling A c^3/(hbar N) equals hbar c sigma0^4 with N the G-free effective Compton-area count, removing the circularity of the thesis's N = holographicBits(G) premise. The Gaussian-Fisher capstone separately proves the score-integral and unique-area-balance construction. Identifying this constructed coupling with measured Newton G remains a physical claim. V-b: the weak-field Einstein R00 source equals 4 pi G rho/c^2 as a consequence of the field's Poisson law (weakFieldRicci00_at), making the Newtonian Einstein source a conclusion rather than an independent premise. Honest: this composes audited derivations and does not remove every physical conditional; the Born-weight premise II and the Newton-coupling identification remain. The full nonlinear source is discharged separately inside the explicit electrogravitic field-equation structure."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.suppression_tendsto_one",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.weakFieldRicci00_at"]
  forbids_substitutes ["the exact H_I = 0 frozen reduction alone, whereas IV supplies the analytic rapidity-to-infinity convergence",
    "the circular N = holographicBits(G) identification, whereas V-a uses the G-free Compton-cell count",
    "calling the constructed information-screen coupling measured Newton G without an \
independent physical identification",
    "an assumed complex Einstein source, whereas V-b derives the weak-field R00 source from the Poisson law"]
  witnessed_by [Physlib.Meta.EntropicDynamicsThesisConditionals.entropicDynamics_thesisConditionals_discharged]

/- ZIL-END -/
