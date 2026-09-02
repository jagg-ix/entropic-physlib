/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.StandardLorentzBoost
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant

meta import Zil

/-!
# The remarkable relativistic vacuum: Bisognano–Wichmann modular flow & Reeh–Schlieder

Formalizes the algebraic-QFT vacuum structure reviewed in S. J. Summers, *Yet More Ado About Nothing:
The Remarkable Relativistic Vacuum State*, arXiv:0802.1854, and links it to the arc's modular /
Bogoliubov / boost machinery.

The two pillars:

* **Bisognano–Wichmann modular covariance** (Summers Eq. 5.2): for the wedge algebra `R(W)` and the
  vacuum `Ω`, the Tomita–Takesaki modular flow is a **geometric boost**,
  `Δ_W^{it} = U(λ_W(2πt))`, where `λ_{W_R}(t)` is the Lorentz boost in the `(t,x)` plane with matrix
  `[[cosh t, sinh t], [sinh t, cosh t]]` — exactly the arc's `thermoBogoliubov t`. So the vacuum
  modular flow at parameter `t` **is** the arc's Bogoliubov boost at rapidity `2πt`
  (`modularBoost`): a one-parameter group of proper Lorentz boosts (`modularBoost_group`,
  `modularBoost_lorentz`), whose time–time component is the Bogoliubov / Lorentz energy
  `cosh(2πt)` (`modularBoost_energy`). The rapidity rate `2π` is the **Unruh** KMS inverse temperature
  (`modularBoost_unruh`): the vacuum restricted to the wedge is thermal at `T = 1/2π`.

* **Reeh–Schlieder** (Summers Thm. 3.1): the vacuum is **cyclic and separating** for every local
  algebra. The separating half — *no nonzero local observable annihilates the vacuum* — gives, in GNS
  terms (`AlgebraicQFT.StarAlgebraGNSFormCommutant`), that **every local event has nonzero vacuum expectation**
  (`reehSchlieder_event_occurs`), and the vacuum expectation `⟨Ω, a*a Ω⟩` is real
  (`reehSchlieder_expectation_real`).

* **§A — Bisognano–Wichmann modular covariance** (`modularBoost`, `modularBoost_group`,
  `modularBoost_lorentz`, `modularBoost_energy`).
* **§B — the Unruh/KMS temperature** (`unruhInverseTemperature`, `modularBoost_unruh`).
* **§C — Reeh–Schlieder** (`IsSeparating`, `reehSchlieder_event_occurs`,
  `reehSchlieder_expectation_real`).

## References

* S. J. Summers, arXiv:0802.1854 (Eq. 5.2 modular covariance, Thm. 3.1 Reeh–Schlieder); J. Bisognano,
  E. Wichmann, J. Math. Phys. 16 (1975) 985. Repo carriers: `ThermoFieldDynamics.TFDImaginaryPart`/`ThermoFieldDynamics.TFDBogoliubovHopf`
  (`thermoBogoliubov`, `thermoBogoliubov_group`), `Lorentz.StandardLorentzBoost`,
  `AlgebraicQFT.StarAlgebraGNSFormCommutant` (`gnsForm`, `gns_self_real`), `ThermoFieldDynamics.KazamaTomitaTakesakiModular`.

See `AlgebraicQFT.SummersVacuumModularLinks` for the wiring of this file into the Tomita–Takesaki modular cluster
(the modular Hamiltonian as the `𝔰𝔬(1,3)` boost generator, the modular flow fixing the commutant, and
the modular energy as the standard Lorentz `γ`-factor).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

open Real
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.StandardLorentzBoost
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant


/-- **[Bisognano–Wichmann] the vacuum modular flow `Δ_W^{it}` is the wedge boost `λ_W(2πt)`** — the
geometric content of modular covariance. In the `(t,x)` wedge plane it is the arc's Bogoliubov boost
at rapidity `2πt`: `modularBoost t = thermoBogoliubov (2πt) = [[cosh 2πt, sinh 2πt],[sinh 2πt, cosh
2πt]]`. -/
noncomputable def modularBoost (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  thermoBogoliubov (2 * Real.pi * t)

/-- **[Δ⁰ = 1] the modular flow at `t = 0` is the identity.** -/
lemma modularBoost_zero : modularBoost 0 = 1 := by
  rw [modularBoost, mul_zero, thermoBogoliubov_zero]

/-- **[Modular automorphism group] `Δ^{is}·Δ^{it} = Δ^{i(s+t)}`.** The vacuum modular flow is a
*one-parameter group* of Lorentz boosts (the Tomita–Takesaki modular automorphism group, geometrically
the boost subgroup leaving the wedge invariant). -/
lemma modularBoost_group (s t : ℝ) : modularBoost s * modularBoost t = modularBoost (s + t) := by
  rw [modularBoost, modularBoost, modularBoost, thermoBogoliubov_group, mul_add]

/-- **[Modular flow is a proper Lorentz boost] `det Δ_W^{it} = 1`.** Each element of the vacuum modular
flow is a unimodular (proper) Lorentz transformation — modular covariance is *geometric*. -/
lemma modularBoost_lorentz (t : ℝ) : (modularBoost t).det = 1 :=
  thermoBogoliubov_det_one (2 * Real.pi * t)

/-- **[Modular energy = Bogoliubov / Lorentz energy] `(Δ_W^{it})₀₀ = cosh(2πt)`.** The time–time
component of the modular boost is the Bogoliubov / causal-diamond horizon energy at the modular
rapidity `2πt` (`= LorentzGroup.γ(tanh 2πt)`). -/
lemma modularBoost_energy (t : ℝ) :
    (modularBoost t) 0 0 = bogoliubovEnergy (Real.sinh (2 * Real.pi * t)) 1 := by
  rw [diamond_horizon_energy, modularBoost, thermoBogoliubov]
  norm_num [Matrix.cons_val_zero]


/-- **The Unruh KMS inverse temperature** `β = 2π` — the rapidity rate of the vacuum modular flow. The
vacuum restricted to the wedge is a KMS equilibrium state at temperature `T = 1/2π` with respect to the
boost (in natural units). -/
noncomputable def unruhInverseTemperature : ℝ := 2 * Real.pi

/-- **[Unruh effect] the modular flow is the boost at rapidity `β·t = 2π·t`.** The vacuum modular flow
runs at rapidity `2π` per unit modular time — the **Unruh** KMS inverse temperature `β = 2π`, so an
accelerated observer sees the vacuum as thermal at `T = 1/2π`. -/
lemma modularBoost_unruh (t : ℝ) :
    modularBoost t = thermoBogoliubov (unruhInverseTemperature * t) := by
  rw [modularBoost, unruhInverseTemperature]


variable {A : Type*} [Ring A] [StarRing A]

/-- **[Reeh–Schlieder, separating] the vacuum is separating for the local algebra** — `⟨Ω, a*a Ω⟩ = 0`
forces `a = 0`: no nonzero local observable annihilates the vacuum. -/
def IsSeparating (ω : A → ℂ) : Prop := ∀ a : A, gnsForm ω a a = 0 → a = 0

/-- **[Reeh–Schlieder, "any local event can occur"] nonzero observables have nonzero vacuum
expectation.** For the separating vacuum, every nonzero local observable `a` has `⟨Ω, a*a Ω⟩ ≠ 0` (the
contrapositive of separating) — in the vacuum, any local event has nonzero probability. -/
lemma reehSchlieder_event_occurs (ω : A → ℂ) (hsep : IsSeparating ω) (a : A) (ha : a ≠ 0) :
    gnsForm ω a a ≠ 0 :=
  fun h => ha (hsep a h)

/-- **[The vacuum expectation is real] `Im ⟨Ω, a*a Ω⟩ = 0`** (for a hermitian state `ω`,
`= AlgebraicQFT.StarAlgebraGNSFormCommutant.gns_self_real`) — the local-event probability `⟨Ω, a*a Ω⟩` is a real number. -/
lemma reehSchlieder_expectation_real (ω : A → ℂ)
    (herm : ∀ x, ω (star x) = starRingEnd ℂ (ω x)) (a : A) :
    (gnsForm ω a a).im = 0 :=
  gns_self_real ω herm a


/-- **[The remarkable vacuum, assembled].** Bisognano–Wichmann: the vacuum modular flow is a
one-parameter group (`modularBoost_group`) of proper Lorentz boosts (`modularBoost_lorentz`) at
rapidity `2πt` — the boost subgroup of the wedge — with energy `cosh(2πt)` (`modularBoost_energy`) and
Unruh KMS temperature `1/2π` (`modularBoost_unruh`). Reeh–Schlieder: in the separating vacuum every
nonzero local observable has nonzero (real) expectation (`reehSchlieder_event_occurs`). The vacuum's
modular structure is the arc's Bogoliubov boost; the vacuum is geometrically a thermal Lorentz flow. -/
lemma remarkable_vacuum (s t : ℝ) (ω : A → ℂ) (hsep : IsSeparating ω) (a : A) (ha : a ≠ 0) :
    modularBoost s * modularBoost t = modularBoost (s + t)
      ∧ (modularBoost t).det = 1
      ∧ (modularBoost t) 0 0 = bogoliubovEnergy (Real.sinh (2 * Real.pi * t)) 1
      ∧ modularBoost t = thermoBogoliubov (unruhInverseTemperature * t)
      ∧ gnsForm ω a a ≠ 0 :=
  ⟨modularBoost_group s t, modularBoost_lorentz t, modularBoost_energy t,
    modularBoost_unruh t, reehSchlieder_event_occurs ω hsep a ha⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost_group where
  formalizes @ "claim:the-vacuums-tomita-takesaki-modular-flow-is-a-one-parameter-group-of-lorentz-boosts-the-bisognano-wichmann-modular-automorphism-group-leaving-the-wedge-invariant",
  supported_by @ "paper:summers-arxiv-0802-1854-yet-more-ado-about-nothing-the-remarkable-relativistic-vacuum-state"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost_lorentz where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.StandardLorentzBoost.thermoBogoliubov_det_one",
  formalizes @ "claim:each-element-of-the-vacuum-modular-flow-is-a-proper-unimodular-determinant-one-lorentz-transformation-modular-covariance-is-geometric"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost_energy where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity.diamond_horizon_energy",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-time-time-component-of-the-modular-boost-equals-the-bogoliubov-horizon-energy-cosh-of-two-pi-t-at-modular-rapidity-two-pi-t-fixing-the-unruh-inverse-temperature-beta-equals-two-pi"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.reehSchlieder_event_occurs where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.gns_self_real",
  formalizes @ "claim:in-the-separating-reeh-schlieder-vacuum-every-nonzero-local-observable-has-nonzero-vacuum-expectation-value-so-any-local-event-has-nonzero-probability"

zil_file_contract physlib.summersRelativisticVacuum where
  promises "The remarkable relativistic vacuum: Bisognano-Wichmann modular flow and Reeh-Schlieder (Summers, arXiv:0802.1854). The vacuum modular flow is a one-parameter group of Lorentz boosts (modularBoost_group), each a proper unimodular det=1 transformation (modularBoost_lorentz), whose time-time component cosh(2 pi t) fixes the Unruh inverse temperature beta = 2 pi (modularBoost_energy). In the separating Reeh-Schlieder vacuum every nonzero local observable has nonzero expectation, so any local event has nonzero probability (reehSchlieder_event_occurs)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost",
    "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.thermoBogoliubov",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant.gnsForm"]
  forbids_substitutes ["the Tomita-Takesaki modular operator of a genuine type III factor and the Bisognano-Wichmann theorem's derivation from Wightman axioms, which are the cited AQFT infrastructure",
    "any claim that the full modular automorphism group of the field algebra is constructed; only the 2x2 boost realization and the separating-vacuum event property are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost_group,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost_lorentz,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.modularBoost_energy,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum.reehSchlieder_event_occurs]

/- ZIL-END -/
