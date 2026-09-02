/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.NagaoNielsenSchrodinger
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularFromState
public import Physlib.Relativity.Special.QIFUnruhFrameChange
meta import Zil

/-!
# The time-independent Schrödinger equation in the modular quantum inertial frame

This module welds the Nagao–Nielsen **Mazur–Ulam route** to the time-independent Schrödinger
equation (`FiniteTarget.NagaoNielsenSchrodinger`) onto the **quantum inertial frame** (QIF) and its
Tomita–Takesaki modular structure, and carries the weld into the curved-spacetime (Unruh) setting.

The QIF packages exactly the Nagao–Nielsen data — a Hermitian generator `H_R`, a positive
irreversible generator `H_I`, and the complex Hamiltonian `H_C = H_R − i·H_I` — and calls its
equilibrium condition `λ(ψ) = Re⟨H_I ψ, ψ⟩/ℏ = 0`. The QIF's own `tise_at_equilibrium` reduces
`H_C` to `H_R` through `complexHamiltonian_eq_H_R_of_isEquilibrium`; here we re-derive the same
conclusion through the **Mazur–Ulam operator-decomposition chain** `tise_via_mazur_ulam_chain`,
showing the two routes agree, and then specialize the generator to the Tomita–Takesaki modular
Hamiltonian `H_θ = −log ρ`.

* `qif_tise_via_mazur_ulam` — for any QIF, an equilibrium `H_R`-eigenstate satisfies the TISE for
  the complex Hamiltonian, derived through the Mazur–Ulam chain. This is the QIF instance of the
  Nagao–Nielsen TISE.
* `modularState_tise_via_mazur_ulam` — for the KMS QIF built from a state's modular Hamiltonian
  `H_θ = −log ρ`, every modular eigenstate satisfies the TISE. This places the TISE on the
  Tomita–Takesaki generator — the Rindler/Unruh boost of QFT on the finite algebra `B(H_d)`.
* `frozen_properTime_modular_reversible` — at frozen entropic proper time `ρ = ρ` the modular
  complex Hamiltonian collapses (`H_I = 0`) to the reversible modular flow: the equilibrium/vacuum
  frame is where entropic time freezes into unitary modular time.
* `unruh_tise_observer_dependence` — the curved-spacetime content: under an Unruh frame change the
  **inertial** observer's `H_R`-eigenstate satisfies the TISE (equilibrium/vacuum), while the
  **accelerated** observer is not at equilibrium (`λ_U > 0`), so the TISE's equilibrium premise
  fails for them. The time-independent Schrödinger equation is thus observer-dependent exactly where
  the Unruh effect is.

**Honest layering.** Nothing new is assumed: every result routes through the proven Nagao–Nielsen
chain, the QIF equilibrium API, the constructive modular Hamiltonian, and the Unruh frame-change
carrier. The novel content is the identification — the Mazur–Ulam TISE *is* the QIF/modular TISE,
and the Unruh disagreement *is* the observer-dependence of that equation.
-/

set_option autoImplicit false

open QuantumMechanics.FiniteTarget QuantumInfo.Finite

@[expose] public section

namespace Physlib.Relativity.Special.ModularSchrodingerInertialFrame

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- **The QIF time-independent Schrödinger equation via the Mazur–Ulam chain.** For any quantum
inertial frame `Q`, an equilibrium state `ψ` (`λ(ψ) = 0`) that is an `H_R`-eigenvector satisfies the
TISE for the full complex Hamiltonian `H_C = H_R − i·H_I`:

  `Q.complexHamiltonian ψ = E • ψ`.

Derived through Nagao–Nielsen's `tise_via_mazur_ulam_chain` (positive `H_I`, kernel membership
`H_I ψ = 0` from equilibrium, `H_R`-eigenstate), showing the Mazur–Ulam operator decomposition
reproduces the QIF's `tise_at_equilibrium`. -/
theorem qif_tise_via_mazur_ulam
    (Q : QuantumInertialFrame H) {ψ : H} (h_eq : Q.IsEquilibriumAt ψ)
    {E : ℂ} (h_eig : Q.H_R ψ = E • ψ) :
    Q.complexHamiltonian ψ = E • ψ := by
  have hI_zero : Q.H_I ψ = 0 := Q.H_I_apply_eq_zero_of_isEquilibrium h_eq
  exact tise_via_mazur_ulam_chain Q.H_R Q.H_I ψ E Q.H_I_isPositive hI_zero h_eig

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **The TISE on the Tomita–Takesaki modular Hamiltonian.** For the KMS quantum inertial frame
`kmsQIF_ofState ρ` — whose Hermitian generator is the modular Hamiltonian `H_θ = −log ρ` lifted to
`EuclideanSpace ℂ d` and whose dissipator vanishes (reversible modular flow) — every modular
eigenstate `H_θ ψ = E_θ • ψ` satisfies the TISE, derived through the Mazur–Ulam chain
(`qif_tise_via_mazur_ulam`). This is the time-independent Schrödinger equation of QFT on the finite
algebra `B(H_d)`, stated on the modular/Rindler generator. -/
theorem modularState_tise_via_mazur_ulam
    (ρ : MState d) (hbar : ℝ) (hbar_pos : 0 < hbar) (beta : ℝ) (beta_pos : 0 < beta)
    {ψ : EuclideanSpace ℂ d} {E_θ : ℂ}
    (h_eig : modularHamiltonianClm ρ ψ = E_θ • ψ) :
    (kmsQIF_ofState ρ hbar hbar_pos beta beta_pos).complexHamiltonian ψ = E_θ • ψ := by
  refine qif_tise_via_mazur_ulam (kmsQIF_ofState ρ hbar hbar_pos beta beta_pos) ?_ h_eig
  exact kmsQIF_ofState_isEquilibriumAt ρ hbar hbar_pos beta beta_pos ψ

/-- **Frozen entropic proper time freezes the modular flow into unitary evolution.** At the
coincident state pair `ρ = ρ` the entropic proper time vanishes, and the complex Hamiltonian built
on the modular Hamiltonian `H_θ = −log ρ` with zero dissipator collapses to `H_θ` itself: the
equilibrium/vacuum frame is exactly where the irreversible entropic clock freezes and the evolution
is the reversible Tomita–Takesaki modular flow. -/
theorem frozen_properTime_modular_reversible (ρ : MState d) :
    (entropicProperTime ρ ρ).toReal = 0
    ∧ complexHamiltonian (modularHamiltonianClm ρ) 0 = modularHamiltonianClm ρ :=
  entropic_proper_time_self_implies_unitary (modularHamiltonianClm ρ) ρ

open Physlib.Relativity.Special.QuantumInertialFrameLorentzian in
/-- **The Unruh observer-dependence of the time-independent Schrödinger equation.** Under an Unruh
frame change between an inertial and an accelerated Lorentzian QIF worldline, the **inertial**
observer's state — at equilibrium (`λ = 0`, the vacuum) — satisfies the TISE for the complex
Hamiltonian whenever it is an `H_R`-eigenstate, while the **accelerated** observer is *not* at
equilibrium (`λ_U = a/(2πc) > 0`), so the equilibrium premise of the TISE fails for them. The
time-independent Schrödinger equation holds in the inertial/vacuum frame and is broken by Unruh
acceleration — the curved-spacetime, observer-dependent face of the equilibrium TISE. -/
theorem unruh_tise_observer_dependence {sd : ℕ}
    {LQW_inertial LQW_accelerated : LorentzianQIFWorldline H sd}
    {M : UnruhEntropicRate}
    (U : UnruhFrameChange LQW_inertial LQW_accelerated M) (t : ℝ)
    {E : ℂ} (h_eig : LQW_inertial.Q.H_R (LQW_inertial.state t) = E • LQW_inertial.state t) :
    LQW_inertial.Q.complexHamiltonian (LQW_inertial.state t) = E • LQW_inertial.state t
    ∧ ¬ LQW_accelerated.IsEquilibriumAt t := by
  obtain ⟨h_in, h_acc⟩ := U.inertial_isEquilibriumAt_accelerated_not t
  exact ⟨qif_tise_via_mazur_ulam LQW_inertial.Q h_in h_eig, h_acc⟩

end Physlib.Relativity.Special.ModularSchrodingerInertialFrame

end

/- ZIL-BEGIN -/

zil attach Physlib.Relativity.Special.ModularSchrodingerInertialFrame.qif_tise_via_mazur_ulam where
  formalizes @ "claim:the-quantum-inertial-frame-time-independent-schrodinger-equation-is-derived-through-the-mazur-ulam-operator-decomposition-chain",
  requires @ "claim:the-mazur-ulam-operator-decomposition-with-a-positive-irreversible-generator-annihilating-the-state-and-an-hR-eigenstate-yields-the-time-independent-schrodinger-equation",
  supported_by @ "paper:garcia-2026-mazur-ulam-operator-decomposition"

zil attach Physlib.Relativity.Special.ModularSchrodingerInertialFrame.modularState_tise_via_mazur_ulam where
  supported_by @ "lean:Physlib.Relativity.Special.ModularSchrodingerInertialFrame.qif_tise_via_mazur_ulam",
  formalizes @ "claim:every-modular-eigenstate-of-the-tomita-takesaki-modular-hamiltonian-minus-log-rho-satisfies-the-time-independent-schrodinger-equation",
  requires @ "claim:the-quantum-inertial-frame-time-independent-schrodinger-equation-is-derived-through-the-mazur-ulam-operator-decomposition-chain"

zil attach Physlib.Relativity.Special.ModularSchrodingerInertialFrame.frozen_properTime_modular_reversible where
  supported_by @ "lean:QuantumMechanics.FiniteTarget.entropic_proper_time_self_implies_unitary",
  formalizes @ "claim:frozen-entropic-proper-time-freezes-the-modular-complex-hamiltonian-into-the-reversible-tomita-takesaki-flow"

zil attach Physlib.Relativity.Special.ModularSchrodingerInertialFrame.unruh_tise_observer_dependence where
  supported_by @ "lean:Physlib.Relativity.Special.ModularSchrodingerInertialFrame.qif_tise_via_mazur_ulam",
  formalizes @ "claim:the-time-independent-schrodinger-equation-holds-for-the-inertial-vacuum-observer-but-its-equilibrium-premise-fails-for-the-unruh-accelerated-observer",
  requires @ "claim:the-quantum-inertial-frame-time-independent-schrodinger-equation-is-derived-through-the-mazur-ulam-operator-decomposition-chain",
  caveat @ "claim:the-accelerated-observer-being-out-of-equilibrium-is-the-unruh-thermal-rate-not-a-failure-of-the-schrodinger-equation-itself"

zil_file_contract physlib.modularSchrodingerInertialFrame where
  promises "The time-independent Schrodinger equation in the modular quantum inertial frame: the Nagao-Nielsen Mazur-Ulam operator-decomposition chain reproduces the QIF equilibrium TISE for the complex Hamiltonian H_C = H_R - i H_I; specialized to the Tomita-Takesaki modular Hamiltonian H_theta = -log rho it gives the TISE on every modular eigenstate (QFT on the finite algebra B(H_d)); frozen entropic proper time collapses the modular complex Hamiltonian to the reversible modular flow; and under an Unruh frame change the TISE holds for the inertial vacuum observer but its equilibrium premise fails for the accelerated observer -- the observer-dependent, curved-spacetime face of the equation."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:QuantumMechanics.FiniteTarget.tise_via_mazur_ulam_chain",
    "lean:QuantumMechanics.FiniteTarget.QuantumInertialFrame.complexHamiltonian",
    "lean:QuantumMechanics.FiniteTarget.modularHamiltonianClm"]
  forbids_substitutes ["any operator-level type III modular theory, the modular Hamiltonian here is the finite-dimensional minus-log-rho on B(H_d)",
    "any claim that the accelerated observer's Schrodinger equation is inconsistent, only its equilibrium premise fails, encoding the Unruh thermal rate"]
  witnessed_by [Physlib.Relativity.Special.ModularSchrodingerInertialFrame.qif_tise_via_mazur_ulam,
    Physlib.Relativity.Special.ModularSchrodingerInertialFrame.modularState_tise_via_mazur_ulam,
    Physlib.Relativity.Special.ModularSchrodingerInertialFrame.frozen_properTime_modular_reversible,
    Physlib.Relativity.Special.ModularSchrodingerInertialFrame.unruh_tise_observer_dependence]

/- ZIL-END -/
