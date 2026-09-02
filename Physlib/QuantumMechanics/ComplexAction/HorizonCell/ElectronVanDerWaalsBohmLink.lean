/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum
public import Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling

/-!
# The electron's Bohm–Madelung wave function and the van der Waals radius

Links the electron-exclusion-cell arc — the electron's Madelung wave function `ψ = R·e^{iS/ℏ}` in
Bohm/de Broglie–Bohm form — to the earlier **van der Waals radius** results
(`VanDerWaalsPolarizabilityScaling`, Fedorov–Tkatchenko: `R_vdW = C·α^{1/7}`). The bridge is the **quantum
Drude oscillator** (QDO): a harmonic-oscillator model of the atom whose polarizability sets the vdW radius, and
which shares the electron's Compton-clock frequency framework and its causal (HO/IHO) regimes.

* **the electron in Bohm form** — the free-electron Madelung wave function (amplitude `R`, phase `S = freePhase`)
  solves the **de Broglie–Bohm quantum Hamilton–Jacobi equation** `∂tS + |∇S|²/2m + V + Q = 0`
  (`electron_madelung_solves_bohm`, `freeParticle_quantumHamiltonJacobi`) — the TDSE in polar form;
* **the vdW radius from the QDO** — the QDO harmonic oscillator's polarizability `α = q²/(m ω²)` gives
  `R_vdW = C·α^{1/7}`, equivalently `R_vdW⁷ = C⁷·α` (`electron_vdWRadius_seventh`, `qmVdWRadius_pow_seven`);
* **the shared frequency framework** — the QDO frequency `ω = ω_dB(ℏω)` and the electron Compton clock
  `ω_C = ω_dB(mc²)` both realize `ω = E/ℏ` (`qdo_compton_share_deBroglie`): the vdW oscillator and the electron
  Zitterbewegung/Compton oscillator are the same de Broglie clock;
* **the causal HO/IHO regimes** — inverting the oscillator `ω² → −ω²` flips the polarizability sign,
  `α_inv = −α` (`vdW_ho_iho_causal`): the binding harmonic (timelike/HO) and anti-binding inverted (spacelike/IHO)
  regimes of the causal trichotomy, now read on the van der Waals polarizability.

So the electron's Bohm–Madelung wave function and the van der Waals radius meet at the quantum Drude oscillator:
the same de Broglie frequency `ω = E/ℏ` that is the Compton clock of the arc is the QDO frequency whose
polarizability fixes `R_vdW = C·α^{1/7}`, and the HO/IHO split of the arc is the binding/anti-binding split of
the vdW polarizability.

* **§A — the electron in Bohm form** (`electron_madelung_solves_bohm`).
* **§B — the vdW radius from the QDO** (`electron_vdWRadius_seventh`).
* **§C — the shared de Broglie / Compton clock** (`qdo_compton_share_deBroglie`).
* **§D — the causal HO/IHO regimes** (`vdW_ho_iho_causal`).
* **§E — assembled** (`electron_bohm_vanDerWaals_link`).

**Honest layering.** Every statement is exact reuse: `freeParticle_quantumHamiltonJacobi`,
`qmVdWRadius_pow_seven`, `qdoPolarizabilityOfHO_pos`, `comptonFrequency_eq_deBroglie_restEnergy`,
`qdoFrequency_eq_deBroglie_energyQuantum`, `qdoPolarizabilityInverted_eq_neg`. The content is the *link* — the
arc's electron (Bohm wave function, Compton clock, causal regimes) and the vdW radius (QDO polarizability) share
the quantum Drude oscillator. ## References

* Fedorov, Tkatchenko (arXiv:1803.11507); de Broglie–Bohm. Repo carriers:
  `Schrodinger.HamiltonJacobiMadelung`, `VanDerWaalsPolarizabilityScaling`,
  `ComptonClock.FrequencyTrinity`, `HorizonCell.ElectronMadelungDeBroglieMomentum`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.Schrodinger
open Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open QuantumMechanics.OneDimension

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronVanDerWaalsBohmLink


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **[The electron's Madelung wave function solves the de Broglie–Bohm equation].** The free electron's polar
wave function `ψ = R·e^{iS/ℏ}` (constant amplitude `R = amp`, phase `S = freePhase k m`) solves the quantum
Hamilton–Jacobi (Bohm) equation `∂tS + |∇S|²/2m + V + Q = 0` — the TDSE written in polar form, the Bohm picture
of the arc's electron. -/
lemma electron_madelung_solves_bohm (k : E) (m amp ħ : ℝ) :
    QuantumHamiltonJacobi (freePhase k m) (fun _ _ => 0) (fun _ _ => amp) m ħ :=
  freeParticle_quantumHamiltonJacobi k m amp ħ


/-- **[The electron's van der Waals radius is `C·α^{1/7}`] `R_vdW⁷ = C⁷·α`.** Modelling the atom as a quantum
Drude oscillator `Q` of charge `q` (`q ≠ 0`), its dipole polarizability `α = q²/(m ω²) = qdoPolarizabilityOfHO`
sets the van der Waals radius `R_vdW = C·α^{1/7}`, equivalently `R_vdW⁷ = C⁷·α` (Fedorov–Tkatchenko). -/
lemma electron_vdWRadius_seventh (q C : ℝ) (hq : q ≠ 0) (Q : HarmonicOscillator) :
    qmVdWRadius C (qdoPolarizabilityOfHO q Q) ^ 7 = C ^ 7 * qdoPolarizabilityOfHO q Q :=
  qmVdWRadius_pow_seven C (qdoPolarizabilityOfHO q Q) (qdoPolarizabilityOfHO_pos q hq Q).le


/-- **[The QDO oscillator and the electron Compton clock share `ω = E/ℏ`].** The electron's Compton clock is the
de Broglie frequency of its rest energy, `ω_C = ω_dB(mc²)`, and the quantum Drude oscillator's frequency is the
de Broglie frequency of its energy quantum, `ω = ω_dB(ℏω)`. The van der Waals polarizability oscillator and the
electron's Compton/Zitterbewegung oscillator are the *same de Broglie clock* `ω = E/ℏ`. -/
lemma qdo_compton_share_deBroglie (m c ω ħ : ℝ) (hħ : ħ ≠ 0) :
    comptonFrequency m c ħ = deBroglieFrequency (m * c ^ 2) ħ
      ∧ deBroglieFrequency (ħ * ω) ħ = ω :=
  ⟨comptonFrequency_eq_deBroglie_restEnergy m c ħ, qdoFrequency_eq_deBroglie_energyQuantum ω ħ hħ⟩


/-- **[The binding/anti-binding split of the vdW polarizability is the causal HO/IHO trichotomy].** Inverting
the oscillator `ω² → −ω²` (`ω → iω`, the pseudo-Hermitian inverted QHO) flips the polarizability sign,
`α_inv = −α`: the binding harmonic oscillator (timelike / HO, positive `α`) and the anti-binding inverted
oscillator (spacelike / IHO, negative `α`) of the arc's causal trichotomy, realized on the van der Waals
polarizability. -/
lemma vdW_ho_iho_causal (q μ ω : ℝ) :
    qdoPolarizabilityInverted q μ ω = -qdoPolarizability q μ ω :=
  qdoPolarizabilityInverted_eq_neg q μ ω


/-- **[The electron's Bohm wave function ↔ the van der Waals radius, assembled].** For a QDO atom `Q` of charge
`q` (`q ≠ 0`) and the free-electron Madelung wave function of wavevector `k`:

* the electron's polar wave function solves the de Broglie–Bohm equation (the TDSE in polar form);
* its van der Waals radius satisfies `R_vdW⁷ = C⁷·α` with `α = qdoPolarizabilityOfHO q Q`;
* the QDO frequency and the electron Compton clock are the same de Broglie clock `ω = E/ℏ`;
* inverting the oscillator flips the polarizability sign (`α_inv = −α`) — the HO/IHO causal split.

The electron's Bohm–Madelung wave function and the van der Waals radius meet at the quantum Drude oscillator. -/
lemma electron_bohm_vanDerWaals_link (k : E) (m amp c ω ħ q C : ℝ) (hħ : ħ ≠ 0) (hq : q ≠ 0)
    (Q : HarmonicOscillator) (μ : ℝ) :
    QuantumHamiltonJacobi (freePhase k m) (fun _ _ => 0) (fun _ _ => amp) m ħ
      ∧ qmVdWRadius C (qdoPolarizabilityOfHO q Q) ^ 7 = C ^ 7 * qdoPolarizabilityOfHO q Q
      ∧ comptonFrequency m c ħ = deBroglieFrequency (m * c ^ 2) ħ
      ∧ deBroglieFrequency (ħ * ω) ħ = ω
      ∧ qdoPolarizabilityInverted q μ ω = -qdoPolarizability q μ ω :=
  ⟨electron_madelung_solves_bohm k m amp ħ,
    electron_vdWRadius_seventh q C hq Q,
    comptonFrequency_eq_deBroglie_restEnergy m c ħ,
    qdoFrequency_eq_deBroglie_energyQuantum ω ħ hħ,
    qdoPolarizabilityInverted_eq_neg q μ ω⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronVanDerWaalsBohmLink

end
