/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.ExperimentalParticleReactions
meta import Zil

/-!
# The full Michel decay `μ⁻ → e⁻ ν̄ₑ ν_μ` with explicit lepton-flavor bookkeeping

The dominant (Michel) muon decay is the three-body process `μ⁻ → e⁻ + ν̄ₑ + ν_μ`. This file makes the
**lepton-family bookkeeping explicit** — each of `Lₑ, L_μ, L_τ` separately balanced across the three-body
final state — and proves the deep content that *fixes which neutrinos appear*: the family numbers force the
final state to contain an **electron antineutrino** `ν̄ₑ` and a **muon neutrino** `ν_μ`, not any other flavour
combination.

* **§A — explicit per-family balance.** `michel_eNum` (`Lₑ : 0 = 1 + (−1) + 0` — the `e⁻` and `ν̄ₑ` cancel),
  `michel_muNum` (`L_μ : 1 = 0 + 0 + 1` — the `ν_μ` carries the muon number), `michel_tauNum`
  (`L_τ : 0 = 0`), and `michel_total` (total `L = 1`).
* **§B — the flavours are forced.** `michel_eAntiNeutrino_forced`: in `μ⁻ → e⁻ + X + ν_μ`, electron-number
  conservation forces `X.eNum = −1`, i.e. `X` is the electron *anti*neutrino (a neutrino `ν_e`, with
  `eNum = +1`, would give `Lₑ = 2`). `michel_muNeutrino_forced`: muon-number conservation forces the third
  body's `muNum = 1`, i.e. the muon neutrino.
* **§C — charge / baryon / total lepton.** `michel_QBL` re-exports the `(Q,B,L)` balance
  (`Particles.ExperimentalParticleReactions.muon_decay_conserves`).
* **§D — main result** `michel_decay_complete`: the flavour structure equation together with all three explicit
  family-number balances.

**Honest layering.** Proven: each lepton family number balances across the three-body final state, and family
conservation uniquely determines the two final neutrino flavours (`ν̄ₑ`, `ν_μ`). Massless-neutrino family
bookkeeping (oscillations, which violate individual `L_ℓ`, are not modelled). The Michel energy spectrum /
decay rate is dynamics, not formalized here.

## References

* Michel decay `μ⁻ → e⁻ ν̄ₑ ν_μ`; lepton family number conservation. `Physlib` (`Particles.LeptonFlavorNumbers`,
  `Particles.ExperimentalParticleReactions`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor


/-- **[Electron number balance]** `Lₑ : 0 = 1 + (−1) + 0` — the muon carries no electron number; in the final
state the `e⁻` (`+1`) and the `ν̄ₑ` (`−1`) cancel, the `ν_μ` contributes `0`. This is *why* the electron-side
neutrino is the antineutrino. -/
lemma michel_eNum : muon.eNum = electron.eNum + antiENeutrino.eNum + muNeutrino.eNum := by
  simp [muon, electron, antiENeutrino, muNeutrino]

/-- **[Muon number balance]** `L_μ : 1 = 0 + 0 + 1` — the muon's family number is carried off by the muon
neutrino `ν_μ`. -/
lemma michel_muNum : muon.muNum = electron.muNum + antiENeutrino.muNum + muNeutrino.muNum := by
  simp [muon, electron, antiENeutrino, muNeutrino]

/-- **[Tau number balance]** `L_τ : 0 = 0` — no tau-flavour leptons are involved. -/
lemma michel_tauNum : muon.tauNum = electron.tauNum + antiENeutrino.tauNum + muNeutrino.tauNum := by
  simp [muon, electron, antiENeutrino, muNeutrino]

/-- **[Total lepton number]** `L = 1` on both sides — a consequence of the three family balances. -/
lemma michel_total : total muon = total (electron + antiENeutrino + muNeutrino) := by
  rw [muonDecay_conserves_flavor]


/-- **[The electron-side neutrino must be `ν̄ₑ`]** in `μ⁻ → e⁻ + X + ν_μ`, electron-number conservation forces
`X.eNum = −1` — `X` is the electron *anti*neutrino. (An electron *neutrino*, `eNum = +1`, would give
`Lₑ = 2`, which is not observed.) -/
lemma michel_eAntiNeutrino_forced (X : LeptonFlavor)
    (h : muon = electron + X + muNeutrino) : X.eNum = -1 := by
  have he := congrArg (·.eNum) h
  simp [muon, electron, muNeutrino] at he
  omega

/-- **[The third body must be the muon neutrino]** in `μ⁻ → e⁻ + ν̄ₑ + Y`, muon-number conservation forces
`Y.muNum = 1` — `Y` carries the muon family number, i.e. `Y = ν_μ`. -/
lemma michel_muNeutrino_forced (Y : LeptonFlavor)
    (h : muon = electron + antiENeutrino + Y) : Y.muNum = 1 := by
  have hm := congrArg (·.muNum) h
  simp [muon, electron, antiENeutrino] at hm
  omega


/-- **[Charge / baryon / lepton balance]** `μ⁻ → e⁻ ν̄ₑ ν_μ` conserves `(Q,B,L)`
(`Particles.ExperimentalParticleReactions.muon_decay_conserves`). -/
lemma michel_QBL :
    Particles.ExperimentalParticleReactions.muon
      = Particles.BaryonLeptonNumberConservation.electron + Particles.BaryonLeptonNumberConservation.antiNeutrino
        + Particles.BaryonLeptonNumberConservation.muonNeutrino :=
  Particles.ExperimentalParticleReactions.muon_decay_conserves


/-- **[The full Michel decay]** `μ⁻ → e⁻ ν̄ₑ ν_μ`: the lepton-flavour structure equation together with each
explicit family-number balance — `Lₑ` (the `e⁻`/`ν̄ₑ` cancellation), `L_μ` (carried by `ν_μ`), and `L_τ` — all
separately conserved across the three-body final state. -/
lemma michel_decay_complete :
    muon = electron + antiENeutrino + muNeutrino
      ∧ muon.eNum = electron.eNum + antiENeutrino.eNum + muNeutrino.eNum
      ∧ muon.muNum = electron.muNum + antiENeutrino.muNum + muNeutrino.muNum
      ∧ muon.tauNum = electron.tauNum + antiENeutrino.tauNum + muNeutrino.tauNum :=
  ⟨muonDecay_conserves_flavor, michel_eNum, michel_muNum, michel_tauNum⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_QBL where
  formalizes @ "claim:muon-decay-mu-to-e-electron-antineutrino-muon-neutrino-conserves-electric-charge-baryon-number-and-total-lepton-number",
  supported_by @ "paper:michel-1950-muon-decay-spectrum"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_eAntiNeutrino_forced where
  formalizes @ "claim:electron-flavor-conservation-forces-the-muon-decay-to-emit-an-electron-antineutrino-not-any-other-electron-flavor-state",
  requires @ "claim:muon-decay-mu-to-e-electron-antineutrino-muon-neutrino-conserves-electric-charge-baryon-number-and-total-lepton-number"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_muNeutrino_forced where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.ExperimentalParticleReactions.muon_decay_conserves",
  formalizes @ "claim:muon-flavor-conservation-forces-the-muon-decay-to-emit-a-muon-neutrino",
  requires @ "claim:muon-decay-mu-to-e-electron-antineutrino-muon-neutrino-conserves-electric-charge-baryon-number-and-total-lepton-number"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_decay_complete where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muonDecay_conserves_flavor",
  formalizes @ "claim:the-muon-decay-mode-mu-to-e-electron-antineutrino-muon-neutrino-is-the-unique-flavor-conserving-two-neutrino-mode",
  requires @ "claim:electron-flavor-conservation-forces-the-muon-decay-to-emit-an-electron-antineutrino-not-any-other-electron-flavor-state"

zil_file_contract physlib.michelDecayFlavor where
  promises "Lepton-flavor structure of muon decay: the mode mu to electron plus electron-antineutrino plus muon-neutrino conserves the total additive lepton-flavor numbers; electron-flavor conservation forces the emitted electron-flavor neutrino to be an antineutrino, and muon-flavor conservation forces a muon neutrino, so this two-neutrino mode is the unique flavor-conserving one; and the mode conserves electric charge, baryon and lepton number."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muon",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.electron"]
  forbids_substitutes ["a computation of the Michel spectrum or decay rate, only the flavor bookkeeping is carried",
    "a dynamical derivation of lepton-flavor conservation, taken as the additive selection rule"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_eAntiNeutrino_forced,
    Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_muNeutrino_forced,
    Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_QBL,
    Physlib.QuantumMechanics.ComplexAction.Particles.MichelDecayFlavor.michel_decay_complete]

/- ZIL-END -/
