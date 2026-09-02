/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding

/-!
# Conservation laws: electric charge, baryon number, lepton number

The zoo is organized by its conserved **additive quantum numbers**. Each particle carries a triple `(Q, B, L)`
— electric charge, baryon number, lepton number — that adds across a multiparticle state (`QuantumNumbers`,
an additive structure). A physical process conserves all three exactly when the incoming and outgoing triples
are *equal* — a single equation in the charge-vector group.

Baryon number is `1/3` per quark (a baryon `qqq` has `B = 1`); lepton number is `+1` per lepton. The canonical
test is **β decay** `n → p + e⁻ + ν̄ₑ`:

  `(Q,B,L):  (0,1,0) = (1,1,0) + (−1,0,1) + (0,0,−1)`,

which holds componentwise — charge, baryon number, and lepton number are simultaneously conserved.

* **§A — the additive quantum numbers.** `QuantumNumbers` with `+`; field-projection simp lemmas.
* **§B — the particles.** `neutron`, `proton`, `electron`, `antiNeutrino`, the pion triplet
  `piPlus`, `piZero`, `piMinus`, `antiMuon`, `muonNeutrino`.
* **§C — conservation in processes.** `beta_decay_conserves` (`n → p e⁻ ν̄`), `pion_decay_conserves`
  (`π⁺ → μ⁺ νμ`), and `proton_baryon_from_quarks` (the proton's `B = 1` is its three quarks' `1/3` each).

**Honest layering.** Proven: `(Q,B,L)` are additive and the listed decays conserve all three. The quantum-number
*assignments* are the empirical particle data; this formalizes the bookkeeping (the conservation laws), not the
decay dynamics (matrix elements / rates).

## References

* Conservation of electric charge, baryon number, lepton number; β decay `n → p e⁻ ν̄`. `Physlib`
  (`Winding.QuarkChargeWinding`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation


/-- **The additive quantum numbers** of a particle (or multiparticle state): electric charge, baryon number,
lepton number. -/
@[ext]
structure QuantumNumbers where
  /-- Electric charge. -/
  electric : ℚ
  /-- Baryon number. -/
  baryon : ℚ
  /-- Lepton number. -/
  lepton : ℚ

/-- Quantum numbers add componentwise across a multiparticle state. -/
instance : Add QuantumNumbers where
  add a b := ⟨a.electric + b.electric, a.baryon + b.baryon, a.lepton + b.lepton⟩

@[simp] lemma add_electric (a b : QuantumNumbers) : (a + b).electric = a.electric + b.electric := rfl
@[simp] lemma add_baryon (a b : QuantumNumbers) : (a + b).baryon = a.baryon + b.baryon := rfl
@[simp] lemma add_lepton (a b : QuantumNumbers) : (a + b).lepton = a.lepton + b.lepton := rfl


/-- Neutron `(0, 1, 0)` — a baryon. -/
def neutron : QuantumNumbers := ⟨0, 1, 0⟩
/-- Proton `(1, 1, 0)` — a baryon. -/
def proton : QuantumNumbers := ⟨1, 1, 0⟩
/-- Electron `(−1, 0, 1)` — a lepton. -/
def electron : QuantumNumbers := ⟨-1, 0, 1⟩
/-- Electron antineutrino `(0, 0, −1)` — an antilepton. -/
def antiNeutrino : QuantumNumbers := ⟨0, 0, -1⟩
/-- π⁺ meson `(1, 0, 0)`. -/
def piPlus : QuantumNumbers := ⟨1, 0, 0⟩
/-- π⁰ meson `(0, 0, 0)`. -/
def piZero : QuantumNumbers := ⟨0, 0, 0⟩
/-- π⁻ meson `(-1, 0, 0)`. -/
def piMinus : QuantumNumbers := ⟨-1, 0, 0⟩
/-- Antimuon `μ⁺` `(1, 0, −1)` — an antilepton. -/
def antiMuon : QuantumNumbers := ⟨1, 0, -1⟩
/-- Muon neutrino `(0, 0, 1)` — a lepton. -/
def muonNeutrino : QuantumNumbers := ⟨0, 0, 1⟩


/-- **[β decay conserves `(Q, B, L)`]** `n → p + e⁻ + ν̄ₑ` conserves electric charge, baryon number, and
lepton number simultaneously — a single equality of charge vectors. -/
lemma beta_decay_conserves : neutron = proton + electron + antiNeutrino := by
  ext <;> simp [neutron, proton, electron, antiNeutrino]

/-- **[π⁺ decay conserves `(Q, B, L)`]** `π⁺ → μ⁺ + νμ` conserves all three additive quantum numbers
(lepton number: `0 = −1 + 1`). -/
lemma pion_decay_conserves : piPlus = antiMuon + muonNeutrino := by
  ext <;> simp [piPlus, antiMuon, muonNeutrino]

/-- **[The pion charge triplet]** `π⁺, π⁰, π⁻` have charges `+1,0,-1` and no baryon
or lepton number. -/
lemma pion_triplet_quantum_numbers :
    piPlus.electric = 1 ∧ piZero.electric = 0 ∧ piMinus.electric = -1
      ∧ piPlus.baryon = 0 ∧ piZero.baryon = 0 ∧ piMinus.baryon = 0
      ∧ piPlus.lepton = 0 ∧ piZero.lepton = 0 ∧ piMinus.lepton = 0 := by
  norm_num [piPlus, piZero, piMinus]

/-- **[π⁺ and π⁻ have neutral total quantum numbers]** the charged pion pair
has the same additive `(Q,B,L)` vector as `π⁰`. -/
lemma pion_charged_pair_quantum_numbers_neutral : piPlus + piMinus = piZero := by
  ext <;> simp [piPlus, piMinus, piZero]

/-- **[The proton's baryon number is its quark content]** `B(p) = 1/3 + 1/3 + 1/3 = 1` — three quarks, each
`B = 1/3`, make a unit-baryon-number proton. -/
lemma proton_baryon_from_quarks : (1 : ℚ) / 3 + 1 / 3 + 1 / 3 = proton.baryon := by
  simp [proton]; norm_num

end Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation

end
