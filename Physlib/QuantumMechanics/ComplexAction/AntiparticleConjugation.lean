/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation

/-!
# Antiparticles: charge conjugation on the additive quantum numbers

Every particle has an **antiparticle** with all additive quantum numbers reversed. On the `(Q, B, L)` charge
vectors (`Particles.BaryonLeptonNumberConservation.QuantumNumbers`), charge conjugation `C` is the negation
`conjugate (Q,B,L) = (−Q,−B,−L)`. This completes the zoo with the antimatter sector and the
particle–antiparticle structure.

* **§A — charge conjugation.** `conjugate`; `conjugate_involutive` (`C² = 1`); `pair_annihilates`
  (`particle + antiparticle = vacuum`, all quantum numbers cancel); `selfConjugate_iff_neutral` (a particle is
  its own antiparticle iff `Q = B = L = 0`).
* **§B — named antiparticles.** `positron = C(electron)` with `(Q,B,L) = (1,0,−1)`;
  `electron_positron_annihilate`, `proton_antiproton_annihilate`; `photon_selfConjugate` (the photon is its own
  antiparticle).

**Honest layering.** Proven: `C` is an involution that sends a particle to the vacuum-summing antiparticle, and
the self-conjugate particles are exactly the `(0,0,0)` neutrals (photon, `Z`, Higgs, graviton). This is the
quantum-number bookkeeping of antimatter; the `C`-eigenvalue phases of field operators are the AQFT content
(`PTSymmetricQFT.ChargeConjugation`, `Hopf.ChargeConjugationRibbonTwist.antipode`), not re-derived here.

## References

* Charge conjugation; particle–antiparticle annihilation. `Physlib` (`Particles.BaryonLeptonNumberConservation`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation


/-- **Charge conjugation** `C` — the antiparticle has all additive quantum numbers reversed. -/
def conjugate (q : QuantumNumbers) : QuantumNumbers := ⟨-q.electric, -q.baryon, -q.lepton⟩

@[simp] lemma conjugate_electric (q : QuantumNumbers) : (conjugate q).electric = -q.electric := rfl
@[simp] lemma conjugate_baryon (q : QuantumNumbers) : (conjugate q).baryon = -q.baryon := rfl
@[simp] lemma conjugate_lepton (q : QuantumNumbers) : (conjugate q).lepton = -q.lepton := rfl

/-- **[`C` is an involution]** `C(C q) = q` — conjugating twice returns the particle. -/
lemma conjugate_involutive (q : QuantumNumbers) : conjugate (conjugate q) = q := by
  ext <;> simp

/-- **[Particle + antiparticle = vacuum]** `q + C q = (0,0,0)` — every additive quantum number cancels, so a
particle and its antiparticle can annihilate to (quantum-number-free) radiation. -/
lemma pair_annihilates (q : QuantumNumbers) : q + conjugate q = ⟨0, 0, 0⟩ := by
  ext <;> simp

/-- **[Self-conjugate ⟺ neutral]** a particle is its own antiparticle exactly when all its additive quantum
numbers vanish — the truly neutral particles (photon, `Z`, Higgs, graviton). -/
lemma selfConjugate_iff_neutral (q : QuantumNumbers) :
    conjugate q = q ↔ q.electric = 0 ∧ q.baryon = 0 ∧ q.lepton = 0 := by
  constructor
  · intro h
    have he := congrArg QuantumNumbers.electric h
    have hb := congrArg QuantumNumbers.baryon h
    have hl := congrArg QuantumNumbers.lepton h
    simp only [conjugate_electric, conjugate_baryon, conjugate_lepton] at he hb hl
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨he, hb, hl⟩
    ext <;> simp [he, hb, hl]


/-- The **positron** `e⁺ = C(e⁻)`. -/
def positron : QuantumNumbers := conjugate electron

/-- **[Positron quantum numbers]** `e⁺ = (1, 0, −1)`: charge `+1`, antilepton (`L = −1`). -/
lemma positron_quantumNumbers : positron = ⟨1, 0, -1⟩ := by
  ext <;> simp [positron, electron]

/-- **[Electron–positron annihilation]** `e⁻ + e⁺ = vacuum` (`→ γγ`). -/
lemma electron_positron_annihilate : electron + positron = ⟨0, 0, 0⟩ :=
  pair_annihilates electron

/-- **[Proton–antiproton annihilation]** `p + p̄ = vacuum` (baryon number `1 + (−1) = 0`). -/
lemma proton_antiproton_annihilate : proton + conjugate proton = ⟨0, 0, 0⟩ :=
  pair_annihilates proton

/-- The **photon** `(0, 0, 0)` — carries no additive quantum numbers. -/
def photon : QuantumNumbers := ⟨0, 0, 0⟩

/-- **[The photon is its own antiparticle]** `C(γ) = γ` — a self-conjugate neutral. -/
lemma photon_selfConjugate : conjugate photon = photon := by
  ext <;> simp [photon]

end Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

end
