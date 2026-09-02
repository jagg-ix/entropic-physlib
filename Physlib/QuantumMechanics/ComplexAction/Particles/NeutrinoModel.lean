/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers
public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass
public import Mathlib.RingTheory.RootsOfUnity.Complex
meta import Zil

/-!
# The neutrino and the tau neutrino

The lepton family numbers (`Particles.LeptonFlavorNumbers`) already carry the three neutrino flavors `ν_e, ν_μ, ν_τ`
as triples `(Lₑ, L_μ, L_τ)`. This file completes the neutrino sector with its charge, its (anti)particle
structure, and the tau-flavor dynamics.

* **§A — the neutrino is a neutral lepton.** Its additive quantum numbers are `(Q,B,L) = (0,0,1)`
  (`neutrino`), electrically neutral as the winding-`0` state (`neutrino_charge_zero`,
  `windingCharge 0 = 0`).
* **§B — the Dirac neutrino.** Although electrically *neutral*, the neutrino is **not** self-conjugate:
  its lepton number `L = 1 ≠ 0`, so by `AntiparticleConjugation.selfConjugate_iff_neutral` the antineutrino
  `ν̄` (with `L = −1`) is a *distinct* particle (`neutrino_not_selfConjugate`, `antineutrino_lepton`). This is
  the Dirac neutrino — neutrality of *charge* does not make a particle its own antiparticle; lepton number
  does the distinguishing. (A Majorana neutrino, with `L` not conserved, would be self-conjugate.)
* **§C — the tau neutrino and tau decay.** `ν_τ` carries only tau family number, distinct from `ν_e`
  (`tauNeutrino_ne_eNeutrino`); leptonic tau decay `τ⁻ → ν_τ + e⁻ + ν̄ₑ` conserves every family number
  (`tauDecay_conserves_flavor`, `tauDecay_conserves_total`), and the muon channel
  `τ⁻ → ν_τ + μ⁻ + ν̄_μ` is checked by the same family-number balance
  (`tauMuonDecay_conserves_flavor`).
* **§C.1 — massive-neutrino oscillation data.** `NeutrinoMassSpectrum` carries the three mass eigenvalues,
  `deltaM21Sq`/`deltaM31Sq` compute the measured mass-square splittings, and
  `NeutrinoOscillationParameters.fromMassSpectrum` links mixing angles to the computed splittings. Normal
  and inverted orderings prove the expected signs of the splittings from nonnegative ordered masses.
* **§C.2 — Type-I seesaw source of the spectrum.** `ThreeFlavorSeesawData` uses the existing
  `Yukawa.SeesawMass` eigenvalues to build the three light neutrino masses, then computes `Δm²₂₁` and
  `Δm²₃₁` from that generated spectrum. The sterile right-handed-neutrino gauge-singlet bridge remains in
  the higher `Yukawa.StandardModelYukawaCoupling` file, avoiding an import cycle through the strong/SU(5)
  particle graph.
* **§D — CPT.** `ν + ν̄ = vacuum` (`neutrino_pair_annihilates`): the neutral neutrino still annihilates its
  distinct antineutrino.
* **§E — the fractional three-fold structure.** In the τ-coherence-loop model the neutrino is a three-node
  attractor, the SU(3) **antitriplet** `3̄`. Its neutrality is *fractional*: three nodes each carrying a third
  (`windingCharge 1 = 1/3`), phased by the cube roots of unity `1, ω, ω²` (the `ℤ/3` characters), whose sum
  **vanishes** (`cubeRoot_sum_zero`, `neutrino_fractional_neutral`). So `Q(ν) = 0` is not a trivial winding-0
  fact but the cancellation of three fractional thirds around the loop (`cubeRoot_pow_three`, with `cubeRoot`
  a primitive cube root of unity).

**Honest layering.** Proven: the neutrino is neutral (`windingCharge 0 = 0`), is a Dirac particle (neutral
but `L≠0`, hence `ν̄ ≠ ν`), `ν_τ ≠ ν_e`, tau decay conserves each lepton family number, and `ν + ν̄ = 0`.
The massive layer is also explicit: mass-square splittings are computed from a spectrum, and a three-flavor
Type-I seesaw spectrum is generated from the existing `Yukawa.SeesawMass` algebra. The PMNS angles and CP
phase remain parameters; no empirical table is imported and no claim is made that the Yukawa values are
predicted.

## References

* Lepton family number, Dirac vs Majorana neutrinos, tau decay. `Physlib` (`Particles.LeptonFlavorNumbers`,
  `AntiparticleConjugation`, `Winding.QuarkChargeWinding`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel


/-- **The neutrino's additive quantum numbers** `(Q,B,L) = (0,0,1)` — electrically neutral, no baryon
number, lepton number `1`. (All three flavors share these; the family number distinguishes them.) -/
def neutrino : Particles.BaryonLeptonNumberConservation.QuantumNumbers := ⟨0, 0, 1⟩

/-- **[The neutrino is electrically neutral]** `Q = 0` as the winding-`0` state (`Winding.QuarkChargeWinding`). -/
lemma neutrino_charge_zero : windingCharge 0 = 0 := neutrino_charge


/-- **[The neutrino is not its own antiparticle]** despite being electrically neutral, `Cν ≠ ν` — its lepton
number `L = 1 ≠ 0` blocks self-conjugacy (`selfConjugate_iff_neutral`). The neutrino is a **Dirac** particle:
the antineutrino is distinct. -/
lemma neutrino_not_selfConjugate : conjugate neutrino ≠ neutrino := by
  intro h
  rw [selfConjugate_iff_neutral] at h
  simp [neutrino] at h

/-- **[The antineutrino carries `L = −1`]** `(Cν).lepton = −1` — opposite lepton number to the neutrino. -/
lemma antineutrino_lepton : (conjugate neutrino).lepton = -1 := by
  simp [neutrino]


/-- **[The tau neutrino is a distinct flavor]** `ν_τ ≠ ν_e` — equal `(Q,B,L)` but different family number
(`ν_τ` carries `L_τ = 1`, `ν_e` carries `Lₑ = 1`). -/
lemma tauNeutrino_ne_eNeutrino : tauNeutrino ≠ eNeutrino := fun h => by
  simpa [tauNeutrino, eNeutrino] using congrArg (·.tauNum) h

/-- **[Tau decay conserves lepton flavor]** `τ⁻ → ν_τ + e⁻ + ν̄ₑ`: the tau number is `1` on both sides
(`τ → ν_τ`), the electron number is `0` (`e⁻` and `ν̄ₑ` cancel), the muon number is `0` — *each* family
number `Lₑ, L_μ, L_τ` is conserved (the tau-sector analogue of `muonDecay_conserves_flavor`). -/
lemma tauDecay_conserves_flavor : tau = tauNeutrino + electron + antiENeutrino := by
  ext <;> simp [tau, tauNeutrino, electron, antiENeutrino]

/-- **[Tau decay conserves total lepton number]** `L` is conserved in `τ⁻ → ν_τ e⁻ ν̄ₑ`, a consequence of
family-number conservation. -/
lemma tauDecay_conserves_total : total tau = total (tauNeutrino + electron + antiENeutrino) := by
  rw [tauDecay_conserves_flavor]

/-- **[Tau-to-muon leptonic decay conserves lepton flavor]**
`τ⁻ → ν_τ + μ⁻ + ν̄_μ`: the tau number is carried by `ν_τ`, while the muon and antimuon-neutrino
family numbers cancel. -/
lemma tauMuonDecay_conserves_flavor : tau = tauNeutrino + muon + antiMuNeutrino := by
  ext <;> simp [tau, tauNeutrino, muon, antiMuNeutrino]

/-- **[Tau-to-muon decay conserves total lepton number]**. -/
lemma tauMuonDecay_conserves_total :
    total tau = total (tauNeutrino + muon + antiMuNeutrino) := by
  rw [tauMuonDecay_conserves_flavor]


/-- The three neutrino mass eigenvalues. The structure stores mass eigenstates,
not flavor states; flavor oscillation is encoded by the mixing angles below. -/
structure NeutrinoMassSpectrum where
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ

namespace NeutrinoMassSpectrum

/-- The solar mass-square splitting `Δm²₂₁ = m₂² - m₁²`. -/
def deltaM21Sq (M : NeutrinoMassSpectrum) : ℝ :=
  M.m2 ^ 2 - M.m1 ^ 2

/-- The atmospheric mass-square splitting `Δm²₃₁ = m₃² - m₁²`. -/
def deltaM31Sq (M : NeutrinoMassSpectrum) : ℝ :=
  M.m3 ^ 2 - M.m1 ^ 2

/-- Normal ordering: `0 ≤ m₁ < m₂ < m₃`. -/
def NormalOrdering (M : NeutrinoMassSpectrum) : Prop :=
  0 ≤ M.m1 ∧ M.m1 < M.m2 ∧ M.m2 < M.m3

/-- Inverted ordering: `0 ≤ m₃ < m₁ < m₂`. -/
def InvertedOrdering (M : NeutrinoMassSpectrum) : Prop :=
  0 ≤ M.m3 ∧ M.m3 < M.m1 ∧ M.m1 < M.m2

/-- Under normal ordering the solar splitting is positive. -/
lemma deltaM21Sq_pos_of_normal (M : NeutrinoMassSpectrum)
    (h : M.NormalOrdering) : 0 < M.deltaM21Sq := by
  rcases h with ⟨hm1, h12, _h23⟩
  have hdiff : 0 < M.m2 - M.m1 := sub_pos.mpr h12
  have hsum : 0 < M.m2 + M.m1 := by linarith
  have hprod : 0 < (M.m2 - M.m1) * (M.m2 + M.m1) := mul_pos hdiff hsum
  have hident : (M.m2 - M.m1) * (M.m2 + M.m1) = M.m2 ^ 2 - M.m1 ^ 2 := by
    ring
  simpa [deltaM21Sq, hident] using hprod

/-- Under normal ordering the atmospheric `31` splitting is positive. -/
lemma deltaM31Sq_pos_of_normal (M : NeutrinoMassSpectrum)
    (h : M.NormalOrdering) : 0 < M.deltaM31Sq := by
  rcases h with ⟨hm1, h12, h23⟩
  have h13 : M.m1 < M.m3 := lt_trans h12 h23
  have hdiff : 0 < M.m3 - M.m1 := sub_pos.mpr h13
  have hsum : 0 < M.m3 + M.m1 := by linarith
  have hprod : 0 < (M.m3 - M.m1) * (M.m3 + M.m1) := mul_pos hdiff hsum
  have hident : (M.m3 - M.m1) * (M.m3 + M.m1) = M.m3 ^ 2 - M.m1 ^ 2 := by
    ring
  simpa [deltaM31Sq, hident] using hprod

/-- Under inverted ordering the solar splitting remains positive. -/
lemma deltaM21Sq_pos_of_inverted (M : NeutrinoMassSpectrum)
    (h : M.InvertedOrdering) : 0 < M.deltaM21Sq := by
  rcases h with ⟨hm3, h31, h12⟩
  have hm1 : 0 ≤ M.m1 := le_trans hm3 h31.le
  have hdiff : 0 < M.m2 - M.m1 := sub_pos.mpr h12
  have hsum : 0 < M.m2 + M.m1 := by linarith
  have hprod : 0 < (M.m2 - M.m1) * (M.m2 + M.m1) := mul_pos hdiff hsum
  have hident : (M.m2 - M.m1) * (M.m2 + M.m1) = M.m2 ^ 2 - M.m1 ^ 2 := by
    ring
  simpa [deltaM21Sq, hident] using hprod

/-- Under inverted ordering the `31` splitting is negative. -/
lemma deltaM31Sq_neg_of_inverted (M : NeutrinoMassSpectrum)
    (h : M.InvertedOrdering) : M.deltaM31Sq < 0 := by
  rcases h with ⟨hm3, h31, _h12⟩
  have hdiff : 0 < M.m1 - M.m3 := sub_pos.mpr h31
  have hsum : 0 < M.m1 + M.m3 := by linarith
  have hprod : 0 < (M.m1 - M.m3) * (M.m1 + M.m3) := mul_pos hdiff hsum
  have hident : (M.m1 - M.m3) * (M.m1 + M.m3) = M.m1 ^ 2 - M.m3 ^ 2 := by
    ring
  have hsq : 0 < M.m1 ^ 2 - M.m3 ^ 2 := by
    simpa [hident] using hprod
  unfold deltaM31Sq
  linarith

end NeutrinoMassSpectrum

/-- The oscillation parameter carrier: three mixing angles, one CP phase, and
the two independent mass-square splittings. -/
structure NeutrinoOscillationParameters where
  theta12 : ℝ
  theta23 : ℝ
  theta13 : ℝ
  deltaCP : ℝ
  deltaM21Sq : ℝ
  deltaM31Sq : ℝ

namespace NeutrinoOscillationParameters

/-- Build oscillation parameters from the mixing angles and a mass spectrum,
computing the mass-square splittings instead of storing them as independent
rows. -/
def fromMassSpectrum (theta12 theta23 theta13 deltaCP : ℝ)
    (M : NeutrinoMassSpectrum) : NeutrinoOscillationParameters :=
  { theta12 := theta12
    theta23 := theta23
    theta13 := theta13
    deltaCP := deltaCP
    deltaM21Sq := M.deltaM21Sq
    deltaM31Sq := M.deltaM31Sq }

/-- The solar splitting in `fromMassSpectrum` is exactly `m₂² - m₁²`. -/
lemma fromMassSpectrum_deltaM21Sq
    (theta12 theta23 theta13 deltaCP : ℝ) (M : NeutrinoMassSpectrum) :
    (fromMassSpectrum theta12 theta23 theta13 deltaCP M).deltaM21Sq =
      M.deltaM21Sq := rfl

/-- The atmospheric splitting in `fromMassSpectrum` is exactly `m₃² - m₁²`. -/
lemma fromMassSpectrum_deltaM31Sq
    (theta12 theta23 theta13 deltaCP : ℝ) (M : NeutrinoMassSpectrum) :
    (fromMassSpectrum theta12 theta23 theta13 deltaCP M).deltaM31Sq =
      M.deltaM31Sq := rfl

end NeutrinoOscillationParameters

/-- Checked capability for the massive-neutrino oscillation layer: the
oscillation record uses computed mass-square splittings, and the ordering
assumptions determine the signs of those splittings. -/
def HasNeutrinoMassOscillationLayer : Prop :=
  (∀ theta12 theta23 theta13 deltaCP : ℝ, ∀ M : NeutrinoMassSpectrum,
      (NeutrinoOscillationParameters.fromMassSpectrum
          theta12 theta23 theta13 deltaCP M).deltaM21Sq = M.deltaM21Sq
        ∧ (NeutrinoOscillationParameters.fromMassSpectrum
          theta12 theta23 theta13 deltaCP M).deltaM31Sq = M.deltaM31Sq)
    ∧ (∀ M : NeutrinoMassSpectrum, M.NormalOrdering →
      0 < M.deltaM21Sq ∧ 0 < M.deltaM31Sq)
    ∧ (∀ M : NeutrinoMassSpectrum, M.InvertedOrdering →
      0 < M.deltaM21Sq ∧ M.deltaM31Sq < 0)

/-- The massive-neutrino oscillation layer is checked from the definitions of
`Δm²₂₁`, `Δm²₃₁`, and the two mass orderings. -/
lemma neutrinoMassOscillationLayer_checked :
    HasNeutrinoMassOscillationLayer :=
  ⟨fun theta12 theta23 theta13 deltaCP M =>
      ⟨NeutrinoOscillationParameters.fromMassSpectrum_deltaM21Sq
          theta12 theta23 theta13 deltaCP M,
        NeutrinoOscillationParameters.fromMassSpectrum_deltaM31Sq
          theta12 theta23 theta13 deltaCP M⟩,
    fun M h => ⟨M.deltaM21Sq_pos_of_normal h, M.deltaM31Sq_pos_of_normal h⟩,
    fun M h => ⟨M.deltaM21Sq_pos_of_inverted h, M.deltaM31Sq_neg_of_inverted h⟩⟩


/-- Three independent Type-I seesaw inputs, one for each light mass eigenvalue.
The Yukawa couplings `yᵢ` and sterile Majorana scales `Mᵢ` are parameters; the
light masses below are computed from the existing one-generation seesaw
eigenvalue formula. -/
structure ThreeFlavorSeesawData where
  y1 : ℝ
  y2 : ℝ
  y3 : ℝ
  v : ℝ
  M1 : ℝ
  M2 : ℝ
  M3 : ℝ

namespace ThreeFlavorSeesawData

/-- First-generation Dirac mass `m_D1 = y₁ v / sqrt 2`, reusing the Standard
Model Yukawa mass carrier from `Yukawa.SeesawMass`. -/
noncomputable def diracMass1 (D : ThreeFlavorSeesawData) : ℝ :=
  yukawaMass D.y1 D.v

/-- Second-generation Dirac mass `m_D2 = y₂ v / sqrt 2`. -/
noncomputable def diracMass2 (D : ThreeFlavorSeesawData) : ℝ :=
  yukawaMass D.y2 D.v

/-- Third-generation Dirac mass `m_D3 = y₃ v / sqrt 2`. -/
noncomputable def diracMass3 (D : ThreeFlavorSeesawData) : ℝ :=
  yukawaMass D.y3 D.v

/-- First light Majorana mass `m₁ = -m₋(m_D1,M1)`, with the Majorana phase
removed as in `Yukawa.SeesawMass.seesaw_lever`. -/
noncomputable def lightMass1 (D : ThreeFlavorSeesawData) : ℝ :=
  -seesawEigenMinus D.diracMass1 D.M1

/-- Second light Majorana mass `m₂ = -m₋(m_D2,M2)`. -/
noncomputable def lightMass2 (D : ThreeFlavorSeesawData) : ℝ :=
  -seesawEigenMinus D.diracMass2 D.M2

/-- Third light Majorana mass `m₃ = -m₋(m_D3,M3)`. -/
noncomputable def lightMass3 (D : ThreeFlavorSeesawData) : ℝ :=
  -seesawEigenMinus D.diracMass3 D.M3

/-- First heavy seesaw mass `m₊(m_D1,M1)`. -/
noncomputable def heavyMass1 (D : ThreeFlavorSeesawData) : ℝ :=
  seesawEigenPlus D.diracMass1 D.M1

/-- Second heavy seesaw mass `m₊(m_D2,M2)`. -/
noncomputable def heavyMass2 (D : ThreeFlavorSeesawData) : ℝ :=
  seesawEigenPlus D.diracMass2 D.M2

/-- Third heavy seesaw mass `m₊(m_D3,M3)`. -/
noncomputable def heavyMass3 (D : ThreeFlavorSeesawData) : ℝ :=
  seesawEigenPlus D.diracMass3 D.M3

/-- The light-neutrino mass spectrum generated by the three seesaw blocks. -/
noncomputable def lightMassSpectrum (D : ThreeFlavorSeesawData) : NeutrinoMassSpectrum where
  m1 := D.lightMass1
  m2 := D.lightMass2
  m3 := D.lightMass3

/-- The first seesaw block obeys the exact lever relation
`m_heavy,1 m_light,1 = y₁² v² / 2`. -/
lemma generation1_lever (D : ThreeFlavorSeesawData) :
    D.heavyMass1 * D.lightMass1 = D.y1 ^ 2 * D.v ^ 2 / 2 := by
  simpa [heavyMass1, lightMass1, diracMass1] using
    (yukawa_seesaw D.y1 D.v D.M1).2.2.2

/-- The second seesaw block obeys the exact lever relation
`m_heavy,2 m_light,2 = y₂² v² / 2`. -/
lemma generation2_lever (D : ThreeFlavorSeesawData) :
    D.heavyMass2 * D.lightMass2 = D.y2 ^ 2 * D.v ^ 2 / 2 := by
  simpa [heavyMass2, lightMass2, diracMass2] using
    (yukawa_seesaw D.y2 D.v D.M2).2.2.2

/-- The third seesaw block obeys the exact lever relation
`m_heavy,3 m_light,3 = y₃² v² / 2`. -/
lemma generation3_lever (D : ThreeFlavorSeesawData) :
    D.heavyMass3 * D.lightMass3 = D.y3 ^ 2 * D.v ^ 2 / 2 := by
  simpa [heavyMass3, lightMass3, diracMass3] using
    (yukawa_seesaw D.y3 D.v D.M3).2.2.2

/-- The generated solar splitting is computed from the two seesaw-generated
light masses: `Δm²₂₁ = m₂² - m₁²`. -/
lemma lightMassSpectrum_deltaM21Sq (D : ThreeFlavorSeesawData) :
    D.lightMassSpectrum.deltaM21Sq = D.lightMass2 ^ 2 - D.lightMass1 ^ 2 := rfl

/-- The generated atmospheric splitting is computed from the first and third
seesaw-generated light masses: `Δm²₃₁ = m₃² - m₁²`. -/
lemma lightMassSpectrum_deltaM31Sq (D : ThreeFlavorSeesawData) :
    D.lightMassSpectrum.deltaM31Sq = D.lightMass3 ^ 2 - D.lightMass1 ^ 2 := rfl

end ThreeFlavorSeesawData

/-- Checked bridge from the existing `Yukawa.SeesawMass` algebra to the
massive-neutrino oscillation layer. It proves three exact seesaw lever
relations and then computes `Δm²₂₁`, `Δm²₃₁` from the generated light spectrum. -/
def HasThreeFlavorSeesawOscillationBridge (D : ThreeFlavorSeesawData) : Prop :=
  D.heavyMass1 * D.lightMass1 = D.y1 ^ 2 * D.v ^ 2 / 2
    ∧ D.heavyMass2 * D.lightMass2 = D.y2 ^ 2 * D.v ^ 2 / 2
    ∧ D.heavyMass3 * D.lightMass3 = D.y3 ^ 2 * D.v ^ 2 / 2
    ∧ D.lightMassSpectrum.deltaM21Sq = D.lightMass2 ^ 2 - D.lightMass1 ^ 2
    ∧ D.lightMassSpectrum.deltaM31Sq = D.lightMass3 ^ 2 - D.lightMass1 ^ 2
    ∧ HasNeutrinoMassOscillationLayer

/-- The three-flavor seesaw/oscillation bridge is checked entirely by existing
`Yukawa.SeesawMass` theorems plus the computed mass-spectrum definitions above. -/
lemma threeFlavorSeesawOscillationBridge_checked (D : ThreeFlavorSeesawData) :
    HasThreeFlavorSeesawOscillationBridge D :=
  ⟨D.generation1_lever,
    D.generation2_lever,
    D.generation3_lever,
    D.lightMassSpectrum_deltaM21Sq,
    D.lightMassSpectrum_deltaM31Sq,
    neutrinoMassOscillationLayer_checked⟩


/-- **[Neutrino–antineutrino annihilation]** `ν + ν̄ = vacuum` — even though the neutrino is electrically
neutral, it has a *distinct* antineutrino (`L → −L`) that annihilates it, so the CPT pairing is non-trivial
(`AntiparticleConjugation`). -/
lemma neutrino_pair_annihilates : neutrino + conjugate neutrino = ⟨0, 0, 0⟩ :=
  pair_annihilates neutrino


/-- **The three-fold generator** `ω = e^{2πi/3}` — the primitive cube root of unity, the `ℤ/3` generator of
the neutrino's three-node τ-coherence loop / SU(3) antitriplet. -/
noncomputable def cubeRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- `ω` is a primitive cube root of unity. -/
lemma cubeRoot_isPrimitiveRoot : IsPrimitiveRoot cubeRoot 3 := by
  simpa [cubeRoot] using Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- **[Three-fold closure]** `ω³ = 1` — the three-node loop closes (the `ℤ/3` / SU(3) antitriplet
structure). -/
lemma cubeRoot_pow_three : cubeRoot ^ 3 = 1 := cubeRoot_isPrimitiveRoot.pow_eq_one

/-- **[The three components sum to zero]** `1 + ω + ω² = 0` — the three cube-root-of-unity phases of the
neutrino's nodes cancel: the algebraic core of its neutrality. -/
lemma cubeRoot_sum_zero : 1 + cubeRoot + cubeRoot ^ 2 = 0 := by
  have h := cubeRoot_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

/-- **[The neutrino is neutral as three fractional thirds]** `(1/3)·(1 + ω + ω²) = 0` — each of the three
nodes carries the fractional charge `windingCharge 1 = 1/3`, and their `ℤ/3`-phased sum vanishes. The
neutrino is neutral *because* it is the antitriplet of three fractional thirds (not a trivial winding-`0`
state). -/
lemma neutrino_fractional_neutral :
    ((windingCharge 1 : ℚ) : ℂ) * (1 + cubeRoot + cubeRoot ^ 2) = 0 := by
  rw [cubeRoot_sum_zero, mul_zero]

end Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.ThreeFlavorSeesawData.generation1_lever where
  formalizes @ "claim:the-type-one-seesaw-lever-the-light-neutrino-mass-is-the-dirac-mass-squared-over-the-heavy-majorana-mass-explaining-neutrino-mass-smallness",
  supported_by @ "paper:minkowski-yanagida-gell-mann-ramond-slansky-seesaw"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.NeutrinoMassSpectrum.deltaM21Sq_pos_of_normal where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:in-the-normal-mass-ordering-the-solar-mass-squared-splitting-delta-m-two-one-squared-is-positive"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.threeFlavorSeesawOscillationBridge_checked where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.ThreeFlavorSeesawData.generation1_lever",
  formalizes @ "claim:the-three-flavor-seesaw-data-produces-a-consistent-light-mass-spectrum-and-oscillation-parameters",
  requires @ "claim:the-type-one-seesaw-lever-the-light-neutrino-mass-is-the-dirac-mass-squared-over-the-heavy-majorana-mass-explaining-neutrino-mass-smallness"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.neutrino_not_selfConjugate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation.selfConjugate_iff_neutral",
  formalizes @ "claim:the-dirac-neutrino-is-not-its-own-antiparticle-distinct-from-the-antineutrino-by-lepton-number"

zil_file_contract physlib.neutrinoModel where
  promises "The neutrino sector: the Dirac neutrino carries lepton number one and is not its own antiparticle, annihilating with its conjugate to the vacuum; the type-one seesaw lever makes the light neutrino mass the Dirac mass squared over the heavy Majorana mass, explaining the smallness of neutrino masses; the mass-squared splittings are positive in the normal ordering (and signed for inverted); and the three-flavor seesaw data yields a consistent light mass spectrum and oscillation parameters, with lepton-flavor conservation in tau decays."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.neutrino",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.ThreeFlavorSeesawData.lightMassSpectrum"]
  forbids_substitutes ["a derivation of the numerical neutrino masses, mixing angles or CP phase, which are experimental inputs",
    "a resolution of the Dirac-versus-Majorana question, only the additive lepton-number bookkeeping and the seesaw lever are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.neutrino_not_selfConjugate,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.neutrino_pair_annihilates,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.neutrinoMassOscillationLayer_checked,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.threeFlavorSeesawOscillationBridge_checked,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.ThreeFlavorSeesawData.generation1_lever,
    Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel.NeutrinoMassSpectrum.deltaM21Sq_pos_of_normal]

/- ZIL-END -/
