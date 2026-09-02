/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator
meta import Zil

/-!
# The charged leptons: family numbers, tau properties, generations as clock frequencies

The lepton sector in four namespaces (each formerly its own module):

* **Part I — `LeptonFlavorNumbers`.** The three separately conserved family numbers `Lₑ, L_μ, L_τ`
  (`LeptonFlavor` with componentwise `+`), the nine lepton assignments, and muon decay
  `μ⁻ → e⁻ + ν̄ₑ + ν_μ` conserving each family number (`muonDecay_conserves_flavor`) and hence the
  total `L` (`muonDecay_conserves_total`). Formalizes the conserved-family-number limit (massless
  neutrinos); oscillations violate family number while preserving total `L` — noted, not contradicted.
* **Part II — `TauLeptonProperties`.** The third generation with PDG values as data and the physical
  relations as theorems: the mass ordering `mₑ < m_μ < m_τ` (`lepton_mass_ordering`), the
  width–lifetime relation `Γ·τ = ħ` (`decayWidth_mul_lifetime`), Sargent's `m⁵` leptonic-width rule
  with the mass-only universality ratio `Γ_τ/Γ_μ = (m_τ/m_μ)⁵` (`sargent_universality_ratio`), and the
  branching-fraction normalization `B_e + B_μ + B_had = 1` (`tau_branching_sum`).
* **Part III — `LeptonGenerationMass`.** A generation as a dimensionless internal-clock frequency
  ratio `r = ω/ω_e` with `m = ħω/c²`: `generationMass_eq_ratio_mul_electronMass` (`m = r·m_e`), the de
  Broglie clock and Dirac dispersion, and the dimensional analysis of the mass ratio — the same pure
  number read three ways as frequency ratio (`mass_ratio_eq_frequency_ratio`), winding-number ratio
  (`windingMass_ratio_eq_winding_ratio`), and Yukawa-coupling ratio (`yukawa_mass_ratio`, the Higgs
  VEV cancels). The *value* of the ratio is not predicted — the generation/Yukawa mass problem is open.
* **Part IV — `ChargedLeptonGenerations`.** The three generations `e, μ, τ` at abstract ratios
  `1 < r_μ < r_τ`: `lepton_mass_ratio` (`m_g/m_e = r`), the mass hierarchy from the ratio ordering
  (`lepton_mass_hierarchy`), and three-generation universality (same charge and spin-½ statistics,
  `ribbonTwist ½ = −1`; only the frequency differs).

**Honest layering.** Proven: the family-number bookkeeping, the width–lifetime and Sargent identities,
the branching normalization, `m = ħω/c²` with its three dimensionless readings of the mass ratio, and
the hierarchy from the ratio ordering. Data: the PDG masses, lifetimes, and branching fractions of
Part II. Open: the values of the generation ratios (equivalently the Yukawa couplings).

## References

* Lepton family number and muon decay (refines `Particles.BaryonLeptonNumberConservation`); Particle
  Data Group, Prog. Theor. Exp. Phys. 2022, 083C01 (`τ` mass 1776.86 MeV, lifetime 2.903×10⁻¹³ s,
  `B(τ→eν̄ν) = 17.82%`, `B(τ→μν̄ν) = 17.39%`); de Broglie internal clock (`m c² = ħ ω`), Yukawa mass
  `m = y v`. Built on `Winding.NumberMass`/`Winding.MassDiracOperator` and
  `Hopf.ChargeConjugationRibbonTwist`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers


/-- The **lepton family numbers** of a state: electron number, muon number, tau number. -/
@[ext]
structure LeptonFlavor where
  /-- Electron-family lepton number. -/
  eNum : ℤ
  /-- Muon-family lepton number. -/
  muNum : ℤ
  /-- Tau-family lepton number. -/
  tauNum : ℤ

/-- Family numbers add componentwise across a multiparticle state. -/
instance : Add LeptonFlavor where
  add a b := ⟨a.eNum + b.eNum, a.muNum + b.muNum, a.tauNum + b.tauNum⟩

@[simp] lemma add_eNum (a b : LeptonFlavor) : (a + b).eNum = a.eNum + b.eNum := rfl
@[simp] lemma add_muNum (a b : LeptonFlavor) : (a + b).muNum = a.muNum + b.muNum := rfl
@[simp] lemma add_tauNum (a b : LeptonFlavor) : (a + b).tauNum = a.tauNum + b.tauNum := rfl


/-- Electron `e⁻` `(1, 0, 0)`. -/
def electron : LeptonFlavor := ⟨1, 0, 0⟩
/-- Electron neutrino `νₑ` `(1, 0, 0)`. -/
def eNeutrino : LeptonFlavor := ⟨1, 0, 0⟩
/-- Electron antineutrino `ν̄ₑ` `(−1, 0, 0)`. -/
def antiENeutrino : LeptonFlavor := ⟨-1, 0, 0⟩
/-- Muon `μ⁻` `(0, 1, 0)`. -/
def muon : LeptonFlavor := ⟨0, 1, 0⟩
/-- Muon neutrino `ν_μ` `(0, 1, 0)`. -/
def muNeutrino : LeptonFlavor := ⟨0, 1, 0⟩
/-- Muon antineutrino `ν̄_μ` `(0, -1, 0)`. -/
def antiMuNeutrino : LeptonFlavor := ⟨0, -1, 0⟩
/-- Tau `τ⁻` `(0, 0, 1)`. -/
def tau : LeptonFlavor := ⟨0, 0, 1⟩
/-- Tau neutrino `ν_τ` `(0, 0, 1)`. -/
def tauNeutrino : LeptonFlavor := ⟨0, 0, 1⟩
/-- Tau antineutrino `ν̄_τ` `(0, 0, -1)`. -/
def antiTauNeutrino : LeptonFlavor := ⟨0, 0, -1⟩


/-- **[Muon decay conserves each family number]** `μ⁻ → e⁻ + ν̄ₑ + ν_μ`: the electron number is `0` on both
sides (`e⁻` and `ν̄ₑ` cancel), the muon number is `1` on both sides — *each* `Lₑ, L_μ, L_τ` is conserved
separately, not just the total. -/
lemma muonDecay_conserves_flavor : muon = electron + antiENeutrino + muNeutrino := by
  ext <;> simp [muon, electron, antiENeutrino, muNeutrino]

/-- **Total lepton number** `L = Lₑ + L_μ + L_τ`. -/
def total (f : LeptonFlavor) : ℤ := f.eNum + f.muNum + f.tauNum

@[simp] lemma total_add (a b : LeptonFlavor) : total (a + b) = total a + total b := by
  simp only [total, add_eNum, add_muNum, add_tauNum]; ring

/-- **[Muon decay conserves total `L`]** the conservation of every family number forces conservation of the
total lepton number `L = Lₑ + L_μ + L_τ`. -/
lemma muonDecay_conserves_total : total muon = total (electron + antiENeutrino + muNeutrino) := by
  rw [muonDecay_conserves_flavor]

end Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers

/-! ## Part II — tau-lepton properties: mass, lifetime, width, and leptonic universality -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.TauLeptonProperties


/-- **Electron mass** `mₑ = 0.51099895 MeV` (PDG). -/
def electronMass : ℝ := 0.51099895

/-- **Muon mass** `m_μ = 105.6583755 MeV` (PDG). -/
def muonMass : ℝ := 105.6583755

/-- **Tau mass** `m_τ = 1776.86 MeV` (PDG). -/
def tauMass : ℝ := 1776.86

/-- **The charged-lepton mass hierarchy** `mₑ < m_μ < m_τ` (three generations, increasing mass). -/
lemma lepton_mass_ordering : electronMass < muonMass ∧ muonMass < tauMass := by
  refine ⟨?_, ?_⟩ <;> norm_num [electronMass, muonMass, tauMass]


/-- **The decay width from the lifetime** `Γ = ħ/τ` — the uncertainty-principle relation between a
particle's total width and its mean lifetime. -/
noncomputable def decayWidth (ħ τ : ℝ) : ℝ := ħ / τ

/-- **Width times lifetime is `ħ`** `Γ·τ = ħ` (the width–lifetime relation). -/
lemma decayWidth_mul_lifetime (ħ τ : ℝ) (hτ : τ ≠ 0) : decayWidth ħ τ * τ = ħ := by
  unfold decayWidth; field_simp

/-- **Tau lifetime** `τ_τ = 2.903×10⁻¹³ s` (PDG). -/
def tauLifetime : ℝ := 2.903e-13

/-- **Muon lifetime** `τ_μ = 2.1969811×10⁻⁶ s` (PDG). -/
def muonLifetime : ℝ := 2.1969811e-6

/-- **The tau is far shorter-lived than the muon** `τ_τ < τ_μ` — a heavier lepton with more open decay
channels decays faster. -/
lemma tau_shorter_than_muon : tauLifetime < muonLifetime := by
  norm_num [tauLifetime, muonLifetime]


/-- **The leptonic partial width** `Γ(ℓ→ℓ'ν̄ν) = G_F² m_ℓ⁵/(192π³)` (tree-level Fermi theory, Sargent's
`m⁵` rule). -/
noncomputable def sargentWidth (GF m : ℝ) : ℝ := GF ^ 2 * m ^ 5 / (192 * Real.pi ^ 3)

/-- **Lepton universality: the leptonic width ratio is mass-only** `Γ_τ/Γ_μ = (m_τ/m_μ)⁵`: because a
single Fermi constant `G_F` governs both `τ` and `μ` leptonic decays, the ratio of their partial widths
depends only on the mass ratio to the fifth power. -/
lemma sargent_universality_ratio (GF : ℝ) (hGF : GF ≠ 0) :
    sargentWidth GF tauMass / sargentWidth GF muonMass = (tauMass / muonMass) ^ 5 := by
  have hμ : muonMass ≠ 0 := by norm_num [muonMass]
  have hden : (192 * Real.pi ^ 3) ≠ 0 := by positivity
  unfold sargentWidth
  rw [div_pow]
  field_simp


/-- **`B(τ → e ν̄ν)` = 17.82%** (PDG). -/
def brTauElectron : ℝ := 0.1782

/-- **`B(τ → μ ν̄ν)` = 17.39%** (PDG). -/
def brTauMuon : ℝ := 0.1739

/-- **`B(τ → hadrons)` = 64.79%** (PDG). -/
def brTauHadron : ℝ := 0.6479

/-- **The tau branching fractions are normalized** `B_e + B_μ + B_had = 1`: the total decay probability
into the three channel classes is one. The near-equality `B_e ≈ B_μ` is lepton universality (equal
weak couplings, tiny phase-space difference). -/
lemma tau_branching_sum : brTauElectron + brTauMuon + brTauHadron = 1 := by
  norm_num [brTauElectron, brTauMuon, brTauHadron]

end Physlib.QuantumMechanics.ComplexAction.Particles.TauLeptonProperties

/-! ## Part III — charged-lepton generations as internal-clock frequencies, and the mass ratio -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.LeptonGenerationMass

open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.Winding.MassDiracOperator
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.DiracMatter
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist


/-- **[Scaling the clock scales the mass]** `m(r·ω) = r·m(ω)`. -/
lemma comptonMass_smul (r ω c ħ : ℝ) : comptonMass (r * ω) c ħ = r * comptonMass ω c ħ := by
  unfold comptonMass; ring

/-- **The mass of the generation at frequency ratio `r`** `m = ħ(rω_e)/c²` — the electron's internal clock
scaled by the dimensionless ratio `r = ω/ω_e` (`r = 1` the electron). No mass value is fixed. -/
noncomputable def generationMass (r ωe c ħ : ℝ) : ℝ := comptonMass (r * ωe) c ħ

/-- **[`m = r·m_e`]** the generation's mass is the electron mass scaled by the frequency ratio `r`. -/
lemma generationMass_eq_ratio_mul_electronMass (r ωe c ħ : ℝ) :
    generationMass r ωe c ħ = r * comptonMass ωe c ħ := by
  rw [generationMass, comptonMass_smul]

/-- **[de Broglie clock]** `ħ ω = m c²` for the generation at ratio `r`. -/
lemma generationMass_restEnergy (r ωe c ħ : ℝ) (hc : c ≠ 0) :
    ħ * (r * ωe) = generationMass r ωe c ħ * c ^ 2 := by
  rw [generationMass]; exact comptonMass_restEnergy (r * ωe) c ħ hc

/-- **[Dirac dispersion]** `E = √(p² + m²)` for the generation at ratio `r`. -/
lemma generation_diracEnergy (r p1 p2 p3 ωe c ħ : ℝ) :
    diracEnergy p1 p2 p3 (generationMass r ωe c ħ)
      = Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + (ħ * (r * ωe) / c ^ 2) ^ 2) := by
  rw [generationMass, diracEnergy_comptonMass]

/-- **[Dirac rest energy = clock energy]** `E_rest · c² = ħ ω`. -/
lemma generation_restEnergy_clock (r ωe c ħ : ℝ) (hc : c ≠ 0)
    (hm : 0 ≤ generationMass r ωe c ħ) :
    diracEnergy 0 0 0 (generationMass r ωe c ħ) * c ^ 2 = ħ * (r * ωe) := by
  rw [generationMass]; exact diracRestEnergy_comptonMass_planck (r * ωe) c ħ hc hm


/-- **[Mass ratio = frequency ratio]** `m(ω₂)/m(ω₁) = ω₂/ω₁`: the lepton mass ratio is the internal-clock
frequency ratio — the dimensionful `ħ` and `c²` of `m = ħω/c²` **cancel**, leaving a pure dimensionless
number. This is the dimensional meaning of the mass ratio. -/
lemma mass_ratio_eq_frequency_ratio (ω₁ ω₂ c ħ : ℝ) (hħ : ħ ≠ 0) (hc : c ≠ 0) :
    comptonMass ω₂ c ħ / comptonMass ω₁ c ħ = ω₂ / ω₁ := by
  unfold comptonMass
  rw [div_div_div_cancel_right₀]
  · rw [mul_div_mul_left _ _ hħ]
  · exact pow_ne_zero 2 hc

/-- **[Mass ratio = winding-number ratio]** if the mass is winding-quantized (`windingMass n = n m₀`), the
ratio is the winding-number ratio `n₂/n₁` — a ratio of counts. -/
lemma windingMass_ratio_eq_winding_ratio (n₁ n₂ : ℤ) (ω₀ c ħ : ℝ)
    (hm₀ : comptonMass ω₀ c ħ ≠ 0) :
    windingMass n₂ ω₀ c ħ / windingMass n₁ ω₀ c ħ = (n₂ : ℝ) / (n₁ : ℝ) := by
  rw [windingMass_eq_zsmul, windingMass_eq_zsmul, mul_div_mul_right _ _ hm₀]

/-- **The Yukawa mass** `m = y v` — a coupling `y` times the common Higgs VEV `v`. -/
noncomputable def yukawaMass (y v : ℝ) : ℝ := y * v

/-- **[Mass ratio = Yukawa-coupling ratio]** in the Standard Model the lepton mass ratio is the Yukawa
coupling ratio `y₂/y₁`: the common Higgs VEV `v` cancels, leaving a dimensionless coupling ratio. -/
lemma yukawa_mass_ratio (y₁ y₂ v : ℝ) (hv : v ≠ 0) :
    yukawaMass y₂ v / yukawaMass y₁ v = y₂ / y₁ := by
  rw [yukawaMass, yukawaMass, mul_div_mul_right _ _ hv]


/-- **[Every generation is a spin-½ fermion]** `ribbonTwist ½ = −1` — charge and statistics are
generation-independent; only the mass (frequency) differs. -/
lemma generation_fermion : ribbonTwist (1 / 2) = -1 := ribbonTwist_fermion

end Physlib.QuantumMechanics.ComplexAction.Particles.LeptonGenerationMass

/-! ## Part IV — the three charged-lepton generations e, μ, τ -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ChargedLeptonGenerations

open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Particles.LeptonGenerationMass


/-- **The electron mass** `m_e = comptonMass ω_e` — the base generation (frequency ratio `r = 1`). -/
noncomputable def electronMass (ωe c ħ : ℝ) : ℝ := comptonMass ωe c ħ

/-- **The muon mass** `m_μ = r_μ·m_e` at the muon's (measured) frequency ratio `r_μ`. -/
noncomputable def muonMass (rμ ωe c ħ : ℝ) : ℝ := generationMass rμ ωe c ħ

/-- **The tau mass** `m_τ = r_τ·m_e` at the tau's (measured) frequency ratio `r_τ`. -/
noncomputable def tauMass (rτ ωe c ħ : ℝ) : ℝ := generationMass rτ ωe c ħ

/-- **[Electron is the base]** `m_e = generationMass 1` (ratio `r = 1`). -/
lemma electronMass_eq_generation_one (ωe c ħ : ℝ) :
    electronMass ωe c ħ = generationMass 1 ωe c ħ := by
  rw [electronMass, generationMass_eq_ratio_mul_electronMass, one_mul]

/-- **[The mass-to-electron ratio is the frequency ratio]** `m_g/m_e = r`: each generation's mass divided by
the electron mass is exactly its dimensionless frequency ratio `r` (the dimensional-analysis result
`mass_ratio_eq_frequency_ratio` applied — no `ħ`, `c`, or scale survives). -/
lemma lepton_mass_ratio (r ωe c ħ : ℝ) (hm : comptonMass ωe c ħ ≠ 0) :
    generationMass r ωe c ħ / electronMass ωe c ħ = r := by
  rw [electronMass, generationMass_eq_ratio_mul_electronMass, mul_div_assoc,
    div_self hm, mul_one]


/-- **[Charged-lepton mass hierarchy]** `1 < r_μ < r_τ ⟹ m_e < m_μ < m_τ`: with a positive electron mass, the
mass ordering follows from the frequency-ratio ordering. No specific ratio values are used. -/
lemma lepton_mass_hierarchy (rμ rτ ωe c ħ : ℝ) (hμ : 1 < rμ) (hτ : rμ < rτ)
    (hm : 0 < comptonMass ωe c ħ) :
    electronMass ωe c ħ < muonMass rμ ωe c ħ ∧ muonMass rμ ωe c ħ < tauMass rτ ωe c ħ := by
  rw [electronMass, muonMass, tauMass, generationMass_eq_ratio_mul_electronMass,
    generationMass_eq_ratio_mul_electronMass]
  refine ⟨?_, ?_⟩
  · nth_rewrite 1 [← one_mul (comptonMass ωe c ħ)]
    exact mul_lt_mul_of_pos_right hμ hm
  · exact mul_lt_mul_of_pos_right hτ hm

/-- **[Three-generation universality]** all three charged leptons are spin-½ fermions (`ribbonTwist ½ = −1` —
shared charge and statistics) and differ only by mass: the muon and tau masses are the electron mass scaled
by their frequency ratios. -/
lemma three_generation_universality (rμ rτ ωe c ħ : ℝ) :
    ribbonTwist (1 / 2) = -1 ∧
      muonMass rμ ωe c ħ = rμ * comptonMass ωe c ħ ∧
      tauMass rτ ωe c ħ = rτ * comptonMass ωe c ħ :=
  ⟨ribbonTwist_fermion, generationMass_eq_ratio_mul_electronMass rμ ωe c ħ,
    generationMass_eq_ratio_mul_electronMass rτ ωe c ħ⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.ChargedLeptonGenerations

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muonDecay_conserves_flavor where
  formalizes @ "claim:muon-decay-conserves-each-lepton-family-number-separately",
  caveat @ "claim:the-conserved-family-number-limit-massive-neutrino-oscillations-violate-it"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.TauLeptonProperties.sargent_universality_ratio where
  formalizes @ "claim:lepton-universality-the-leptonic-width-ratio-is-the-mass-ratio-to-the-fifth-power",
  supported_by @ "measurement:pdg-2022-tau-lepton-properties"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.LeptonGenerationMass.mass_ratio_eq_frequency_ratio where
  formalizes @ "claim:the-lepton-mass-ratio-is-the-dimensionless-internal-clock-frequency-ratio",
  caveat @ "claim:the-value-of-the-ratio-is-not-predicted-the-generation-yukawa-mass-problem-is-open"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ChargedLeptonGenerations.lepton_mass_hierarchy where
  formalizes @ "claim:the-charged-lepton-mass-hierarchy-follows-from-the-frequency-ratio-ordering",
  requires @ "claim:the-lepton-mass-ratio-is-the-dimensionless-internal-clock-frequency-ratio"

zil_file_contract physlib.leptonFlavorNumbers where
  promises "The charged leptons: muon decay conserves each family number separately, lepton universality makes the leptonic width ratio the mass ratio to the fifth power, the lepton mass ratio is the dimensionless internal-clock frequency ratio, and the mass hierarchy follows from the frequency-ratio ordering."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.LeptonFlavor",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.LeptonGenerationMass.generationMass"]
  forbids_substitutes ["the values of the generation ratios, the open Yukawa mass problem",
    "the PDG masses and lifetimes, empirical inputs"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.LeptonFlavorNumbers.muonDecay_conserves_flavor,
    Physlib.QuantumMechanics.ComplexAction.Particles.TauLeptonProperties.sargent_universality_ratio,
    Physlib.QuantumMechanics.ComplexAction.Particles.LeptonGenerationMass.mass_ratio_eq_frequency_ratio,
    Physlib.QuantumMechanics.ComplexAction.Particles.ChargedLeptonGenerations.lepton_mass_hierarchy]

/- ZIL-END -/
