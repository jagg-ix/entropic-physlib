/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.VanDerWaalsRadii
public import Physlib.QuantumMechanics.OneDimension.HarmonicOscillator.Basic
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# The polarizability–van-der-Waals-radius scaling law `R_vdW ∝ α^{1/7}`

D. V. Fedorov, M. Sadhukhan, M. Stöhr and A. Tkatchenko, *Quantum-Mechanical Relation between Atomic
Dipole Polarizability and the van der Waals Radius*, Phys. Rev. Lett. (arXiv:1803.11507), derive — inside
the quantum Drude oscillator (QDO) model — a scaling law relating the van der Waals radius `R_vdW`
(the periphery radius of [[VanDerWaalsRadii]]) to the atomic dipole polarizability `α`. It is markedly
different from the classical hard-sphere result.

This extends `VanDerWaalsRadii` with the paper's **derived** relations (the fitted prefactor `2.54` of
Eq. 7, and `C₂, C₃` of Eq. 13, are kept as free constants `C`, not hardcoded):

* **§A — the classical scaling `R_a³ = α` (Eq. 1).** from the classical force balance
  `q𝓔 = q²d/R_a³` and the induced-dipole definition `qd = α𝓔`, one gets `R_a³ = α`, i.e. the classical
  exponent `1/3` (`classical_forceBalance_cube`).
* **§B — the dispersion force is the energy gradient (Eq. 4).** for `E_disp = −¾ α²ℏω/R⁶` and
  `F_disp = −9/2 α²ℏω/R⁷`, the degree-`−6` homogeneity gives `R·F_disp = 6 E_disp`
  (`dispersion_force_energy`) — the content of `F_disp = −dE_disp/dR`.
* **§C — the quantum scaling `R_vdW ∝ α^{1/7}` (Eqs. 7, 13).** the QDO exchange/dispersion balance yields
  the exponent `1/7`, markedly different from the classical `1/3` (`qm_exponent_ne_classical`); its
  higher-multipole generalization `2/(7(n+1))` recovers `1/7` at the dipole order `n = 1`
  (`multipoleVdWExponent_dipole`).
* **§D — the heteronuclear combination rule (Eq. 9).** the equilibrium distance
  `D_a = 2C((α_A+α_B)/2)^{1/7}` reduces to twice the homonuclear radius for identical atoms
  (`equilibriumDistanceHetero_homonuclear`).
* **§E — the QDO dipole polarizability.** `α = q²/(μω²)` (`qdoPolarizability`) and its inverse
  `q² = α μ ω²` (`qdoPolarizability_charge_sq`).
* **§F — the exchange integral and its gradient (Eqs. 2–3).** the Heitler–London exchange energy
  `J_ex = q²/(2R) e^{−μω R²/2ℏ}` (`exchangeIntegral`) and the exact force `F_ex = −dJ_ex/dR`
  (`exchangeIntegral_hasDerivAt`; Eq. 3 is its large-`μω/ℏ` approximation).
* **§G — the seventh-power form (Eqs. 5–6).** `R_vdW⁷ = C⁷ α` (`qmVdWRadius_pow_seven`) and the
  proportionality function `C(μω,R) = ½(3ℏ/μω)^{2/7} exp(2μω R²/7ℏ)` (`proportionalityC`).
* **§H — the alternative combination rules (Eqs. 10–12).** arithmetic/geometric means of radii and of
  polarizabilities, all agreeing at `2 R_vdW` for identical atoms (`*_homonuclear`).
* **§I — the force balance is the physical link.** `forceBalance_seventh_power`: setting the exchange
  repulsion (§F) equal to the dispersion attraction (§B) with `q² = α μ ω²` (§E) forces
  `μ²ω² R⁷ e^{−μω R²/2ℏ} = 9 ℏ² α`, i.e. `R_vdW⁷ ∝ α` — deriving the `α^{1/7}` scaling (§C, §G) from the
  QDO exchange/dispersion mechanism.
* **§J — the QDO is a charged PhysLib harmonic oscillator.** links the polarizability to
  `QuantumMechanics.OneDimension.HarmonicOscillator`: `qdoPolarizabilityOfHO` (`α = q²/(Q.m Q.ω²)`),
  `qdoPolarizabilityOfHO_pos` (positive by the oscillator's `hm`, `hω`), and
  `qdoPolarizabilityOfHO_charge_sq`.
* **§K — the inverted QHO.** `qdoPolarizabilityInverted_eq_neg`: the inversion `ω² → −ω²` (`ω → iω`,
  `OperatorAlgebra.InvertedOscillatorPseudoHermitian`) flips the polarizability sign, `α_inv = −α`.
* **§L — the Compton-clock frequency framework.** `qdoFrequency_eq_deBroglie_energyQuantum` and
  `comptonFrequency_eq_deBroglie_restEnergy`: the QDO frequency `ω = ω_dB(ℏω)` and the electron's
  `ω_C = ω_dB(mc²)` / Zitterbewegung `2ω_C` (`ComptonClock`, `ComptonClock.ElectronZitterbewegung`) share
  the single relation `ω = E/ℏ`.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling

open scoped Real


/-- **The classical hard-sphere van der Waals radius satisfies `R_a³ = α`** (Eq. 1): an atom modelled as a
point charge `q` in a uniform compensating sphere of radius `R_a`, in an applied field `𝓔`, has force
balance `q𝓔 = q²d/R_a³`; with the induced dipole `qd = α𝓔` this forces `R_a³ = α`, the classical exponent
`1/3`. -/
lemma classical_forceBalance_cube (q d Eext Ra α : ℝ)
    (hq : q ≠ 0) (hE : Eext ≠ 0) (hRa : Ra ≠ 0)
    (hbal : q * Eext = q ^ 2 * d / Ra ^ 3) (hdip : q * d = α * Eext) :
    Ra ^ 3 = α := by
  have hqE : q * Eext ≠ 0 := mul_ne_zero hq hE
  have h1 : q * Eext * Ra ^ 3 = q ^ 2 * d := by
    rw [hbal]; field_simp
  have h3 : q * Eext * Ra ^ 3 = q * Eext * α := by
    rw [h1, show q ^ 2 * d = q * (q * d) from by ring, hdip]; ring
  exact mul_left_cancel₀ hqE h3


/-- **The dispersion energy** `E_disp = −¾ α²ℏω/R⁶` (Eq. 4), with `A = α²ℏω`. -/
noncomputable def dispersionEnergy (A R : ℝ) : ℝ := -(3 / 4) * A / R ^ 6

/-- **The dispersion force** `F_disp = −9/2 α²ℏω/R⁷` (Eq. 4). -/
noncomputable def dispersionForce (A R : ℝ) : ℝ := -(9 / 2) * A / R ^ 7

/-- **`F_disp = −dE_disp/dR`, read as degree-`−6` homogeneity** `R·F_disp = 6 E_disp` (Eq. 4): the
`R⁷` power and `9/2` coefficient of the force are exactly `6/R` times the `R⁶` energy — the Euler relation
for the homogeneous `R⁻⁶` dispersion potential. -/
lemma dispersion_force_energy (A R : ℝ) (hR : R ≠ 0) :
    R * dispersionForce A R = 6 * dispersionEnergy A R := by
  unfold dispersionForce dispersionEnergy
  field_simp
  ring


/-- **The classical scaling exponent** `1/3` (Eq. 1). -/
noncomputable def classicalScalingExponent : ℝ := 1 / 3

/-- **The quantum (QDO) scaling exponent** `1/7` (Eq. 7): the central result of the paper. -/
noncomputable def qmScalingExponent : ℝ := 1 / 7

/-- **The quantum and classical exponents differ** `1/7 ≠ 1/3`: the QDO relation is markedly different
from the classical hard-sphere picture. -/
lemma qm_exponent_ne_classical : qmScalingExponent ≠ classicalScalingExponent := by
  unfold qmScalingExponent classicalScalingExponent; norm_num

/-- **The quantum van der Waals radius** `R_vdW(α) = C α^{1/7}` (Eq. 7); `C ≈ 2.54` a.u. is fitted to the
noble-gas reference data and kept here as a free constant. -/
noncomputable def qmVdWRadius (C α : ℝ) : ℝ := C * α ^ qmScalingExponent

/-- **The higher-multipole scaling exponent** `2/(7(n+1))` (Eq. 13): the QDO relation generalizes to the
multipole polarizability `α_n`, `R_vdW(α_n) = C_n α_n^{2/(7(n+1))}`. -/
noncomputable def multipoleVdWExponent (n : ℝ) : ℝ := 2 / (7 * (n + 1))

/-- **The dipole order `n = 1` recovers the `1/7` law** (Eq. 13 → Eq. 7): `2/(7·2) = 1/7`. -/
lemma multipoleVdWExponent_dipole : multipoleVdWExponent 1 = qmScalingExponent := by
  unfold multipoleVdWExponent qmScalingExponent; norm_num


/-- **The heteronuclear equilibrium distance** `D_a = 2C((α_A+α_B)/2)^{1/7}` (Eq. 9): the accurate
combination rule for a vdW-bonded dimer of atoms `A`, `B`, built from the arithmetic mean of their
polarizabilities. -/
noncomputable def equilibriumDistanceHetero (C αA αB : ℝ) : ℝ :=
  2 * C * ((αA + αB) / 2) ^ qmScalingExponent

/-- **The combination rule reduces to twice the radius for identical atoms**: `D_a(α,α) = 2 R_vdW(α)`,
the homonuclear equilibrium distance `D = 2 R_vdW` (Eq. 9 generalizes `D(α) ≡ 2 R_vdW`). -/
lemma equilibriumDistanceHetero_homonuclear (C α : ℝ) :
    equilibriumDistanceHetero C α α = 2 * qmVdWRadius C α := by
  unfold equilibriumDistanceHetero qmVdWRadius
  rw [show (α + α) / 2 = α from by ring]
  ring


/-- **The quantum Drude oscillator dipole polarizability** `α = q²/(μω²)`, expressed in the three QDO
parameters: the charge `q`, the mass `μ`, and the characteristic valence frequency `ω`. -/
noncomputable def qdoPolarizability (q μ ω : ℝ) : ℝ := q ^ 2 / (μ * ω ^ 2)

/-- **The QDO charge in terms of the polarizability** `q² = α μ ω²` — the substitution used to trade the
microscopic charge for the measurable polarizability throughout the derivation. -/
lemma qdoPolarizability_charge_sq (q μ ω : ℝ) (hμ : μ ≠ 0) (hω : ω ≠ 0) :
    qdoPolarizability q μ ω * (μ * ω ^ 2) = q ^ 2 := by
  unfold qdoPolarizability
  field_simp


/-- **The QDO exchange integral** `J_ex = q²/(2R)·e^{−μω R²/(2ℏ)}` (Eq. 2): with the Gaussian overlap
`S = e^{−μω R²/(2ℏ)}`, the Heitler–London exchange energy of two identical bosonic QDOs at separation
`R`. Here `w = μω` and `hbar = ℏ`. -/
noncomputable def exchangeIntegral (q w hbar R : ℝ) : ℝ :=
  q ^ 2 / 2 * (R⁻¹ * Real.exp (-(w / (2 * hbar)) * R ^ 2))

/-- **The exchange force is the exact negative gradient of `J_ex`** (Eq. 3):
`F_ex = −dJ_ex/dR = q²/2·e^{−μω R²/2ℏ}(1/R² + μω/ℏ)`. The paper's Eq. 3 is the large-`μω/ℏ` approximation
of this, dropping `1/R²` when `μω/ℏ ≫ 1/R²` (valid at `R = 2R_vdW`). -/
lemma exchangeIntegral_hasDerivAt (q w hbar R : ℝ) (hR : R ≠ 0) :
    HasDerivAt (fun r => exchangeIntegral q w hbar r)
      (-(q ^ 2 / 2) * Real.exp (-(w / (2 * hbar)) * R ^ 2) * ((R ^ 2)⁻¹ + w / hbar)) R := by
  have hp : HasDerivAt (fun r : ℝ => -(w / (2 * hbar)) * r ^ 2)
      (-(w / (2 * hbar)) * (2 * R)) R := by
    simpa using (hasDerivAt_pow 2 R).const_mul (-(w / (2 * hbar)))
  have hexp := hp.exp
  have hinv : HasDerivAt (fun r : ℝ => r⁻¹) (-(R ^ 2)⁻¹) R := hasDerivAt_inv hR
  have h := (hinv.mul hexp).const_mul (q ^ 2 / 2)
  exact h.congr_deriv (by field_simp; ring)


/-- **The scaling law in seventh-power form** `R_vdW⁷ = C⁷ α` (Eq. 5): the `α^{1/7}` law of Eq. 7 is
equivalently the statement that `R_vdW⁷` is proportional to the polarizability. -/
lemma qmVdWRadius_pow_seven (C α : ℝ) (hα : 0 ≤ α) :
    qmVdWRadius C α ^ 7 = C ^ 7 * α := by
  unfold qmVdWRadius qmScalingExponent
  rw [mul_pow, ← Real.rpow_natCast (α ^ (1 / 7 : ℝ)) 7, ← Real.rpow_mul hα]
  norm_num

/-- **The QDO proportionality function** `C(μω, R_vdW) = ½(3ℏ/μω)^{2/7} exp(2μω R_vdW²/(7ℏ))` (Eq. 6):
the force balance gives `R_vdW = C α^{1/7}` with this `C`, which (Table I) varies by under 9% among species
and is `≈ 2.54` (Eq. 7). Here `w = μω`, `hbar = ℏ`. -/
noncomputable def proportionalityC (w hbar RvdW : ℝ) : ℝ :=
  1 / 2 * (3 * hbar / w) ^ (2 / 7 : ℝ) * Real.exp (2 * w * RvdW ^ 2 / (7 * hbar))


/-- **Combination rule, arithmetic mean of radii** `D_a(R) = 2·(R_A+R_B)/2` (Eq. 10). -/
noncomputable def equilibriumDistanceRadiiArith (RA RB : ℝ) : ℝ := 2 * ((RA + RB) / 2)

/-- **Combination rule, geometric mean of polarizabilities** `D_g(α) = 2C(√(α_A α_B))^{1/7}` (Eq. 11). -/
noncomputable def equilibriumDistancePolGeom (C αA αB : ℝ) : ℝ :=
  2 * C * Real.sqrt (αA * αB) ^ qmScalingExponent

/-- **Combination rule, geometric mean of radii** `D_g(R) = 2√(R_A R_B)` (Eq. 12). -/
noncomputable def equilibriumDistanceRadiiGeom (RA RB : ℝ) : ℝ := 2 * Real.sqrt (RA * RB)

/-- All three combination rules agree for identical atoms: **arithmetic mean of radii** gives `2R`. -/
lemma equilibriumDistanceRadiiArith_homonuclear (R : ℝ) :
    equilibriumDistanceRadiiArith R R = 2 * R := by
  unfold equilibriumDistanceRadiiArith; ring

/-- **Geometric mean of polarizabilities** gives `2 R_vdW(α)` for identical atoms (`α ≥ 0`). -/
lemma equilibriumDistancePolGeom_homonuclear (C α : ℝ) (hα : 0 ≤ α) :
    equilibriumDistancePolGeom C α α = 2 * qmVdWRadius C α := by
  unfold equilibriumDistancePolGeom qmVdWRadius
  rw [Real.sqrt_mul_self hα]
  ring

/-- **Geometric mean of radii** gives `2R` for identical atoms (`R ≥ 0`). -/
lemma equilibriumDistanceRadiiGeom_homonuclear (R : ℝ) (hR : 0 ≤ R) :
    equilibriumDistanceRadiiGeom R R = 2 * R := by
  unfold equilibriumDistanceRadiiGeom
  rw [Real.sqrt_mul_self hR]


/-- **The Eq. 3 exchange force (large-`μω/ℏ` approximation)** `F_ex ≈ q²/2·(μω/ℏ)·e^{−μω R²/2ℏ}` — the
repulsive force from `exchangeIntegral_hasDerivAt` (§F) with the subdominant `1/R²` term dropped. Here
`w = μω`, `hbar = ℏ`. -/
noncomputable def exchangeForceApprox (q w hbar R : ℝ) : ℝ :=
  q ^ 2 / 2 * (w / hbar) * Real.exp (-(w / (2 * hbar)) * R ^ 2)

/-- **The exchange–dispersion force balance gives `R_vdW⁷ ∝ α`** — the physical link tying the exchange
force (§F), the dispersion force (§B) and the QDO polarizability (§E) to the `α^{1/7}` scaling (§C, §G).
At equilibrium the repulsion `F_ex` balances the attraction `−F_disp`; with `q² = α μ ω²`
(`qdoPolarizability_charge_sq`) this forces `μ²ω² R⁷ e^{−μω R²/2ℏ} = 9 ℏ² α`, i.e. `R_vdW⁷` is proportional
to `α` — the seventh-power form of `qmVdWRadius_pow_seven`. -/
lemma forceBalance_seventh_power
    (q μ ω hbar α R : ℝ) (hω : ω ≠ 0) (hℏ : hbar ≠ 0) (hR : R ≠ 0) (hα : α ≠ 0)
    (hq : q ^ 2 = α * (μ * ω ^ 2))
    (hbal : exchangeForceApprox q (μ * ω) hbar R = -dispersionForce (α ^ 2 * hbar * ω) R) :
    μ ^ 2 * ω ^ 2 * R ^ 7 * Real.exp (-(μ * ω / (2 * hbar)) * R ^ 2) = 9 * hbar ^ 2 * α := by
  unfold exchangeForceApprox dispersionForce at hbal
  rw [hq] at hbal
  field_simp [hR, hℏ, hα, hω] at hbal
  rw [show -(μ * ω / (2 * hbar)) * R ^ 2 = -(μ * ω * R ^ 2 / (2 * hbar)) from by ring]
  linear_combination hbal


open QuantumMechanics.OneDimension

/-- **The QDO polarizability of a charged PhysLib harmonic oscillator**: the quantum Drude oscillator is a
`QuantumMechanics.OneDimension.HarmonicOscillator` (mass `Q.m`, angular frequency `Q.ω`) carrying charge
`q`, and its dipole polarizability is `α = q²/(Q.m Q.ω²)` — the `qdoPolarizability` of §E evaluated on the
oscillator's own parameters. -/
noncomputable def qdoPolarizabilityOfHO (q : ℝ) (Q : HarmonicOscillator) : ℝ :=
  qdoPolarizability q Q.m Q.ω

/-- **The QDO polarizability is positive** for a nonzero charge — by the harmonic oscillator's positivity
of mass (`Q.hm`) and frequency (`Q.hω`), the vdW radius `R_vdW = C α^{1/7}` (§C) is well defined. -/
lemma qdoPolarizabilityOfHO_pos (q : ℝ) (hq : q ≠ 0) (Q : HarmonicOscillator) :
    0 < qdoPolarizabilityOfHO q Q := by
  have hm := Q.hm
  have hω := Q.hω
  unfold qdoPolarizabilityOfHO qdoPolarizability
  positivity

/-- **The charge–polarizability relation on the oscillator** `q² = α Q.m Q.ω²` — the QDO substitution
`qdoPolarizability_charge_sq` instantiated on the PhysLib harmonic oscillator, with the nonvanishing of
`Q.m`, `Q.ω` supplied by its positivity axioms. -/
lemma qdoPolarizabilityOfHO_charge_sq (q : ℝ) (Q : HarmonicOscillator) :
    qdoPolarizabilityOfHO q Q * (Q.m * Q.ω ^ 2) = q ^ 2 := by
  unfold qdoPolarizabilityOfHO
  exact qdoPolarizability_charge_sq q Q.m Q.ω (ne_of_gt Q.hm) (ne_of_gt Q.hω)


/-- **The polarizability of the inverted (unstable) oscillator** `α = q²/(μ·(−ω²))`: the harmonic
frequency is replaced by the inverted-oscillator continuation `ω² → −ω²` (`ω → iω`), the pseudo-Hermitian
inverted QHO of `OperatorAlgebra.InvertedOscillatorPseudoHermitian`. -/
noncomputable def qdoPolarizabilityInverted (q μ ω : ℝ) : ℝ := q ^ 2 / (μ * -(ω ^ 2))

/-- **Inversion flips the sign of the polarizability** `α_inv = −α`: the inverted (anti-binding) oscillator
has negative polarizability — the van der Waals counterpart of the inverted QHO `ω → iω`, whose energy
grows as `cosh(2κt)` (`OperatorAlgebra.InvertedOscillatorPseudoHermitian.invertedEnergyGrowth`) rather
than oscillating. -/
lemma qdoPolarizabilityInverted_eq_neg (q μ ω : ℝ) :
    qdoPolarizabilityInverted q μ ω = -qdoPolarizability q μ ω := by
  unfold qdoPolarizabilityInverted qdoPolarizability
  rw [mul_neg, div_neg]


open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-- **The QDO characteristic frequency is the de Broglie/Planck frequency of its energy quantum `ℏω`**:
`ω_dB(ℏω) = ω`. The harmonic-oscillator frequency `ω` of the Drude oscillator obeys the same
energy–frequency relation `ω = E/ℏ` as the electron's Compton clock, tying the vdW polarizability
oscillator to the Compton-clock frequency framework. -/
lemma qdoFrequency_eq_deBroglie_energyQuantum (ω ħ : ℝ) (hħ : ħ ≠ 0) :
    deBroglieFrequency (ħ * ω) ħ = ω := by
  unfold deBroglieFrequency
  field_simp

/-- **The Compton frequency is the de Broglie frequency of the rest energy `mc²`** — so the electron's
Compton clock `ω_C = mc²/ℏ`, its Zitterbewegung `2ω_C`
(`ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton`,
`ComptonClock.ElectronZitterbewegung`) and the Drude oscillator's `ω = ω_dB(ℏω)` all realize the single
relation `ω = E/ℏ`, the common frequency face shared by the vdW polarizability oscillator and the electron
Zitterbewegung oscillator. -/
lemma comptonFrequency_eq_deBroglie_restEnergy (m c ħ : ℝ) :
    comptonFrequency m c ħ = deBroglieFrequency (m * c ^ 2) ħ := rfl

end Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling

end
