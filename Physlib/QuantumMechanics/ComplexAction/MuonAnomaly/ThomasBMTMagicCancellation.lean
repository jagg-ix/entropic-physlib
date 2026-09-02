/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment
public import Physlib.Relativity.PauliMatrices.Basic
meta import Zil

/-!
# Thomas–BMT dynamics: the spin tune, the γ-independent anomaly frequency, and the magic
cancellation — the dynamical grounding of the operating point

The epistemic audit (`zil-epistemic-audit.md`) classified the magic-rapidity story as a
change of variables: `γ = √(1+1/a)` was a *definition* whose agreement with the storage ring was
algebraically forced. This module supplies the missing **dynamics** from the Thomas–Bargmann–
Michel–Telegdi equation, after which that same `γ` becomes a *derived cancellation condition* —
a statement with genuine failure modes:

* **§A the T-BMT precession rates.** The lab-frame spin precession rate
  `ω_s = (q/(γm))·((1+Gγ)B_⊥ + (1+G)B_∥)` (T-BMT, no electric field) and the cyclotron rate
  `ω_c = qB/(γm)`, as scalar carriers.
* **§B the spin tune and the γ-independent anomaly frequency.** `ω_s/ω_c − 1 = Gγ` (the spin
  tune), and the *reason storage rings can measure `a` at all*:
  `ω_a := ω_s − ω_c = G·(q/m)·B` — **the Lorentz factor cancels identically**. What the
  experiment measures is the anomaly as a frequency, before any reparameterization.
* **§C the magic cancellation.** With electric fields the anomaly precession acquires the term
  `(a − 1/(γ²−1))·(β×E)`; the coefficient `electricTermCoeff a γ` vanishes **iff**
  `γ² = 1 + 1/a` — and the *existing* operating-point carrier `AnomalyRapidity.gamma a` is
  exactly that zero (`electricTermCoeff_vanishes_at_gamma`). At the magic point the measured
  frequency is pure anomaly for **any** electric field: `ω_a = (q/m)·a·B`
  (`magic_operating_point`). The claim in `gamma`'s docstring ("the Lorentz factor at which the
  electric-field spin precession cancels") is here proven, not asserted.

**Epistemic status (per the audit's discipline):** §B–§C are Class-D content — the γ-cancellation
in `anomalyFrequency_gamma_independent` and the iff of `electricTerm_vanishes_iff_magic` are
computations that could have failed; the *shape* of the electric coefficient is the T-BMT
structure, encoded here as the definition `tbmtOmegaA` (the residual Class-C ansatz: this module
takes the T-BMT force law itself as given, per BMT 1959, not derived from QED).

## References

* V. Bargmann, L. Michel, V. L. Telegdi, Phys. Rev. Lett. 2 (1959) 435. L. H. Thomas 1927.
* J. D. Jackson, *Classical Electrodynamics*, §11.11 (the `a − 1/(γ²−1)` electric term).
* F. A. Asenjo, B. Koch, arXiv:2309.16216 — extended BMT equations and the anomalous-moment
  observable (the generalization target for a future arc).
* “Approaches to Solving the T-BMT Equation” (accelerator homework): the ring-frame reduction,
  spin tune `Gγ`, spinor/Hopf transcription.
* Repo carriers: `AnomalyRapidity.gamma`/`gamma_anomaly`/`fermilabMagicGamma`,
  `Hopf.FibrationSpinorMap.hopfBase` (for the future spinor face).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation

/-! ## A. The T-BMT precession rates -/

/-- **The T-BMT spin precession rate** (lab frame, magnetic only):
`ω_s = (q/(γm))·((1+Gγ)B_⊥ + (1+G)B_∥)` — the Thomas–BMT rate for anomalous gyromagnetic ratio
`G`, Lorentz factor `γ`, perpendicular/parallel magnetic components. -/
noncomputable def tbmtSpinRate (q m γ G Bperp Bpar : ℝ) : ℝ :=
  q / (γ * m) * ((1 + G * γ) * Bperp + (1 + G) * Bpar)

/-- **The cyclotron rate** `ω_c = qB/(γm)` — the momentum-rotation frequency in the same field. -/
noncomputable def cyclotronRate (q m γ B : ℝ) : ℝ := q * B / (γ * m)

/-- **The anomaly precession rate with an electric field** (one-component shadow of the standard
T-BMT result, Jackson §11.11): `ω_a = (q/m)·(a·B − (a − 1/(γ²−1))·βE)`, where `βE` stands for the
relevant `(β×E)/c` component. The electric term's coefficient is the object of §C. -/
noncomputable def tbmtOmegaA (q m a γ B βE : ℝ) : ℝ :=
  q / m * (a * B - (a - 1 / (γ ^ 2 - 1)) * βE)

/-- **The electric-term coefficient** `a − 1/(γ²−1)` — what multiplies `β×E` in the anomaly
precession. Its zero is the magic operating point. -/
noncomputable def electricTermCoeff (a γ : ℝ) : ℝ := a - 1 / (γ ^ 2 - 1)

/-! ## B. The spin tune and the γ-independent anomaly frequency -/

/-- **[The spin tune is `Gγ`]** `ω_s/ω_c − 1 = Gγ` for a purely perpendicular field: per orbit
turn, the spin advances `Gγ` extra revolutions — the accelerator's spin tune, the quantity the
resonance machinery of the T-BMT homework is built around. -/
theorem spinTune_eq_G_mul_gamma (q m γ G B : ℝ)
    (hq : q ≠ 0) (hm : m ≠ 0) (hγ : γ ≠ 0) (hB : B ≠ 0) :
    tbmtSpinRate q m γ G B 0 / cyclotronRate q m γ B - 1 = G * γ := by
  unfold tbmtSpinRate cyclotronRate
  field_simp
  ring

/-- **[The anomaly frequency is γ-independent]** `ω_s − ω_c = G·(q/m)·B`. The Lorentz factors
cancel **identically** between the spin and cyclotron rates — the dynamical reason a storage ring
measures the anomaly `G` directly as a frequency difference, at any energy: what Fermilab's `ω_a`
*is*, derived from the T-BMT structure before any reparameterization of `G`. -/
theorem anomalyFrequency_gamma_independent (q m γ G B : ℝ) (hm : m ≠ 0) (hγ : γ ≠ 0) :
    tbmtSpinRate q m γ G B 0 - cyclotronRate q m γ B = G * (q / m) * B := by
  unfold tbmtSpinRate cyclotronRate
  field_simp
  ring

/-! ## C. The magic cancellation -/

/-- **[The electric term vanishes iff the Lorentz factor is magic]**
`a − 1/(γ²−1) = 0 ↔ γ² = 1 + 1/a`. The right-hand side is a *derived zero-condition of the
dynamics*, not a definition: the coefficient's shape comes from the T-BMT equation, and the iff
could have failed. -/
theorem electricTerm_vanishes_iff_magic (a γ : ℝ) (ha : a ≠ 0) (hγ : γ ^ 2 ≠ 1) :
    electricTermCoeff a γ = 0 ↔ γ ^ 2 = 1 + 1 / a := by
  unfold electricTermCoeff
  rw [sub_eq_zero]
  constructor
  · intro h
    have hγ1 : γ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hγ
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    rw [h]
    have h1 : 1 + 1 / a - 1 = 1 / a := by ring
    rw [h1, one_div_one_div]

/-- **[The existing operating-point carrier is the zero of the electric term]**
`electricTermCoeff a (gamma a) = 0` for `a > 0`. The `AnomalyRapidity.gamma` definition — whose
docstring *claims* the electric-field cancellation — here earns that claim as a theorem: it is
exactly the magic zero of the T-BMT electric coefficient. This upgrades the operating-point story
from a change of variables to a derived cancellation condition. -/
theorem electricTermCoeff_vanishes_at_gamma (a : ℝ) (ha : 0 < a) :
    electricTermCoeff a (gamma a) = 0 := by
  have hsq : gamma a ^ 2 = 1 + 1 / a := by
    unfold gamma
    rw [Real.sq_sqrt (by positivity)]
  rw [(electricTerm_vanishes_iff_magic a (gamma a) ha.ne' (by
    rw [hsq]
    have : 1 / a > 0 := by positivity
    linarith)).mpr hsq]

/-- **[At the magic point the measured frequency is pure anomaly, for any electric field]**
`ω_a(γ = gamma a) = (q/m)·a·B` — the electric term drops **identically in `βE`**: the storage
ring at the magic Lorentz factor measures `a` as a clean frequency regardless of the electric
environment. This is the dynamical statement the experiment is built on, with
`fermilabMagicGamma ≈ 29.3` the numerical instance. -/
theorem magic_operating_point (q m a B βE : ℝ) (ha : 0 < a) :
    tbmtOmegaA q m a (gamma a) B βE = q / m * (a * B) := by
  unfold tbmtOmegaA
  have h := electricTermCoeff_vanishes_at_gamma a ha
  unfold electricTermCoeff at h
  rw [h]
  ring

/-! ## D. The rest-frame force law from the Dirac–Pauli Hamiltonian — the QED grounding

The contract previously declared the T-BMT force law "taken as given, not derived from QED". The
required carriers exist, so the boundary moves: the **rest-frame** content of the force law is here
derived from the quantum magnetic-dipole Hamiltonian by the Heisenberg equation of motion on the
*proven* Pauli commutators (`σ1_σ3_commutator`), with the coupling `g = gFactor G = 2(1+G)` from
the first-quantized-QED arc and `G = schwingerAnomaly α = α/2π` the QED one-loop value. What
remains declaredly underived: the covariant boost/Thomas extension (the `(1+Gγ)` vs `(1+G)`
splitting — the Asenjo–Koch constraint arc) and the loop computation of `F₂` itself. -/

section QEDGrounding

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment
open PauliMatrix Complex
open scoped PauliMatrix

/-- **The magnetic-dipole Hamiltonian** for a vertical field `B` (the ring geometry):
`H = −(g/2)·(qℏ/(2m))·B·σ₃` — the spin part of the Dirac–Pauli Hamiltonian in the rest frame,
with the full `g`-factor (Dirac `2` plus anomaly) as coupling. -/
noncomputable def dipoleHamiltonianZ (g q m ℏ B : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((-(g * q * ℏ * B / (4 * m)) : ℝ) : ℂ) • σ3

/-- **[Heisenberg precession from the proven Pauli commutator]**
`(i/ℏ)[H, σ₁] = (gqB/(2m))·σ₂` — the Heisenberg equation of motion for the transverse spin
component under the dipole Hamiltonian gives rotation at `ω = gqB/(2m)`: the **rest-frame spin
precession law derived from quantum mechanics**, the commutator `[σ₃,σ₁] = 2i·σ₂` doing the
physics (Physlib `σ1_σ3_commutator`, a proven matrix theorem — this could fail and doesn't). -/
theorem heisenberg_precession_of_dipole (g q m ℏ B : ℝ) (hℏ : ℏ ≠ 0) :
    (Complex.I / (ℏ : ℂ)) •
        (dipoleHamiltonianZ g q m ℏ B * σ1 - σ1 * dipoleHamiltonianZ g q m ℏ B)
      = ((g * q * B / (2 * m) : ℝ) : ℂ) • σ2 := by
  have hcomm : σ3 * σ1 - σ1 * σ3 = (2 * I) • σ2 :=
    calc σ3 * σ1 - σ1 * σ3 = -(σ1 * σ3 - σ3 * σ1) := by rw [neg_sub]
      _ = -(-(2 * I) • σ2) := by rw [σ1_σ3_commutator]
      _ = (2 * I) • σ2 := by rw [neg_smul, neg_neg]
  unfold dipoleHamiltonianZ
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, hcomm, smul_smul, smul_smul]
  congr 1
  have hℏc : (ℏ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **[The T-BMT rate at rest is the Dirac–Pauli precession]**
`tbmtSpinRate(γ = 1) = gFactor(G)·qB/(2m)`. The classical force-law carrier of §A, evaluated in
the rest frame, coincides exactly with the quantum Heisenberg rate at the full `g = 2(1+G)`: the
rest-frame content of the T-BMT force law is *grounded in* the Dirac–Pauli Hamiltonian, not
postulated beside it. -/
theorem tbmtSpinRate_rest_eq_diracPauli (q m G B : ℝ) :
    tbmtSpinRate q m 1 G B 0 = gFactor G * q * B / (2 * m) := by
  unfold tbmtSpinRate
  rw [gFactor]
  ring

/-- **[The QED chain closes: `α → a → g → magic point → clean frequency`]** with the one-loop QED
coupling `G = schwingerAnomaly α = α/2π`: the rest-frame rate carries the QED `g`-factor, and at
the magic Lorentz factor the measured frequency is the pure QED anomaly times `qB/m` for any
electric field. The force law's coupling, operating point, and output frequency are all fixed by
the QED input. -/
theorem qed_forceLaw_chain (q m B βE α : ℝ) (hα : 0 < α) :
    tbmtSpinRate q m 1 (schwingerAnomaly α) B 0
        = gFactor (schwingerAnomaly α) * q * B / (2 * m)
      ∧ tbmtOmegaA q m (schwingerAnomaly α) (gamma (schwingerAnomaly α)) B βE
        = q / m * (schwingerAnomaly α * B) :=
  ⟨tbmtSpinRate_rest_eq_diracPauli q m (schwingerAnomaly α) B,
    magic_operating_point q m (schwingerAnomaly α) B βE (schwingerAnomaly_pos α hα)⟩

end QEDGrounding

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach spinTune_eq_G_mul_gamma where
  formalizes @ "claim:tbmt-spin-tune-is-anomaly-times-gamma",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  caveat @ "claim:scalar-rate-shadow-of-the-vector-tbmt-equation"

zil_theorem_intent anomalyFrequency_gamma_independent where
  at_level bridge_theorem
  must_mention [tbmtSpinRate, cyclotronRate]

zil attach anomalyFrequency_gamma_independent where
  formalizes @ "claim:anomaly-frequency-is-gamma-independent-g-times-qb-over-m",
  requires @ "claim:tbmt-spin-tune-is-anomaly-times-gamma",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  supported_by @ "measurement:fermilab-muon-g-2-final-2025",
  caveat @ "claim:tbmt-force-law-taken-as-given-not-derived-from-qed"

zil_theorem_intent electricTerm_vanishes_iff_magic where
  at_level bridge_theorem
  must_mention [electricTermCoeff]

zil attach electricTerm_vanishes_iff_magic where
  formalizes @ "claim:magic-gamma-derived-as-electric-term-cancellation-of-tbmt",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  supported_by @ "paper:asenjo-koch-2309-16216",
  caveat @ "claim:one-component-shadow-of-the-beta-cross-e-term"

zil attach electricTermCoeff_vanishes_at_gamma where
  formalizes @ "claim:existing-operating-point-gamma-is-the-magic-zero-of-tbmt-dynamics",
  requires @ "claim:magic-gamma-derived-as-electric-term-cancellation-of-tbmt",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  caveat @ "claim:upgrades-the-audited-change-of-variables-to-a-derived-cancellation-not-yet-entanglement-evidence"

zil attach magic_operating_point where
  formalizes @ "claim:at-magic-gamma-the-measured-frequency-is-pure-anomaly-for-any-electric-field",
  requires @ "claim:existing-operating-point-gamma-is-the-magic-zero-of-tbmt-dynamics",
  requires @ "claim:anomaly-frequency-is-gamma-independent-g-times-qb-over-m",
  supported_by @ "measurement:fermilab-bnl-magic-momentum-3.094-gev-over-c-and-gamma-29.3",
  caveat @ "claim:frequency-to-a-mu-extraction-still-imports-external-ratios-omega-p-mu-mass"

zil_theorem_intent heisenberg_precession_of_dipole where
  at_level bridge_theorem
  must_mention [dipoleHamiltonianZ]

zil attach heisenberg_precession_of_dipole where
  formalizes @ "claim:rest-frame-spin-precession-from-dirac-pauli-heisenberg-commutator",
  supported_by @ "paper:dirac-1928-pauli-term",
  caveat @ "claim:vertical-field-two-by-two-shadow-of-the-full-dirac-hamiltonian"

zil attach tbmtSpinRate_rest_eq_diracPauli where
  formalizes @ "claim:tbmt-rest-frame-rate-is-the-dirac-pauli-g-factor-precession",
  requires @ "claim:rest-frame-spin-precession-from-dirac-pauli-heisenberg-commutator",
  supported_by @ "paper:bargmann-michel-telegdi-1959",
  caveat @ "claim:boost-thomas-extension-one-plus-g-gamma-splitting-remains-underived"

zil attach qed_forceLaw_chain where
  formalizes @ "claim:qed-alpha-fixes-coupling-operating-point-and-output-frequency-of-the-force-law",
  requires @ "claim:tbmt-rest-frame-rate-is-the-dirac-pauli-g-factor-precession",
  requires @ "claim:at-magic-gamma-the-measured-frequency-is-pure-anomaly-for-any-electric-field",
  supported_by @ "paper:schwinger-1948",
  caveat @ "claim:one-loop-value-imported-as-schwinger-anomaly-loop-integral-not-formalized"

zil_file_contract physlib.thomasBMTMagicCancellation where
  promises "The dynamical grounding of the storage-ring operating point from the Thomas-BMT structure: the spin tune is G gamma, the anomaly frequency omega_s minus omega_c is gamma-independent and equal to G q B over m (what the ring measures), the electric-term coefficient a minus one over gamma squared minus one vanishes exactly at gamma squared equal one plus one over a, the existing operating-point carrier gamma of AnomalyRapidity is that magic zero, and at the magic point the measured frequency is pure anomaly for any electric field."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.gamma",
    "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity.fermilabMagicGamma"]
  forbids_substitutes ["the covariant boost/Thomas extension of the rest-frame Heisenberg law, which remains underived",
    "the loop computation of F2 itself, imported as the Schwinger value",
    "entanglement or Schmidt-number evidence claimed from the dynamical cancellation",
    "the full vector T-BMT equation or Frenet-Serret ring frame, deferred to the spinor-face arc"]
  witnessed_by [spinTune_eq_G_mul_gamma, anomalyFrequency_gamma_independent,
    electricTerm_vanishes_iff_magic, electricTermCoeff_vanishes_at_gamma, magic_operating_point,
    heisenberg_precession_of_dipole, tbmtSpinRate_rest_eq_diracPauli, qed_forceLaw_chain]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation

end
