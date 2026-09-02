/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaTransitionLocalEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaComplexCanonicalBornProduct
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# Merging the Ipek–Caticha arc with the complex Schrödinger functional and the Nagao–Nielsen complex contour

Links the Ipek–Caticha coupled-gravity entropic dynamics (arXiv:2006.05036) to two established structures of the
repository: the **linear complex Schrödinger flow** (`HamiltonKillingComplexStructureSchrodinger`, Caticha's
Hamilton–Killing derivation) and the **Nagao–Nielsen complex action / contour**
(`EntropicDynamicsComplexActionNagaoNielsen`, `e^{iS_R/ℏ − S_I/ℏ}`). The two links pin down exactly *where*
gravity enters and *what* the local clock does.

* **the flat generator is the linear Schrödinger operator** (`flatGeneratorLM`, `flatGenerator_superposition`): the
  fixed-background Ipek–Caticha generator `𝓛₀(ψ) = E·ψ` is the `ℂ`-linear map `E·id`, so it superposes *by* the
  repository's `schrodinger_superposition` — flat entropic dynamics *is* the linear Schrödinger flow;
* **gravity breaks exactly that linearity** (`flat_linear_gravity_nonlinear`): the gravity-coupled generator
  violates the very superposition that `schrodinger_superposition` guarantees for the linear flow — the
  Ipek–Caticha prediction located precisely against the Hamilton–Killing linear Schrödinger operator;
* **the local entropic time is the Nagao–Nielsen `ℏ`** (`localClock_transition_is_entropyDamping`): the
  local-clock transition weight (`α = 1/δξ⊥`) is the Nagao–Nielsen entropy damping `e^{−S_I/ℏ}` with
  `ℏ = 2δξ⊥` — the local proper time *is* the effective `ℏ` of the complex-action contour, so the transition sits
  on the `kuikenWeight` hub with a position-dependent `ℏ`;
* **the conjugate wave function is the reversed contour phase** (`edWaveFunction_conj_is_nn_antiphase`):
  `Ψ* = \overline{Ψ}` at unit amplitude is `e^{−iθ}`, the anti-phase `e^{−iS_R/ℏ}` of the Nagao–Nielsen weight — the
  `Ψ*` canonical variable is the reversed complex-action contour.

So the Ipek–Caticha arc connects cleanly: its flat generator is the Hamilton–Killing linear Schrödinger operator
(superposition), its gravity coupling is the nonlinear departure from it, its local entropic time is the effective
`ℏ = 2δξ⊥` of the Nagao–Nielsen complex action, and its `(Ψ, Ψ*)` variables are the forward/reversed contours of
`e^{iS_R/ℏ − S_I/ℏ}`.

* **§A — the complex Schrödinger functional** (`flatGeneratorLM`, `flatGenerator_superposition`,
  `flat_linear_gravity_nonlinear`).
* **§B — the Nagao–Nielsen complex contour** (`localClock_transition_is_entropyDamping`,
  `edWaveFunction_conj_is_nn_antiphase`, `ipekCaticha_on_nagaoNielsen_contour`).
* **§C — the normalized infinite-mode solution on that spine**
  (`perepelkinMode_nonHermitian_nagaoNielsen_caticha`,
  `normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain`): each theta coefficient is the
  zero-imaginary-energy specialization of the non-Hermitian evolution factor, hence a Nagao–Nielsen
  complex-action weight; its energy operator is Caticha's flat linear generator; and the full packet's
  unit Born mass feeds Caticha's entropic wave-function reconstruction pointwise.

**Honest layering.** The linear-map representation, the superposition/violation dichotomy, the local-`ℏ` identity,
and the reversed-contour phase are exact algebra, reusing `schrodinger_superposition`,
`gravGenerator_superposition_violation`, `ed_transition_is_entropyDamping`,
`ed_wavefunction_phase_is_complexAction_phase`, and `edWaveFunction_conj`. ## References

* S. Ipek, A. Caticha, arXiv:2006.05036; A. Caticha (Hamilton–Killing); K. Nagao, H.B. Nielsen (complex action).
  Repo carriers: `EntropicTime.HamiltonKillingComplexStructureSchrodinger` (`schrodinger_superposition`),
  `EntropicTime.EntropicDynamicsComplexActionNagaoNielsen` (`ed_transition_is_entropyDamping`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSuperpositionViolation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaTransitionLocalEntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaComplexCanonicalBornProduct
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsComplexActionNagaoNielsen
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
open Physlib.QFT.Wick.Consistency

/- ZIL-BEGIN -/
open Zil
/- ZIL-END -/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen


/-- **The flat generator as a `ℂ`-linear map** `𝓛₀ = E·id` — the fixed-background Ipek–Caticha Schrödinger
generator represented as the `ℂ`-linear operator `E·id` on `ℂ`, the Hamilton–Killing linear Schrödinger
Hamiltonian. -/
noncomputable def flatGeneratorLM (E : ℝ) : ℂ →ₗ[ℂ] ℂ := (E : ℂ) • LinearMap.id

/-- **[The linear map is the flat generator] `𝓛₀ = E·(·)`.** -/
lemma flatGeneratorLM_apply (E : ℝ) (ψ : ℂ) : flatGeneratorLM E ψ = flatGenerator E ψ := by
  simp only [flatGeneratorLM, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul,
    flatGenerator]

/-- **[The flat entropic-dynamics generator superposes, via the Hamilton–Killing linear Schrödinger flow].** The
fixed-background generator is `ℂ`-linear, so `𝓛₀(c₁ψ₁ + c₂ψ₂) = c₁𝓛₀ψ₁ + c₂𝓛₀ψ₂` follows from the repository's
`schrodinger_superposition` — flat entropic dynamics is the linear Schrödinger flow. -/
lemma flatGenerator_superposition (E : ℝ) (c₁ c₂ ψ₁ ψ₂ : ℂ) :
    flatGenerator E (c₁ • ψ₁ + c₂ • ψ₂) = c₁ • flatGenerator E ψ₁ + c₂ • flatGenerator E ψ₂ := by
  simp only [← flatGeneratorLM_apply]
  exact schrodinger_superposition (flatGeneratorLM E) c₁ c₂ ψ₁ ψ₂

/-- **[Flat linear Schrödinger, gravity nonlinear].** The combined result: the flat generator superposes exactly
as the Hamilton–Killing linear Schrödinger operator (`schrodinger_superposition`), while the gravity-coupled
generator violates that superposition (`gravGenerator_superposition_violation`) — gravity is precisely the
nonlinear departure from the linear Schrödinger flow. -/
lemma flat_linear_gravity_nonlinear (E lam : ℝ) (hlam : lam ≠ 0) :
    (∀ c₁ c₂ ψ₁ ψ₂ : ℂ, flatGenerator E (c₁ • ψ₁ + c₂ • ψ₂)
        = c₁ • flatGenerator E ψ₁ + c₂ • flatGenerator E ψ₂)
      ∧ (∃ ψ₁ ψ₂ : ℂ, gravGenerator E lam (ψ₁ + ψ₂)
        ≠ gravGenerator E lam ψ₁ + gravGenerator E lam ψ₂) :=
  ⟨fun c₁ c₂ ψ₁ ψ₂ => flatGenerator_superposition E c₁ c₂ ψ₁ ψ₂,
   gravGenerator_superposition_violation E lam hlam⟩


/-- **[The local entropic time is the Nagao–Nielsen `ℏ`] `P = e^{−S_I/(2δξ⊥)}`.** With the local-clock multiplier
`α = 1/δξ⊥`, the transition weight is the Nagao–Nielsen entropy damping `e^{−S_I/ℏ}` with imaginary action
`S_I = (Δχ−b)²` and effective `ℏ = 2δξ⊥` — the local proper time is the `ℏ` of the complex-action contour. -/
lemma localClock_transition_is_entropyDamping (δξ b Δχ : ℝ) (hδξ : δξ ≠ 0) :
    edTransitionWeight (entropicTimeMultiplier δξ) b Δχ = entropyDamping ((Δχ - b) ^ 2) (2 * δξ) := by
  have hα : entropicTimeMultiplier δξ ≠ 0 := by
    unfold entropicTimeMultiplier; exact one_div_ne_zero hδξ
  rw [ed_transition_is_entropyDamping (entropicTimeMultiplier δξ) b Δχ hα]
  congr 1
  unfold entropicTimeMultiplier
  field_simp

/-- **[The conjugate wave function is the reversed Nagao–Nielsen contour] `Ψ* = e^{−iθ}`.** At unit amplitude the
conjugate wave function `Ψ* = \overline{Ψ}` is the anti-phase `e^{−iθ} = e^{−iS_R/ℏ}` — the `Ψ*` canonical variable
is the reversed complex-action contour of the Nagao–Nielsen weight. -/
lemma edWaveFunction_conj_is_nn_antiphase (θ : ℝ) :
    (starRingEnd ℂ) (edWaveFunction 1 θ) = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [edWaveFunction_conj, ed_wavefunction_phase_is_complexAction_phase]

/-- **[The Ipek–Caticha arc on the Nagao–Nielsen contour, assembled].** The local-clock transition is the entropy
damping with `ℏ = 2δξ⊥`, and the conjugate wave function is the reversed contour phase — the coupled-gravity
entropic dynamics on the complex-action contour. -/
lemma ipekCaticha_on_nagaoNielsen_contour (δξ b Δχ θ : ℝ) (hδξ : δξ ≠ 0) :
    (edTransitionWeight (entropicTimeMultiplier δξ) b Δχ = entropyDamping ((Δχ - b) ^ 2) (2 * δξ))
      ∧ ((starRingEnd ℂ) (edWaveFunction 1 θ) = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) :=
  ⟨localClock_transition_is_entropyDamping δξ b Δχ hδξ, edWaveFunction_conj_is_nn_antiphase θ⟩

/-! ## C. The normalized infinite-mode solution on the Caticha--Nagao--Nielsen spine -/

/-- Every half-integer coefficient of the normalized Perepelkin theta packet lies on the existing
Caticha--Nagao--Nielsen spine:

* it is the `E_I = 0` specialization of the non-Hermitian evolution factor;
* it satisfies the corresponding modewise non-Hermitian Schrödinger equation;
* that evolution factor is exactly the Nagao--Nielsen complex-action weight with zero imaginary action;
* the same real mode energy acts through Caticha's flat complex-linear generator.

This theorem introduces no second evolution or Hamiltonian.  It composes the spectral, non-Hermitian,
complex-action, and entropic-dynamics interfaces already present in the repository. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.perepelkin.modeNonHermitianNagaoNielsenCaticha,
  zil_concept physics.entropicDynamicsComplexActionSchrodinger,
  zil_requires assumptions.nonzeroHbarMassWellWidth,
  zil_level bridge_theorem, zil_export]
/- ZIL-END -/
lemma perepelkinMode_nonHermitian_nagaoNielsen_caticha
    {hbar mass width : ℝ} (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hwidth : width ≠ 0)
    (mu : ℕ) (beta t : ℝ) (n : ℤ) :
    let E := perepelkinModeEnergy hbar mass width mu n
    let amplitude := perepelkinSpectralAmplitude hbar mass width mu beta
    amplitude t n = evolutionFactor E 0 hbar t * amplitude 0 n
      ∧ HasDerivAt (fun s : ℝ => amplitude s n)
          (((E : ℝ) : ℂ) / (Complex.I * hbar) * amplitude t n) t
      ∧ evolutionFactor E 0 hbar t = complexActionWeight (-(E * t)) 0 hbar
      ∧ flatGeneratorLM E (amplitude t n) = (E : ℂ) * amplitude t n := by
  dsimp only
  refine ⟨?_, hasDerivAt_perepelkinSpectralAmplitude hhbar hmass hwidth mu beta t n,
    ?_, ?_⟩
  · simpa [spectralPhase, evolutionFactor_at_H_I_zero] using
      perepelkinSpectralAmplitude_eq_spectralPhase hhbar hmass hwidth mu beta t n
  · simpa using evolutionFactor_eq_complexActionWeight
      (perepelkinModeEnergy hbar mass width mu n) 0 hbar t
  · rw [flatGeneratorLM_apply]
    rfl

/-- The complete normalized bridge.  The full infinite-mode packet has unit Born mass; its
pointwise Born density is therefore a valid input to Caticha's entropic wave-function reconstruction;
and every spectral coefficient simultaneously realizes the zero-damping non-Hermitian equation,
Nagao--Nielsen complex-action phase, and Caticha flat linear generator described above. -/
/- ZIL-BEGIN -/
@[zil_claim physlib.perepelkin.normalizedNonHermitianNagaoNielsenCatichaChain,
  zil_concept physics.entropicDynamicsComplexActionSchrodinger,
  zil_requires assumptions.positivePerepelkinPhysicalParameters,
  zil_level bridge_theorem, zil_export]
/- ZIL-END -/
lemma normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain
    {hbar mass width : ℝ} (hhbar : hbar ≠ 0) (hmass : 0 < mass) (hwidth : 0 < width)
    {mu : ℕ} (hmu : 0 < mu) {beta : ℝ} (hbeta : 0 < beta) (t Phi : ℝ) :
    (∫ x in (0 : ℝ)..width,
      (Complex.normSq (perepelkinWaveFunction hbar mass width mu beta x t) : ℂ)) = 1
      ∧ (∀ x : ℝ,
        ‖edWaveFunction
            (Complex.normSq (perepelkinWaveFunction hbar mass width mu beta x t)) Phi‖ ^ 2 =
          Complex.normSq (perepelkinWaveFunction hbar mass width mu beta x t))
      ∧ (∀ n : ℤ,
        let E := perepelkinModeEnergy hbar mass width mu n
        let amplitude := perepelkinSpectralAmplitude hbar mass width mu beta
        amplitude t n = evolutionFactor E 0 hbar t * amplitude 0 n
          ∧ HasDerivAt (fun s : ℝ => amplitude s n)
              (((E : ℝ) : ℂ) / (Complex.I * hbar) * amplitude t n) t
          ∧ evolutionFactor E 0 hbar t = complexActionWeight (-(E * t)) 0 hbar
          ∧ flatGeneratorLM E (amplitude t n) = (E : ℂ) * amplitude t n) := by
  refine ⟨integral_normSq_perepelkinWaveFunction hbar mass hwidth hmu hbeta t, ?_, ?_⟩
  · intro x
    exact hamiltonKilling_born_rule
      (Complex.normSq (perepelkinWaveFunction hbar mass width mu beta x t)) Phi
      (Complex.normSq_nonneg _)
  · intro n
    exact perepelkinMode_nonHermitian_nagaoNielsen_caticha
      hhbar hmass.ne' hwidth.ne' mu beta t n

/- ZIL-BEGIN -/

zil attach perepelkinMode_nonHermitian_nagaoNielsen_caticha where
  formalizes @ "claim:perepelkin-mode-is-zero-imaginary-energy-nonhermitian-schrodinger-complex-action-caticha-flow",
  requires @ "assumption:nonzero-hbar-mass-and-well-width",
  requires @ "claim:perepelkin-half-integer-mode-spectral-evolution",
  supported_by @ "paper:perepelkin-2112.15212",
  supported_by @ "paper:nagao-nielsen-complex-action",
  supported_by @ "paper:caticha-hamilton-killing-schrodinger",
  caveat @ "claim:zero-imaginary-energy-specialization-has-no-nonhermitian-damping"

zil attach normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain where
  formalizes @ "claim:normalized-infinite-mode-schrodinger-links-nonhermitian-nagao-nielsen-caticha-entropic-dynamics",
  requires @ "assumption:positive-mass-width-mode-and-thermal-parameter",
  requires @ "claim:perepelkin-wavefunction-unit-born-normalization",
  requires @ "claim:caticha-entropic-wavefunction-born-reconstruction",
  requires @ "claim:perepelkin-mode-is-zero-imaginary-energy-nonhermitian-schrodinger-complex-action-caticha-flow",
  supported_by @ "paper:perepelkin-2112.15212",
  supported_by @ "paper:ipek-abedi-caticha-2018",
  supported_by @ "paper:nagao-nielsen-complex-action",
  caveat @ "claim:modewise-time-derivative-not-a-new-proof-of-the-summed-spatial-pde",
  caveat @ "claim:caticha-reconstruction-matches-born-density-not-a-claimed-pointwise-phase-identification"

zil_theorem_intent perepelkinMode_nonHermitian_nagaoNielsen_caticha where
  at_level bridge_theorem
  must_mention [perepelkinSpectralAmplitude, perepelkinModeEnergy,
    evolutionFactor, complexActionWeight, flatGeneratorLM]

zil_theorem_intent normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain where
  at_level bridge_theorem
  must_mention [perepelkinWaveFunction, perepelkinSpectralAmplitude,
    perepelkinModeEnergy, evolutionFactor, complexActionWeight,
    flatGeneratorLM, edWaveFunction]

#zil_validate_embedded normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain where
  no_sorry, claim_linked, requirement_linked

zil_file_contract physlib.normalizedPerepelkinCatichaNagaoNielsen where
  promises "The normalized infinite Perepelkin theta packet is linked, without a duplicate evolution law, to the zero-imaginary-energy non-Hermitian Schrodinger factor, its Nagao-Nielsen complex-action weight, Caticha's flat linear energy generator, and Caticha's pointwise Born-density wave-function reconstruction."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.integral_normSq_perepelkinWaveFunction",
    "lean:Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.hasDerivAt_perepelkinSpectralAmplitude",
    "lean:Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.perepelkinSpectralAmplitude_eq_spectralPhase",
    "lean:Physlib.QuantumMechanics.NonHermitian.WickRotation.evolutionFactor_at_H_I_zero",
    "lean:Physlib.QuantumMechanics.NonHermitian.WickRotation.evolutionFactor_eq_complexActionWeight",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger.hamiltonKilling_born_rule",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen.flatGeneratorLM_apply"
  ]
  forbids_substitutes [
    "claiming nonzero imaginary energy or dissipative evolution for the normalized unitary packet",
    "claiming that pointwise Born-density reconstruction identifies the packet's Caticha phase",
    "promoting the coefficientwise time ODE to an independently proved summed spatial Schrodinger PDE"
  ]
  witnessed_by [perepelkinMode_nonHermitian_nagaoNielsen_caticha,
    normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain]

#zil_formalization_lint physlib.normalizedPerepelkinCatichaNagaoNielsen

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen

end
