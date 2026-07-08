/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Thermodynamics.SecondLaw
public import Physlib.QuantumMechanics.Clock.HarmonicOscillatorPhaseClock
public import Physlib.QFT.Wick.Consistency
public import Physlib.QuantumMechanics.NonHermitian.WickRotation
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Entropic twin paradox: path-dependent entropic time and interference

Where the geometric twin paradox treats two worldlines under real proper time,
this module treats the **entropic twin
paradox**: two interferometer paths — the "twins" — that may be kinematically
identical but accumulate **different entropic proper times** `τ_ent` because of
different entropy-production rates `λ`. The age difference shows up as a
measurable **suppression of interference visibility**, not as a clock reading.

Following the influence-functional weight `A_i ∝ exp(i S_{R,i}/ℏ − S_{I,i}/ℏ)
= e^{iφ_i} e^{−τ_{ent,i}}` (with `φ_i = S_{R,i}/ℏ`, `τ_{ent,i} = S_{I,i}/ℏ`):

* `entropicPathAmplitude φ τ` — a single path's amplitude (unitary phase ×
  entropic damping), with `‖A‖ = e^{−τ}`.
* `twoPathIntensity` — the recombined intensity
  `e^{−2τ₁} + e^{−2τ₂} + 2 e^{−(τ₁+τ₂)} cos Δφ` (`twoPathIntensity_eq`); the
  interference term is damped by the **summed** entropic time.
* `asymmetric_entropic_time_difference` / `asymmetric_visibility_suppression` —
  the Stern–Gerlach example: an extra rate `δλ` over a window `T` gives
  `Δτ_ent = δλ·T` and visibility suppression `exp(−½ δλ T)`.

## The twins

* **Quantum oscillator** (`oscillatorTwoLevelIntensity`): two energy eigenstates
  `n, m` of Physlib's `HarmonicOscillator` are the twins; their phase difference
  is `(n−m)ω t` (`oscillator_phase_difference`) and the fringe is
  `2 e^{−2τ}(1 + cos((n−m)ω t))`.
* **Electron / two-level** (`electronCoherence`): the two spin levels are the
  twins; the coherence `e^{−iω₀t} e^{−λt}` has visibility `e^{−λt}`
  (`norm_electronCoherence`). A non-Hermitian dimer exhibits a PT-like spectral
  transition at the critical rate `λ_c = 2|g|/ℏ`
  (`ptDiscriminant_at_criticalRate`, `ptEigenvalue_root`).

At `λ = 0` (zero entropy production) the damping is `1` and the standard unitary
interference is recovered.


## References

- **Pauli 1933** — *Die allgemeinen Prinzipien der Wellenmechanik*
- **Fujiwara 1979** — *A construction of the fundamental solution for the Schrödinger equation*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.Thermodynamics.SecondLaw QuantumMechanics.OneDimension.HarmonicOscillator
open Physlib.QFT.Wick.Consistency Physlib.QuantumMechanics.NonHermitian.WickRotation
namespace Physlib.Relativity.Special.TwinParadox.EntropicInterference

open QuantumInfo.Finite QuantumMechanics.OneDimension FieldSpecification

/-! ## §1 — Single-path amplitude: unitary phase × entropic damping -/

/-- A single path's influence-functional amplitude `e^{iφ} e^{−τ_ent}`: a unitary
phase `φ = S_R/ℏ` times the entropic damping `e^{−τ_ent}`, `τ_ent = S_I/ℏ`.

This is the **physical / interferometer-layer** name for the path amplitude.
The QFT-layer canonical form is `complexActionWeight` (in
`Physlib.QFT.Wick.Consistency`); both layers coincide at `ℏ = 1` via
`entropicPathAmplitude_eq_complexActionWeight`.  We keep both as separate
definitions to preserve the physical-product form
(`exp(iφ) · exp(−τ)`) used by downstream interferometer proofs — without
forcing them through the `complexActionWeight` single-exp form. -/
def entropicPathAmplitude (phi tau_ent : ℝ) : ℂ :=
  Complex.exp (↑phi * Complex.I) * (↑(Real.exp (-tau_ent)) : ℂ)

@[simp] theorem entropicPathAmplitude_re (phi tau_ent : ℝ) :
    (entropicPathAmplitude phi tau_ent).re = Real.exp (-tau_ent) * Real.cos phi := by
  unfold entropicPathAmplitude
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]; ring

@[simp] theorem entropicPathAmplitude_im (phi tau_ent : ℝ) :
    (entropicPathAmplitude phi tau_ent).im = Real.exp (-tau_ent) * Real.sin phi := by
  unfold entropicPathAmplitude
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]; ring

/-- **The amplitude's modulus is the entropic damping** `e^{−τ_ent}`: the entropic
proper time enters as the magnitude, the unitary phase as the argument. -/
theorem norm_entropicPathAmplitude (phi tau_ent : ℝ) :
    ‖entropicPathAmplitude phi tau_ent‖ = Real.exp (-tau_ent) := by
  unfold entropicPathAmplitude
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

/-! ## §1′ — Grounding: the path amplitude is an established entropic-time object

The definition `entropicPathAmplitude` is **not** a new posited object. We prove
it is exactly the complex action weight `complexActionWeight` (at `ℏ = 1`,
i.e. with `φ = S_R/ℏ`, `τ = S_I/ℏ`), so it inherits the justifications already
established for that weight: it distributes over Wick's theorem, its modulus is
the quantum relative entropy, and it is the non-Hermitian Schrödinger evolution
factor. This is what makes the abstraction the right one. -/

/-- **The path amplitude is the complex action weight.** With `φ = S_R/ℏ` and
`τ = S_I/ℏ`, `e^{iφ} e^{−τ} = exp(i S_R/ℏ − S_I/ℏ)` — the influence-functional /
path-integral weight `complexActionWeight`. -/
theorem entropicPathAmplitude_eq_complexActionWeight (phi tau : ℝ) :
    entropicPathAmplitude phi tau = complexActionWeight phi tau 1 := by
  unfold entropicPathAmplitude complexActionWeight
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- **The path amplitude distributes over Wick's theorem.** Being a
`complexActionWeight`, it is the same scalar that factors uniformly across the
time-ordered Wick-contraction expansion — grounding it in the QFT path integral. -/
theorem entropicPathAmplitude_smul_wicks_theorem
    {𝓕 : FieldSpecification} (phi tau : ℝ) (φs : List 𝓕.FieldOp) :
    entropicPathAmplitude phi tau •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length, entropicPathAmplitude phi tau • φsΛ.wickTerm := by
  rw [entropicPathAmplitude_eq_complexActionWeight]
  exact complexActionWeight_smul_wicks_theorem phi tau 1 φs

/-- **The damping is the quantum relative entropy.** When the entropic time is the
relative-entropy gap `D(ρ‖σ) = (entropicProperTime ρ σ).toReal`, the amplitude's
modulus is `e^{−D(ρ‖σ)}` — the entropic time of the interference is exactly
Physlib's `entropicProperTime`, not a free parameter. -/
theorem norm_entropicPathAmplitude_relativeEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (phi : ℝ) (ρ σ : MState d) :
    ‖entropicPathAmplitude phi ((entropicProperTime ρ σ).toReal)‖ =
      Real.exp (-(entropicProperTime ρ σ).toReal) :=
  norm_entropicPathAmplitude phi _

/-! ## §2 — Two-path recombination and the interference term -/

/-- Recombined intensity `|A₁ + A₂|²` of two interferometer paths. -/
def twoPathIntensity (phi1 tau1 phi2 tau2 : ℝ) : ℝ :=
  Complex.normSq (entropicPathAmplitude phi1 tau1 + entropicPathAmplitude phi2 tau2)

/-- **Entropic interference law.** The recombined intensity is
`e^{−2τ₁} + e^{−2τ₂} + 2 e^{−(τ₁+τ₂)} cos(φ₁−φ₂)`: the interference term is damped
by the **sum** of the two paths' entropic proper times. -/
theorem twoPathIntensity_eq (phi1 tau1 phi2 tau2 : ℝ) :
    twoPathIntensity phi1 tau1 phi2 tau2 =
      Real.exp (-(2 * tau1)) + Real.exp (-(2 * tau2))
        + 2 * (Real.exp (-(tau1 + tau2)) * Real.cos (phi1 - phi2)) := by
  unfold twoPathIntensity
  rw [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    entropicPathAmplitude_re, entropicPathAmplitude_re,
    entropicPathAmplitude_im, entropicPathAmplitude_im, Real.cos_sub]
  have e1 : Real.exp (-(2 * tau1)) = Real.exp (-tau1) * Real.exp (-tau1) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(2 * tau2)) = Real.exp (-tau2) * Real.exp (-tau2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e12 : Real.exp (-(tau1 + tau2)) = Real.exp (-tau1) * Real.exp (-tau2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2, e12]
  linear_combination (Real.exp (-tau1)) ^ 2 * Real.sin_sq_add_cos_sq phi1
    + (Real.exp (-tau2)) ^ 2 * Real.sin_sq_add_cos_sq phi2

/-- **Zero-entropy limit**: with no entropy production (`τ = 0`) the standard
unitary interference `2(1 + cos Δφ)` is recovered — full visibility. -/
theorem twoPathIntensity_at_zero_entropy (phi1 phi2 : ℝ) :
    twoPathIntensity phi1 0 phi2 0 = 2 * (1 + Real.cos (phi1 - phi2)) := by
  rw [twoPathIntensity_eq]; simp; ring

/-! ## §3 — Entropic time difference and visibility suppression -/

/-- Entropic-time difference between the two paths `Δτ_ent = τ₁ − τ₂`. -/
def deltaTauEnt (tau1 tau2 : ℝ) : ℝ := tau1 - tau2

/-- Mean entropic time `τ̄_ent = (τ₁ + τ₂)/2` governing the fringe visibility. -/
def meanTauEnt (tau1 tau2 : ℝ) : ℝ := (tau1 + tau2) / 2

/-- The interference term's damping is `e^{−2τ̄_ent}` — set by the mean entropic
time of the two paths. -/
theorem interference_damping_eq_mean (tau1 tau2 : ℝ) :
    Real.exp (-(tau1 + tau2)) = Real.exp (-(2 * meanTauEnt tau1 tau2)) := by
  unfold meanTauEnt; congr 1; ring

/-- **Stern–Gerlach asymmetric example.** Path 1 sees an extra entropic rate `δλ`
over a window `T` (rate `λ₀+δλ`), path 2 stays at `λ₀`; the entropic-time
difference is `Δτ_ent = δλ·T`. -/
theorem asymmetric_entropic_time_difference (lambda0 dlambda T : ℝ) :
    deltaTauEnt ((lambda0 + dlambda) * T) (lambda0 * T) = dlambda * T := by
  unfold deltaTauEnt; ring

/-- **Visibility suppression.** The asymmetric configuration's visibility
`e^{−τ̄}` is the symmetric one's times `exp(−½ δλ T)` — the measurable signature
of the entropic-time difference. -/
theorem asymmetric_visibility_suppression (lambda0 dlambda T : ℝ) :
    Real.exp (-meanTauEnt ((lambda0 + dlambda) * T) (lambda0 * T)) =
      Real.exp (-meanTauEnt (lambda0 * T) (lambda0 * T)) * Real.exp (-(dlambda * T / 2)) := by
  unfold meanTauEnt
  rw [← Real.exp_add]; congr 1; ring

/-! ## §4 — Quantum oscillator as the twins -/

/-- The phase accumulated by the `n`-th oscillator eigenstate over time `t`:
`(E_n/ℏ)·t`, using Physlib's harmonic-oscillator phase rate. -/
def oscillatorPhase (Q : HarmonicOscillator) (n : ℕ) (t : ℝ) : ℝ :=
  Q.eigenPhaseRate n * t

/-- **Grounding: the oscillator path amplitude is the reversible Schrödinger
phase of the eigenstate.** At zero entropic damping, the path amplitude with the
oscillator phase equals `reversiblePhase (E_n) ℏ t = exp(−i E_n t/ℏ)` — the actual
unitary evolution phase of the `n`-th eigenstate (from
`Physlib.QuantumMechanics.NonHermitian.WickRotation`). -/
theorem oscillatorPhase_amplitude_eq_reversiblePhase
    (Q : HarmonicOscillator) (n : ℕ) (t : ℝ) :
    entropicPathAmplitude (-(oscillatorPhase Q n t)) 0 =
      reversiblePhase (Q.eigenValue n) Constants.ℏ t := by
  unfold entropicPathAmplitude reversiblePhase oscillatorPhase
    QuantumMechanics.OneDimension.HarmonicOscillator.eigenPhaseRate
  rw [neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one]
  congr 1
  push_cast; ring

/-- The phase difference between oscillator eigenstates `n` and `m` is
`(n−m)·ω·t`. -/
theorem oscillator_phase_difference (Q : HarmonicOscillator) (n m : ℕ) (t : ℝ) :
    oscillatorPhase Q n t - oscillatorPhase Q m t = ((n : ℝ) - m) * Q.ω * t := by
  unfold oscillatorPhase
  rw [Q.eigenPhaseRate_eq, Q.eigenPhaseRate_eq]; ring

/-- Recombined intensity of two oscillator eigenstates (the "twins") sharing a
common entropic damping `τ`. -/
def oscillatorTwoLevelIntensity (Q : HarmonicOscillator) (n m : ℕ) (tau t : ℝ) : ℝ :=
  twoPathIntensity (oscillatorPhase Q n t) tau (oscillatorPhase Q m t) tau

/-- **Oscillator fringe.** Two oscillator eigenstates with common entropic time
`τ` interfere with fringe `2 e^{−2τ}(1 + cos((n−m)ω t))`. -/
theorem oscillatorTwoLevelIntensity_eq (Q : HarmonicOscillator) (n m : ℕ) (tau t : ℝ) :
    oscillatorTwoLevelIntensity Q n m tau t =
      2 * Real.exp (-(2 * tau)) * (1 + Real.cos (((n : ℝ) - m) * Q.ω * t)) := by
  unfold oscillatorTwoLevelIntensity
  rw [twoPathIntensity_eq, oscillator_phase_difference, show -(tau + tau) = -(2 * tau) from by ring]
  ring

/-! ## §5 — Electron (two-level system) as the twins -/

/-- Coherence of an electron two-level system: phase `−ω₀ t` and entropic damping
`λ t`. The two spin levels are the twins; their entropic-time difference drives
the coherence. -/
def electronCoherence (omega0 lambda t : ℝ) : ℂ :=
  entropicPathAmplitude (-(omega0 * t)) (lambda * t)

/-- **Grounding: the electron coherence is the non-Hermitian Schrödinger
evolution factor.** `electronCoherence ω₀ λ t = evolutionFactor ω₀ λ 1 t`, the
solution of `iℏ ∂_t ψ = H_C ψ` with `H_C = H_R − i H_I` (eigenvalues `ω₀`, `λ`)
proved in `Physlib.QuantumMechanics.NonHermitian.WickRotation`. The coherence is therefore
not a posited formula but the established Schrödinger amplitude. -/
theorem electronCoherence_eq_evolutionFactor (omega0 lambda t : ℝ) :
    electronCoherence omega0 lambda t = evolutionFactor omega0 lambda 1 t := by
  unfold electronCoherence
  rw [entropicPathAmplitude_eq_complexActionWeight, ← evolutionFactor_eq_complexActionWeight]

/-- **Dephasing / visibility decay.** The electron coherence has modulus
`e^{−λt}`: the interference visibility decays at the entropic rate `λ`. -/
theorem norm_electronCoherence (omega0 lambda t : ℝ) :
    ‖electronCoherence omega0 lambda t‖ = Real.exp (-(lambda * t)) :=
  norm_entropicPathAmplitude _ _

/-- At `λ = 0` the electron coherence is a pure unitary phase (unit modulus). -/
theorem norm_electronCoherence_at_zero_rate (omega0 t : ℝ) :
    ‖electronCoherence omega0 0 t‖ = 1 := by
  rw [norm_electronCoherence]; simp

/-! ### Non-Hermitian dimer and the PT-like transition -/

/-- Discriminant of the non-Hermitian dimer `g² − (ℏλ/2)²` controlling its
PT-like spectral transition. -/
def ptDiscriminant (g hbar lambda : ℝ) : ℝ := g ^ 2 - (hbar * lambda / 2) ^ 2

/-- Critical entropic rate `λ_c = 2|g|/ℏ` of the PT-like transition. -/
def criticalRate (g hbar : ℝ) : ℝ := 2 * |g| / hbar

/-- **Exceptional point.** At the critical rate the discriminant vanishes — the
two eigenvalues coalesce and the dimer becomes defective. -/
theorem ptDiscriminant_at_criticalRate (g hbar : ℝ) (hh : 0 < hbar) :
    ptDiscriminant g hbar (criticalRate g hbar) = 0 := by
  unfold ptDiscriminant criticalRate
  rw [show hbar * (2 * |g| / hbar) / 2 = |g| from by field_simp, sq_abs]; ring

/-- **Eigenvalue verification.** Given a square root `s` of the discriminant
(`s² = g² − (ℏλ/2)²`), the value `δ = iℏλ/2 + s` solves the dimer's
characteristic quadratic `δ² − iℏλ·δ − g² = 0`. The same holds for `−s`, giving
the eigenvalue pair `ε_± = E − δ_±`. -/
theorem ptEigenvalue_root (g hbar lambda : ℝ) (s : ℂ)
    (hs : s ^ 2 = (g : ℂ) ^ 2 - ((hbar * lambda : ℝ) / 2 : ℂ) ^ 2) :
    (Complex.I * ((hbar * lambda : ℝ) : ℂ) / 2 + s) ^ 2
        - Complex.I * ((hbar * lambda : ℝ) : ℂ) * (Complex.I * ((hbar * lambda : ℝ) : ℂ) / 2 + s)
        - (g : ℂ) ^ 2 = 0 := by
  linear_combination hs - (((hbar * lambda : ℝ) : ℂ) / 2) ^ 2 * Complex.I_mul_I

end Physlib.Relativity.Special.TwinParadox.EntropicInterference

end
