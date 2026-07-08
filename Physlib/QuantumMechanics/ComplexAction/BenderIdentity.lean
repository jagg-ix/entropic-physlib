/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Bender-Brody-Hook identity: complex energy ↔ entropy-production rate

Bender, Brody & Hook 2008 study "complex classical mechanics" with
complex energies `E = E_R + i·E_I`. In the resonance / Gamow-state
formalism, an exponentially decaying state has `E = E_R − i·Γ/2`
with decay width `Γ > 0`.

This module records the algebraic translation between Bender's
complex-energy framing and the complex-action framing
`S = S_R + i·S_I`:

  `dS_I/dt = −Im E`,      `Γ = 2 · dS_I/dt`,      `τ = ℏ / Γ`.

The translation is purely algebraic — no operator infrastructure
is required at this level. Connecting it to the QIF structure (§E)
identifies `dS_I/dt` with the expectation `H_I.reApplyInnerSelf ψ`
on a QIF state `ψ`, giving `τ_ψ = 1 / (2 · entropicRate ψ)`.

§F inverts the §A direction: given a measured lifetime `τ`, the
functions `rateFromLifetime`, `widthFromLifetime`, and
`entropyRateFromLifetime` recover the rate, width, and
entropy-production-rate parameters of §A via `λ := 1/τ`,
`Γ := ℏ/τ`, `Ṡ_I := ℏ/(2τ)`.

## Contents

### §A — Bender translation

* `imaginaryEnergyOfRate` — `Im E := −Ṡ_I`.
* `widthFromRate` — `Γ := 2 · Ṡ_I`.
* `lifetimeFromRate` — `τ := ℏ / (2 · Ṡ_I) = ℏ / Γ`.

### §B — Algebraic identities

* `widthFromRate_eq_negTwoImE` — `Γ = −2 · Im E`.
* `lifetime_mul_width` — `τ · Γ = ℏ`.
* `lifetime_pos` — positivity from `ℏ > 0`, `Ṡ_I > 0`.

### §C — Boring-model recovery (reversible limit)

* `widthFromRate_at_zero` — at `Ṡ_I = 0`, `Γ = 0`.
* `imaginaryEnergyOfRate_at_zero` — at `Ṡ_I = 0`, `Im E = 0`.

### §D — Stationarity split (linearity of variation)

* `stationaryComplexAction_split` — the complex-action variation
  `δV_R + i·δV_I = 0` is equivalent to `δV_R = 0 ∧ δV_I = 0`.

### §E — Bridge to `QuantumInertialFrame`

* `qifLifetime` — lifetime parametrized by a QIF and a state.
* `qifLifetime_eq_inv_two_entropicRate` — `τ_ψ = 1 / (2 · λ(ψ))`
  whenever the entropic rate is positive.

### §F — Inverse direction

* `widthFromLifetime` — `Γ := ℏ / τ`.
* `rateFromLifetime` — `λ := 1 / τ`.
* `entropyRateFromLifetime` — `Ṡ_I := ℏ / (2·τ)`.
* `rate_lifetime_inverse` — `λ · τ = 1`.
* `widthFromLifetime_eq_two_entropyRateFromLifetime` —
  `Γ = 2 · Ṡ_I` reproduced in inverse-direction parameters.

### §G — Bender exponential decay law

* `benderDecayFraction` — `f(t,τ) := exp(−t/τ)`, the
  squared-norm fraction `|ψ(t)|² / |ψ(0)|²` predicted by
  the Bender 2008 starting equation for a Gamow state with
  lifetime `τ`.
* `benderDecayFraction_at_zero` — at `t = 0`, fraction is `1`.
* `benderDecayFraction_at_lifetime` — at `t = τ`, fraction is
  `exp(−1) ≈ 0.368` (the operational definition of lifetime).
* `benderDecayFraction_strictAnti` — strict monotone decay in
  `t` for `τ > 0`.
* `qifLifetime_decayFraction_eq_inv_e` — bridge from §E to §G:
  at `t = qifLifetime ψ`, the Bender decay fraction equals
  `exp(−1)`.

### §H — Complex energy

* `complexEnergyOfRate` — `E := E_R − i·Ṡ_I`, the Gamow
  complex energy expressed from (real-energy, entropy-rate)
  inputs.  The Bender 2008 starting form
  `E = E_R − i·(Γ/2)` is recovered at `Ṡ_I = Γ/2`.
* `complexEnergyOfRate_re` — `Re E = E_R`.
* `complexEnergyOfRate_im` — `Im E = −Ṡ_I = imaginaryEnergyOfRate`.
* `widthFromRate_eq_negTwoIm_complexEnergyOfRate` — `Γ =
  −2·Im(E)` directly from the complex-energy projection.

### §I — Bender real-part phase accumulation (stationary state)

* `benderPhase` — `arg(ψ(t)) − arg(ψ(0)) = −E_R·t/ℏ`, the
  real-part complement to §G's decay law.  Together §G + §I
  give the polar decomposition of the Bender 2008 starting
  equation `ψ(t) = exp(−i·E·t/ℏ)·ψ(0)` for a state of
  *definite complex energy* `E = E_R − i·Ṡ_I`.
* `benderPhase_at_zero`        — `Δφ(0) = 0`.
* `benderPhase_linear_in_T`     — phase grows linearly in `t`
  for a stationary state (constant `E_R`).
* `bender_polar_decomposition` — §G + §I give the squared
  modulus and the argument of `ψ(t)/ψ(0)` respectively.

## Reference paper and central equation

Carl M. Bender, Dorje C. Brody, Daniel W. Hook (2008),
*Quantum effects in classical systems having complex energy*,
Journal of Physics A: Mathematical and Theoretical **41** (35),
352003 (12 pp.).
DOI: [10.1088/1751-8113/41/35/352003](https://doi.org/10.1088/1751-8113/41/35/352003).
arXiv: [0804.4169](https://arxiv.org/abs/0804.4169).

The paper studies classical Hamiltonian dynamics with a complex
energy `E = E_R + i·E_I`.  A state evolved by the standard
quantum phase factor

  `ψ(t) = exp(−i·E·t/ℏ) · ψ(0)`

then decays as

  `|ψ(t)|² = exp(2·E_I·t/ℏ) · |ψ(0)|²`,

i.e. exponential decay when `E_I < 0`.  Writing the same evolution
through the complex-action weight `exp(i·S/ℏ)` with
`S = S_R + i·S_I` gives

  `exp(i·S/ℏ) = exp(i·S_R/ℏ) · exp(−S_I/ℏ)`,

and matching the two forms over an interval `Δt` yields the
identification this module records:

  `dS_I/dt = −Im E   ⇔   Γ = 2·dS_I/dt   ⇔   τ = ℏ/Γ`.

The Gamow normalisation `E = E_R − i·Γ/2` is the special case
`dS_I/dt = Γ/2`.

## Related references

- Carl M. Bender, Stefan Boettcher (1998), *Real spectra in
  non-Hermitian Hamiltonians having `PT` symmetry*, Physical
  Review Letters **80** (24), 5243–5246.
  DOI: [10.1103/PhysRevLett.80.5243](https://doi.org/10.1103/PhysRevLett.80.5243).
  Earlier Bender work introducing the `PT`-symmetric class of
  non-Hermitian Hamiltonians with real spectra; provides historical
  context for the 2008 complex-energy classical-mechanics paper.

- J. B. Pendry (2021), *Photon number conservation in time
  dependent systems*, Optics Express **29** (25), 41587.
  arXiv: [2209.11576](https://arxiv.org/abs/2209.11576).
  Proves that PT-symmetric time-dependent media conserve photon
  number even when energy is not conserved.  The orthogonality
  relation between Floquet eigenvectors makes each contribute
  independently to the total photon count.  In experimental
  realisations of such systems (e.g. pump-modulated ITO at ENZ
  wavelengths) this conservation law constrains observables in
  ways that the algebraic Bender identity alone does not.

- J. B. Pendry (2024), *An avalanche model for femtosecond
  optical response*, arXiv: [2407.08391](https://arxiv.org/abs/2407.08391).
  Microscopic origin for the femtosecond reflectivity rise in
  pump-modulated ITO: an Auger-driven electron avalanche makes
  the conduction-band density grow as `n(t) = n₀ · exp(β t)`
  with `β = E·e / √(U_G · m)`.  The effective Drude damping
  becomes `γ_eff = γ_Drude − β`; above threshold (`β > γ_Drude`)
  this yields negative effective damping — Bender's complex-
  energy structure (gain mode) derived from explicit microscopic
  dynamics rather than postulated.

- D. Oue, J. B. Pendry, M. G. Silveirinha (2024),
  *Stable-to-unstable transition in quantum friction*, arXiv:
  [2402.09074](https://arxiv.org/abs/2402.09074).
  A third route to the Bender gain mode: two metallic plates
  in shear motion at velocity `±v/2`.  The Doppler-shifted
  Drude permittivity `ε(ω ± k_x·v/2)` has negative imaginary
  part for short-wavelength modes when `|k_x|·v/2 > ω`, making
  the moving medium a gain medium.  Stable-to-unstable
  transition at critical velocity `v̄_cr ≈ −2/log(γ̄)` (his
  eq. 15, dimensionless units `v̄ = v/(ω_sp·L)`, `γ̄ = γ/ω_sp`).
  Same Bender complex-energy gain structure as Pendry 2024 but
  through Doppler-shift instead of avalanche dynamics.  No
  experimental measurement of this specific setup as of this
  writing; the theoretical prediction stands.
## Evidence-level discipline

The theorems in this module are **claim-level 1**: positivity and
algebraic identities. They do **not** prove:

- existence of the Gamow state `E_R − i·Γ/2` (Pauli's objection
  applies on the operator side);
- falsifiable predictive content beyond the algebraic relation;
- discreteness or quantization.

The boring-model recovery is explicit at `Ṡ_I = 0`: width vanishes,
imaginary energy vanishes, and the QIF lifetime diverges (formally
`ℏ / 0 = 0` in Lean's Real arithmetic; physically the reversible
limit `τ = ∞`).

## Scope of `τ`

The symbol `τ` throughout this module is the **Gamow decay
lifetime** of a resonance: `τ := ℏ / Γ` with `Γ` the width of
the imaginary part of the complex energy.  It is **not**:

* a pulse envelope rise time (set by source preparation, not by
  `H_I`);
* a transport / diffusion / thermalisation timescale;
* a coherence / dephasing time `T₂` in an open-system (Lindblad
  or master-equation) description;
* a population relaxation time `T₁` for an excited level.

These four timescales coincide only in special cases.  Operational
identifications of `τ` with the timescale of a specific physical
mechanism in a specific experiment live in consumer files (for
example `Physlib.Optics.TemporalDoubleSlit`); the present module
records only the algebraic identity `λ ↔ Γ ↔ τ ↔ Ṡ_I`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction

open QuantumMechanics.FiniteTarget

/-! ## §A — Bender translation -/

/-- **Imaginary part of complex energy** from an entropy-production
rate: `Im E := −Ṡ_I` (Bender identity). -/
def imaginaryEnergyOfRate (dSI_dt : ℝ) : ℝ := -dSI_dt

/-- **Resonance width** from an entropy-production rate:
`Γ := 2 · Ṡ_I`. -/
def widthFromRate (dSI_dt : ℝ) : ℝ := 2 * dSI_dt

/-- **Resonance lifetime** from an entropy-production rate:
`τ := ℏ / Γ = ℏ / (2 · Ṡ_I)`. -/
def lifetimeFromRate (ℏ dSI_dt : ℝ) : ℝ := ℏ / (2 * dSI_dt)

/-! ## §B — Algebraic identities -/

/-- **`Γ = −2 · Im E`**: the width equals minus twice the imaginary
energy.

Claim level: 1 (algebraic identity).
Does not prove: existence of the resonance state; physical meaning
of `ℏ`; quantization. The same identity holds for `Ṡ_I = 0`
(boring model), where `Γ = 0` and `Im E = 0` trivially. -/
theorem widthFromRate_eq_negTwoImE (dSI_dt : ℝ) :
    widthFromRate dSI_dt = -2 * imaginaryEnergyOfRate dSI_dt := by
  unfold widthFromRate imaginaryEnergyOfRate
  ring

/-- **Width-lifetime duality**: `τ · Γ = ℏ`.

Claim level: 1 (algebraic identity).
Does not prove: existence of the resonance; that any real system
has the predicted lifetime. The boring model `Ṡ_I = 0` falls
outside the hypothesis since the identity requires `Ṡ_I ≠ 0`. -/
theorem lifetime_mul_width (ℏ dSI_dt : ℝ) (h : dSI_dt ≠ 0) :
    lifetimeFromRate ℏ dSI_dt * widthFromRate dSI_dt = ℏ := by
  unfold lifetimeFromRate widthFromRate
  field_simp

/-- The width is positive iff the entropy-production rate is. -/
theorem widthFromRate_pos_iff (dSI_dt : ℝ) :
    0 < widthFromRate dSI_dt ↔ 0 < dSI_dt := by
  unfold widthFromRate
  constructor <;> intro h <;> linarith

/-- **Lifetime is positive** when both `ℏ > 0` and `Ṡ_I > 0`.

Claim level: 1 (positivity).
Does not prove: discreteness; minimum step; quantization. The same
conclusion holds for any positive `Ṡ_I` with no specific physical
content — this is just `positive / positive = positive`. -/
theorem lifetime_pos {ℏ dSI_dt : ℝ}
    (hℏ : 0 < ℏ) (hSI : 0 < dSI_dt) :
    0 < lifetimeFromRate ℏ dSI_dt := by
  unfold lifetimeFromRate
  exact div_pos hℏ (by linarith)

/-! ## §C — Boring-model recovery (reversible limit) -/

/-- **At `Ṡ_I = 0` the width vanishes** — no decay, the state is
stationary. -/
@[simp] theorem widthFromRate_at_zero : widthFromRate 0 = 0 := by
  unfold widthFromRate
  ring

/-- **At `Ṡ_I = 0` the imaginary energy vanishes** — energy is real,
the state is bound rather than resonant. -/
@[simp] theorem imaginaryEnergyOfRate_at_zero :
    imaginaryEnergyOfRate 0 = 0 := by
  unfold imaginaryEnergyOfRate
  ring

/-! ## §D — Stationarity split (linearity of variation) -/

/-- **Stationarity of the complex action splits into its real and
imaginary parts**: for any real `δV_R, δV_I`, the complex variation
`δV_R + i·δV_I = 0` is equivalent to `δV_R = 0 ∧ δV_I = 0`.

This is linearity of variation for the complex-valued action
functional. Useful as a foundational lemma for downstream consumers
who want to derive separate Euler-Lagrange equations for the real
and imaginary parts.

Claim level: 1 (foundational identity).
Does not prove: existence of stationary trajectories; uniqueness;
quantization. The same equivalence holds trivially at
`δV_R = δV_I = 0`. -/
theorem stationaryComplexAction_split (δV_R δV_I : ℝ) :
    ((δV_R : ℂ) + Complex.I * (δV_I : ℂ) = 0) ↔
      (δV_R = 0 ∧ δV_I = 0) := by
  constructor
  · intro h
    have hR : (((δV_R : ℂ) + Complex.I * (δV_I : ℂ)).re) = 0 := by
      rw [h]; simp
    have hI : (((δV_R : ℂ) + Complex.I * (δV_I : ℂ)).im) = 0 := by
      rw [h]; simp
    simp at hR hI
    exact ⟨hR, hI⟩
  · rintro ⟨hR, hI⟩
    rw [hR, hI]
    simp

/-! ## §E — Bridge to `QuantumInertialFrame`

The QIF structure `(H_R, H_I, ℏ)` with state `ψ` identifies the
entropy-production rate as

  `dS_I/dt := H_I.reApplyInnerSelf ψ = Re ⟨ψ, H_I ψ⟩`.

Plugging into `lifetimeFromRate` gives the QIF lifetime; the
positivity of `H_I` plus `ℏ > 0` ensures the numerator-denominator
positivity. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- **QIF lifetime at a state `ψ`**: `τ_ψ := ℏ / (2 · ⟨ψ, H_I ψ⟩)`,
the Bender lifetime parametrized by a Quantum Inertial Frame. -/
def qifLifetime (Q : QuantumInertialFrame H) (ψ : H) : ℝ :=
  lifetimeFromRate Q.hbar (Q.H_I.reApplyInnerSelf ψ)

/-- **`qifLifetime = 1 / (2 · entropicRate ψ)`** whenever the
entropic rate is positive.

This is the operational form of the Bender lifetime in the QIF
language: it factors out `ℏ` against the `ℏ` in `entropicRate ψ
:= ⟨ψ, H_I ψ⟩ / ℏ`.

Claim level: 1 (algebraic identity under
the entropic-rate identification).
Does not prove: that any system actually has `entropicRate ψ > 0`;
that the QIF structure is non-trivial; quantization. The boring
model `H_I := 0` (reversibleQIF) makes `entropicRate ψ = 0`, so
the hypothesis `0 < entropicRate ψ` fails and the conclusion does
not apply — the boring model is *outside* the hypothesis,
correctly. -/
theorem qifLifetime_eq_inv_two_entropicRate
    (Q : QuantumInertialFrame H) {ψ : H}
    (h_pos : 0 < Q.entropicRate ψ) :
    qifLifetime Q ψ = 1 / (2 * Q.entropicRate ψ) := by
  unfold qifLifetime lifetimeFromRate QuantumInertialFrame.entropicRate
  have hℏ : Q.hbar ≠ 0 := ne_of_gt Q.hbar_pos
  have h_re : Q.H_I.reApplyInnerSelf ψ ≠ 0 := by
    intro h_eq
    have : Q.entropicRate ψ = 0 := by
      unfold QuantumInertialFrame.entropicRate
      rw [h_eq]
      simp
    linarith
  field_simp

/-- **QIF lifetime is positive** at any state where the entropic
rate is positive. -/
theorem qifLifetime_pos
    (Q : QuantumInertialFrame H) {ψ : H}
    (h_pos : 0 < Q.entropicRate ψ) :
    0 < qifLifetime Q ψ := by
  rw [qifLifetime_eq_inv_two_entropicRate Q h_pos]
  exact div_pos one_pos (by linarith)

/-! ## §F — Inverse direction

Given a lifetime `τ`, the Bender identity inverts to a rate, a
width, and an entropy-production rate via the algebraic relations
`λ = 1/τ`, `Γ = ℏ/τ`, `Ṡ_I = ℏ/(2τ)`. -/

/-- **Decay rate from lifetime**: `λ := 1 / τ`. -/
def rateFromLifetime (τ : ℝ) : ℝ := 1 / τ

/-- **Width from lifetime**: `Γ := ℏ / τ`. -/
def widthFromLifetime (ℏ τ : ℝ) : ℝ := ℏ / τ

/-- **Entropy-production rate from lifetime**:
`Ṡ_I := ℏ / (2·τ) = Γ / 2`. -/
def entropyRateFromLifetime (ℏ τ : ℝ) : ℝ := ℏ / (2 * τ)

/-- **Rate–lifetime inverse**: `λ · τ = 1`.

Claim level: 1 (algebraic identity).
Does not prove: existence of the resonance; that any system has
the predicted rate. The boring model `τ = ∞` falls outside the
hypothesis since the identity requires `τ ≠ 0`. -/
theorem rate_lifetime_inverse {τ : ℝ} (hτ : τ ≠ 0) :
    rateFromLifetime τ * τ = 1 := by
  unfold rateFromLifetime
  field_simp

/-- **`Γ = 2 · Ṡ_I` reproduced in inverse-direction parameters**:
`widthFromLifetime ℏ τ = 2 · entropyRateFromLifetime ℏ τ`. -/
theorem widthFromLifetime_eq_two_entropyRateFromLifetime
    (ℏ τ : ℝ) :
    widthFromLifetime ℏ τ = 2 * entropyRateFromLifetime ℏ τ := by
  unfold widthFromLifetime entropyRateFromLifetime
  ring

/-- **Inverse direction recovers §A**: applying
`lifetimeFromRate` to `entropyRateFromLifetime` returns `τ`. -/
theorem lifetimeFromRate_entropyRateFromLifetime
    {ℏ τ : ℝ} (hℏ : ℏ ≠ 0) (hτ : τ ≠ 0) :
    lifetimeFromRate ℏ (entropyRateFromLifetime ℏ τ) = τ := by
  unfold lifetimeFromRate entropyRateFromLifetime
  field_simp

/-- **Inverse direction agrees on the width**: applying
`widthFromRate` to `entropyRateFromLifetime` returns
`widthFromLifetime`. -/
theorem widthFromRate_entropyRateFromLifetime
    (ℏ τ : ℝ) :
    widthFromRate (entropyRateFromLifetime ℏ τ) =
      widthFromLifetime ℏ τ := by
  unfold widthFromRate entropyRateFromLifetime widthFromLifetime
  ring

/-- **Positivity of `rateFromLifetime` at positive lifetime**. -/
theorem rateFromLifetime_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < rateFromLifetime τ :=
  div_pos one_pos hτ

/-! ## §G — Bender exponential decay law

The Bender 2008 starting equation

  `ψ(t) = exp(−i·E·t/ℏ) · ψ(0)`

with `E = E_R − i·Γ/2` (the Gamow normalisation, see the
opening docstring) gives a squared-modulus evolution

  `|ψ(t)|² = exp(2·E_I·t/ℏ) · |ψ(0)|²
          = exp(−Γ·t/ℏ) · |ψ(0)|²
          = exp(−t/τ) · |ψ(0)|²    (using `τ = ℏ/Γ`)`

This section formalises the **squared-modulus decay fraction**
`f(t, τ) := |ψ(t)|² / |ψ(0)|² = exp(−t/τ)` and proves four
basic properties:

* `benderDecayFraction_at_zero`        — `f(0, τ) = 1`
* `benderDecayFraction_at_lifetime`    — `f(τ, τ) = exp(−1)`
* `benderDecayFraction_strictAnti`     — strict decay in `t`
* `qifLifetime_decayFraction_eq_inv_e` — bridge from §E

The last theorem is the bridge: it shows that the QIF lifetime
defined in §E is precisely the `1/e` time of the Bender decay
fraction.  This connects the abstract entropic-rate algebra
(§A-§F) to a measurable observable (the time at which the
squared-norm has decayed to `1/e` of its initial value).

**Note on scope.**  This section formalises the *scalar*
content — the algebraic exponential identity `exp(−t/τ)` and
its behaviour at distinguished points.  The full Schrödinger
evolution `ψ(t) := exp(−i·H·t/ℏ)·ψ(0)` as an operator on
`QuantumInertialFrame.H` is not formalised; that would
require the operator-exp infrastructure for non-Hermitian
generators, which is beyond the scope of the algebraic
identity recorded here.  Downstream code that has access to
such infrastructure can compose it with this section's results
to derive the full state evolution.
-/

/-- **Bender decay fraction**: the predicted squared-modulus
ratio `|ψ(t)|² / |ψ(0)|²` for a Gamow state with lifetime `τ`.

Defined directly as `exp(−t/τ)`.  At `t = 0` the fraction is
`1` (no decay yet); at `t = τ` the fraction is `exp(−1) ≈
0.368` (the operational definition of lifetime). -/
def benderDecayFraction (t τ : ℝ) : ℝ := Real.exp (-(t / τ))

/-- **At `t = 0` no decay has occurred** — the fraction is
`1`. -/
@[simp] theorem benderDecayFraction_at_zero (τ : ℝ) :
    benderDecayFraction 0 τ = 1 := by
  unfold benderDecayFraction
  simp

/-- **At `t = τ` the fraction is `1/e`** — the operational
definition of "lifetime": the time at which a Gamow state has
decayed to `exp(−1) ≈ 0.368` of its initial squared norm. -/
@[simp] theorem benderDecayFraction_at_lifetime {τ : ℝ}
    (hτ : τ ≠ 0) :
    benderDecayFraction τ τ = Real.exp (-1) := by
  unfold benderDecayFraction
  rw [div_self hτ]

/-- **Bender decay fraction is strictly monotone-decreasing**
in `t` whenever `τ > 0`.  Together with
`benderDecayFraction_at_zero` and
`benderDecayFraction_at_lifetime`, this is the falsifiable
shape of the Bender 2008 prediction: monotone exponential decay
through the `1/e` point at `t = τ`. -/
theorem benderDecayFraction_strictAnti {τ : ℝ} (hτ : 0 < τ) :
    StrictAnti (fun t : ℝ => benderDecayFraction t τ) := by
  intro t₁ t₂ ht
  unfold benderDecayFraction
  apply Real.exp_lt_exp.mpr
  apply neg_lt_neg
  exact (div_lt_div_iff_of_pos_right hτ).mpr ht

/-- **Bender decay fraction is positive** for any input. -/
theorem benderDecayFraction_pos (t τ : ℝ) :
    0 < benderDecayFraction t τ := by
  unfold benderDecayFraction
  exact Real.exp_pos _

/-! ### Bridge from §E: QIF lifetime is the `1/e` time -/

/-- **Bridge theorem**: at time `t = qifLifetime ψ`, the
Bender decay fraction equals `exp(−1)`.

This connects §E (the QIF entropic-rate formulation of the
Bender lifetime as a structural quantity) to §G (the Bender
decay law as a measurable observable).  The proof is direct
substitution + `benderDecayFraction_at_lifetime`. -/
theorem qifLifetime_decayFraction_eq_inv_e
    (Q : QuantumInertialFrame H) {ψ : H}
    (h_pos : 0 < Q.entropicRate ψ) :
    benderDecayFraction (qifLifetime Q ψ) (qifLifetime Q ψ) =
      Real.exp (-1) := by
  apply benderDecayFraction_at_lifetime
  exact ne_of_gt (qifLifetime_pos Q h_pos)

/-! ## §H — Complex energy

Bender, Brody & Hook 2008 organise their treatment around the
complex energy

  `E = E_R + i·E_I`

with `E_I = −Ṡ_I` (the Bender identity §A) and the Gamow
normalisation

  `E = E_R − i·Γ/2`

obtained at `Ṡ_I = Γ/2`.  §A defined the imaginary part
`imaginaryEnergyOfRate Ṡ_I := −Ṡ_I` directly; this section
adds the full complex energy `complexEnergyOfRate (E_R Ṡ_I)`
as a first-class object together with its real/imaginary
projections, recovering the Bender 2008 starting form.

The content here is cosmetic — projection lemmas only, no new
algebraic identity.  Its value is making the connection to the
standard physics notation (`E = E_R − i·Γ/2`) explicit in
Lean, so downstream theorems can be stated directly in terms
of `E`. -/

/-- **Bender complex energy** in the Gamow form `E = E_R −
i·Ṡ_I`.  The real part is the real energy `E_R`; the
imaginary part is `−Ṡ_I = imaginaryEnergyOfRate Ṡ_I` per §A.

When `Ṡ_I = Γ/2`, this is the standard Bender 2008 starting
form `E = E_R − i·(Γ/2)`. -/
def complexEnergyOfRate (E_R dSI_dt : ℝ) : ℂ :=
  ⟨E_R, -dSI_dt⟩

/-- **Real part of the Bender complex energy** is `E_R`. -/
@[simp] theorem complexEnergyOfRate_re (E_R dSI_dt : ℝ) :
    (complexEnergyOfRate E_R dSI_dt).re = E_R := by
  unfold complexEnergyOfRate
  rfl

/-- **Imaginary part of the Bender complex energy** equals
`imaginaryEnergyOfRate Ṡ_I = −Ṡ_I` from §A. -/
@[simp] theorem complexEnergyOfRate_im (E_R dSI_dt : ℝ) :
    (complexEnergyOfRate E_R dSI_dt).im =
      imaginaryEnergyOfRate dSI_dt := by
  unfold complexEnergyOfRate imaginaryEnergyOfRate
  rfl

/-- **Width-energy duality via complex projection**:
`Γ = −2 · Im(E)` directly from the complex-energy form.

This is `widthFromRate_eq_negTwoImE` (§B) re-stated through
the §H complex-energy projection. -/
theorem widthFromRate_eq_negTwoIm_complexEnergyOfRate
    (E_R dSI_dt : ℝ) :
    widthFromRate dSI_dt =
      -2 * (complexEnergyOfRate E_R dSI_dt).im := by
  rw [complexEnergyOfRate_im]
  exact widthFromRate_eq_negTwoImE dSI_dt

/-- **At `Ṡ_I = 0` the complex energy is purely real** —
boring-model limit consistent with §C. -/
@[simp] theorem complexEnergyOfRate_at_zero (E_R : ℝ) :
    complexEnergyOfRate E_R 0 = (E_R : ℂ) := by
  unfold complexEnergyOfRate
  apply Complex.ext
  · rfl
  · simp

/-! ## §I — Bender real-part phase accumulation (stationary state)

The Bender 2008 starting equation

 `ψ(t) = exp(−i·E·t/ℏ) · ψ(0)`

with `E = E_R + i·E_I` factors polarly for a state of
**definite complex energy** into a squared-modulus part and
an argument part:

 `|ψ(t)|² / |ψ(0)|² = exp(2·E_I·t/ℏ) = exp(−Γ·t/ℏ)`
 (§G)

 `arg(ψ(t)) − arg(ψ(0)) = −E_R · t / ℏ`
 (§I, here)

Section §G formalises the modulus side via `benderDecayFraction`;
this section §I formalises the argument side via
`benderPhase`. Together §G + §I give the polar decomposition
of `ψ(t) / ψ(0)` — the full Bender 2008 evolution at the
scalar level, without requiring operator-exp infrastructure
for `exp(−i·H·t/ℏ)`.

## Scope

This section formalises the **stationary-state** phase: a
state of definite complex energy `E = E_R − i·Ṡ_I` whose real
part `E_R` is *constant in time*. This is the case directly
addressed by the Bender 2008 paper.

It does **not** formalise:

* phase accumulation in a time-varying real Hamiltonian
 `H_R(t)` (the general `Δφ(T) = −(1/ℏ)·∫₀^T E_R(t') dt'`
 form, which would require Mathlib's `intervalIntegral`);

* action-integral phases over accelerated wave-packet
 trajectories (e.g. the `T³` gravitational phase reported
 in matter-wave interferometers like Margalit et al. 2021,
 Sci. Adv. **7**, eabg2879). Those phases are **not** part
 of the Bender complex-energy framework — they come from
 general Hamilton-Jacobi action integrals over classical
 trajectories with a purely Hermitian `H_R`, with no
 `Im[E]` involved. Linking them to the Bender identity
 would be a scope creep: same Schrödinger equation, but a
 qualitatively different physical mechanism.

What §I *does* deliver is the **scalar argument-side
completeness of §G**: given a state of definite Bender
complex energy, §G gives `|ψ(t)|²/|ψ(0)|²` and §I gives
`arg(ψ(t)) − arg(ψ(0))`. Their composition is `ψ(t)/ψ(0)`,
the full scalar evolution factor.
-/

/-- **Bender real-part phase** accumulated by a stationary
state of definite complex energy `E = E_R − i·Ṡ_I` over time
`t`:

  `Δφ := −E_R · t / ℏ`.

For such a state, the Bender 2008 starting equation factors
as

  `ψ(t) = exp(−i·E_R·t/ℏ) · exp(−Ṡ_I·t/ℏ) · ψ(0)
       = exp(i · benderPhase E_R t ℏ) · sqrt(benderDecayFraction t τ) · ψ(0)`.

Stationary `E_R` only — the time-varying case is outside the
Bender-identity scope per the §I docstring above. -/
def benderPhase (E_R t ℏ : ℝ) : ℝ := -(E_R * t) / ℏ

/-- **At `t = 0` no phase has accumulated** — the trivial
identity. -/
@[simp] theorem benderPhase_at_zero (E_R ℏ : ℝ) :
    benderPhase E_R 0 ℏ = 0 := by
  unfold benderPhase
  simp

/-- **Bender phase is linear in `t`** for a stationary state
(constant `E_R`): the slope is `−E_R / ℏ`. -/
theorem benderPhase_linear_in_T (E_R t ℏ : ℝ) :
    benderPhase E_R t ℏ = (-E_R / ℏ) * t := by
  unfold benderPhase
  ring

/-! ### Bridge: §G + §I give the full polar decomposition

For a state of definite complex energy `E = E_R − i·Ṡ_I`,
the evolution ratio `ψ(t) / ψ(0) = exp(−i·E·t/ℏ)` decomposes
polarly into:

  `|ψ(t)/ψ(0)|² = benderDecayFraction t τ`         (§G modulus)
  `arg(ψ(t)/ψ(0)) = benderPhase E_R t ℏ`           (§I argument)

The product `sqrt(benderDecayFraction) · exp(i · benderPhase)`
*is* `ψ(t) / ψ(0)` — the scalar evolution factor in the
Bender 2008 starting equation.  This bridge theorem records
that fact at the algebraic level. -/

/-- **Polar reconstruction of the Bender evolution factor**:
the squared modulus of the positive-real factor
`exp(−t/(2τ))` is exactly `benderDecayFraction t τ` from §G,
and the argument of the complex-exponential factor is exactly
`benderPhase E_R t ℏ` from §I.  Up to the freedom in the
square-root convention, the product `exp(i · benderPhase) ·
exp(−t/(2τ))` is `ψ(t)/ψ(0)` from the Bender 2008 starting
equation, restricted to a state of definite `(E_R, τ)`. -/
theorem bender_polar_decomposition (E_R t ℏ τ : ℝ) :
    Real.exp (-(t / (2 * τ))) ^ 2 = benderDecayFraction t τ ∧
    benderPhase E_R t ℏ = -(E_R * t) / ℏ := by
  refine ⟨?_, rfl⟩
  unfold benderDecayFraction
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end Physlib.QuantumMechanics.ComplexAction

end
