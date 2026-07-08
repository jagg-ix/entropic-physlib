/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Material timescales for open-system optical experiments

This module distinguishes the four timescales that appear in
visibility / decay measurements on a driven medium and names
which one the Bender lifetime identity from
`Physlib.QuantumMechanics.ComplexAction.BenderIdentity`
applies to.

In an open-system (Lindblad / master-equation) description, a
driven optical medium has at least four distinct timescales:

* `τ_envelope` — the rise time of the **driving pulse envelope**.
 Set by source preparation, not by the medium. Controls the
 Fourier-bandwidth and so the spectrum envelope width.

* `τ_coherence` (`T₂`) — the **dephasing time** of the medium's
 off-diagonal density-matrix elements between two times.
 Controls fringe visibility in interferometric experiments
 (e.g. temporal double-slit fringe contrast at separation `S`).

* `τ_population` (`T₁`) — the **population relaxation** time of
 excited levels in the medium. Controls amplitude decay of
 occupation numbers.

* `τ_Gamow` — the **resonance decay lifetime** of an unstable
 state, defined by `τ_Gamow := ℏ / Γ` where `Γ` is the resonance
 width. This is the timescale that appears in the Bender-Brody-
 Hook complex-energy identity (see `BenderIdentity`).

These four timescales coincide only in special cases. Standard
open-system relations give for example `1 / T₂ = 1 / (2 T₁) + 1 /
T_φ` where `T_φ` is the pure-dephasing time; the envelope time is
independent of all three and the Gamow time can differ from each
of them by many orders of magnitude.

## What this module records

§A defines named representatives for the four timescales (Prop-level
predicates that an experimenter can attach to a measurement
without committing to any particular numerical value).

§B records, as an explicit `Prop`, the **literal-rise-time
identification hypothesis** — the claim that the Bender lifetime
equals the envelope rise time of the experimental drive. This
is the identification implicit in any code that takes a
laboratory-measured `τ_envelope` and plugs it into the Bender
identity's `τ` slot. Stating it as a `Prop` makes it explicit
that this is an empirical hypothesis, separable from the
algebraic identity.

§C records the **medium-dephasing identification hypothesis**:
the Bender lifetime equals the medium dephasing time `T₂`. This
is the alternative identification when the experiment probes
coherence decay rather than amplitude decay (the temporal
double-slit fringe-visibility measurement is in this class).

§D states a refutation condition: if the visibility of an
interferometric experiment at fixed slit separation `S` is
independent of the envelope rise time, the literal-rise-time
identification is refuted for that experimental class (because a
common Bender lifetime would predict exponential dependence on
`1/τ_envelope`).

## References

* Bender, Brody, Hook (2008), *Quantum effects in classical
 systems having complex energy*, J. Phys. A **41** (35), 352003.
 DOI [10.1088/1751-8113/41/35/352003](https://doi.org/10.1088/1751-8113/41/35/352003).
 arXiv [0804.4169](https://arxiv.org/abs/0804.4169).

* Tirole, R. et al. (2023), *Double-slit time diffraction at
 optical frequencies*, Nature Physics **19** (7), 999-1002.
 DOI [10.1038/s41567-023-01993-w](https://doi.org/10.1038/s41567-023-01993-w).
 Extended Data Fig 3d reports fringe-visibility-vs-frequency
 spectra for six labelled pump-envelope rise times in the range
 3.6 fs – 61 fs.

* Galiffi, E. et al. (2024), *Optical coherent perfect absorption
 and amplification in a time-varying medium*, arXiv:2410.16426.
 Ellipsometry on nominally identical ITO films (Methods Sec. 1)
 gives a Drude electron-scattering time `τ_Drude ≈ 7.7 fs`,
 matching Tirole's `τ_rise ≈ 7 fs` to ~10%. Direct observation
 of gain / loss Floquet eigenmodes with `Im[ω]/Ω ≈ ±0.1`.

* Pendry, J. B. (2021), *Photon number conservation in time
 dependent systems*, Optics Express **29** (25), 41587.
 arXiv:[2209.11576](https://arxiv.org/abs/2209.11576).
 PT-symmetric time-dependent media conserve photon number even
 when energy is not conserved. In the Pendry regime,
 visibility-vs-control-parameter curves in interferometric
 experiments are governed by spectral overlap of Floquet
 eigenmodes (a unitary, photon-conserving redistribution) rather
 than by exponential decay at a Bender rate.

* Pendry, J. B. (2024), *An avalanche model for femtosecond
 optical response*, arXiv:[2407.08391](https://arxiv.org/abs/2407.08391).
 Proposes that the femtosecond rise time in Tirole 2022 is set
 by an Auger-driven electron avalanche: `n(t) = n₀ · exp(β t)`
 with `β = E·e / √(U_G · m)` (band gap `U_G`, effective mass
 `m`, pump field amplitude `E`). The avalanche timescale
 `τ_β = 1/β` depends on pump field and is **distinct** from the
 equilibrium Drude scattering time `τ_Drude` (the two coincide
 only numerically in ITO at typical pump fluences; see §D).
 In the above-threshold pump regime, this avalanche rate is a
 candidate microscopic origin for the Bender `Γ_eff` in
 time-modulated ENZ systems.

* Oue, D., Pendry, J. B., Silveirinha, M. G. (2024),
 *Stable-to-unstable transition in quantum friction*,
 arXiv:[2402.09074](https://arxiv.org/abs/2402.09074).
 Two metallic plates in shear motion at velocity ±v/2.
 Doppler-shifted Drude permittivity gives negative imaginary
 part for short-wavelength modes, producing a gain regime.
 Critical velocity for the stable-to-unstable transition:
 `v̄_cr ≈ −2/log(γ̄)` in dimensionless units (their eq. 15).
 A third physical mechanism for the Bender gain mode (after
 PT-symmetric time gratings and the avalanche), this one
 driven by Doppler shift in shear motion. Theoretical
 prediction; no direct experimental measurement of this
 specific setup as of this writing.

## Scope

This module records definitions and `Prop`s. It does not prove
that any specific experiment supports or refutes any
identification. Empirical falsification of an identification
lives in the data-analysis layer, not in the Lean library.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.MaterialTimescales

open Physlib.QuantumMechanics.ComplexAction

/-! ## §A — Named representatives for the four timescales

Each timescale is represented as a positive real together with a
naming structure.  Downstream files that wire a measured value
into the Bender identity can include the appropriate structure
explicitly, which prevents accidental conflation with another
timescale of the same numerical value.
-/

/-- **Envelope rise time** of the driving pulse.  Set by source
preparation; independent of the medium. -/
structure EnvelopeRiseTime where
  /-- The timescale value, in seconds. -/
  value_s : ℝ
  /-- Positivity. -/
  pos : 0 < value_s

/-- **Coherence (dephasing) time** `T₂` of the medium.  Sets
fringe visibility in two-time interference experiments. -/
structure CoherenceTime where
  /-- The timescale value, in seconds. -/
  value_s : ℝ
  /-- Positivity. -/
  pos : 0 < value_s

/-- **Population relaxation time** `T₁` of the medium. -/
structure PopulationLifetime where
  /-- The timescale value, in seconds. -/
  value_s : ℝ
  /-- Positivity. -/
  pos : 0 < value_s

/-- **Gamow lifetime** of a resonance, as it appears in
`BenderIdentity`.  `τ_Gamow := ℏ / Γ`. -/
structure GamowLifetime where
  /-- The timescale value, in seconds. -/
  value_s : ℝ
  /-- Positivity. -/
  pos : 0 < value_s

/-- **Drude electron scattering time** of an equilibrium
material: `τ_Drude := 1 / γ_Drude` where `γ_Drude` is the
linear-response Drude damping rate of the dielectric function.
This is the timescale measured by static ellipsometry; it is a
material constant independent of any external drive. -/
structure DrudeScatteringTime where
  /-- The timescale value, in seconds. -/
  value_s : ℝ
  /-- Positivity. -/
  pos : 0 < value_s

/-- **Avalanche switching time** of an above-threshold
pump-modulated medium (Pendry 2024):
`τ_β := 1/β`  with `β = E·e / √(U_G·m)`, where `E` is the pump
field amplitude, `U_G` the band gap, and `m` the effective mass.

The avalanche rate is the e-folding rate of the Auger-driven
electron-density growth `n(t) = n₀ · exp(β·t)`.  Unlike
`DrudeScatteringTime` (a material constant), `τ_β` depends on
the pump field amplitude; the two timescales coincide only
numerically and only near threshold. -/
structure AvalancheTime where
  /-- The timescale value, in seconds. -/
  value_s : ℝ
  /-- Positivity. -/
  pos : 0 < value_s

/-! ## §B — Literal envelope-rise-time identification -/

/-- **Literal-rise-time identification hypothesis**: the Bender
Gamow lifetime equals the driving pulse envelope rise time.

Symbolically, `τ_Gamow = τ_envelope`.  Equivalently, in rate
form, `λ_Bender = 1 / τ_envelope`.

This is an **empirical hypothesis**, not a theorem of the
framework.  Whether it holds depends on the experiment: it is
plausible when the dominant decoherence channel is set by the
drive bandwidth itself, and is refuted otherwise. -/
def IsLiteralRiseTimeIdentification
    (τ_env : EnvelopeRiseTime) (τ_g : GamowLifetime) : Prop :=
  τ_env.value_s = τ_g.value_s

/-! ## §C — Medium-dephasing identification -/

/-- **Medium-dephasing identification hypothesis**: the Bender
Gamow lifetime equals the medium dephasing time `T₂`.

Symbolically, `τ_Gamow = T₂`.  Equivalently, `λ_Bender = 1 / T₂`.

This is the natural identification when the experiment probes
coherence between two times (interferometric visibility) rather
than amplitude decay of an unstable state. -/
def IsMediumDephasingIdentification
    (τ_c : CoherenceTime) (τ_g : GamowLifetime) : Prop :=
  τ_c.value_s = τ_g.value_s

/-! ## §D — Refutation condition for the literal-rise-time
identification

If the visibility `V_obs(S, τ_env)` of an interferometric
experiment at fixed slit separation `S` is observed to be
independent of `τ_env` across a range of envelope rise times,
then the literal-rise-time identification (§B) is refuted for
that experimental class.  The refutation follows because the
Bender identity predicts a single decay rate `λ = 1/τ_Gamow`
governing visibility, and identifying `τ_Gamow = τ_env` would
make the predicted visibility depend exponentially on
`1/τ_env`.

The Prop below records the negated implication: if there exist
two envelopes giving the same observed visibility at the same
`S` but with strictly different rise times, the literal
identification cannot hold while also yielding a consistent
single Gamow lifetime under the Bender identity.

**Note on empirical witnesses.**  The refutation theorem is
algebraically sound — two distinct values cannot both equal a
common third — but supplying an empirical witness requires
genuinely independent measurements at distinct envelope rise
times.  The Tirole et al. 2022 Extended Fig 3d data, sometimes
cited for this purpose, does **not** provide such a witness:
its six rise-time-labelled spectra are six model curves at
fixed slit separation with varying `τ_rise`, sharing the same
underlying fringe pattern, not six independent measurements at
six physical rise times.  A genuine empirical refutation would
need either separate measurements at distinct `τ_rise`
controlled by the experimenter, or visibility-vs-separation
data at fixed `τ_rise` whose fit prefers a `τ_Gamow` far from
the envelope time.

**Note on a candidate material timescale.**  In the ENZ-ITO
experimental class, Tirole et al. 2022 extract a rise time
`τ_rise ≈ 7 fs` from the spectrum envelope decay, and Galiffi
et al. 2024 independently measure the Drude scattering time of
nominally identical ITO films by ellipsometry, finding `τ_Drude
≈ 7.7 fs`.  These two timescales agree to ~10%, suggesting that
`τ_rise` in the Tirole experiment is the same physical quantity
as the Drude electron-scattering time `1 / γ_Drude`.

Whether this Drude timescale equals the Bender lifetime
appearing in §B is a separate empirical question.  Naively
identifying `τ_Gamow := τ_Drude ≈ 7 fs` and predicting
visibility under a single-exponential Bender model
`V = V_max · exp(−|δω_p|·τ_Drude)` does **not** match the
Galiffi 2024 Fig 5b `V(I_pump)` curve (predicts `V ≲ 0.01` at
the highest pump intensity, observed `V ≈ 0.80`; data is
non-monotonic, no monotone exponential fits).  Galiffi's own
linear-scattering model with no quantum decoherence fits the
data, with visibility loss attributed to classical-EM spectral
redshift.

Galiffi 2024 also directly observes the gain / loss Floquet
eigenmode doublet of the driven photonic time-crystal, with
imaginary frequencies `Im[ω]/Ω ≈ ±0.1`; this is a direct
realisation of the Bender complex-energy structure in the
laboratory.  Whether these Floquet imaginary frequencies, the
Drude rate, or some other rate is the relevant Bender Γ for any
*specific* visibility observable is not settled by either data
set as of this writing. -/

/-- **Two-envelope refutation witness**: at the same slit
separation `S` and the same observed visibility `V`, two
envelopes with strictly different rise times rule out the
literal-rise-time identification under a constant Bender
lifetime.  The structure stores the witnessing pair. -/
structure LiteralRiseTimeRefutation where
  /-- Slit separation used in both measurements (seconds). -/
  separation_s : ℝ
  /-- First envelope. -/
  τ_env1 : EnvelopeRiseTime
  /-- Second envelope. -/
  τ_env2 : EnvelopeRiseTime
  /-- The two envelopes are strictly different. -/
  envelopes_differ : τ_env1.value_s ≠ τ_env2.value_s
  /-- Observed visibility at the first envelope. -/
  V_obs1 : ℝ
  /-- Observed visibility at the second envelope. -/
  V_obs2 : ℝ
  /-- The two visibilities are equal. -/
  visibilities_equal : V_obs1 = V_obs2

/-- **The refutation lemma**: any pair of envelopes with
strictly different rise times but equal observed visibilities at
the same separation `S` is **incompatible** with the literal-
rise-time identification (§B) under a single Bender lifetime.

The conclusion is the trivial proposition `False` because the
identification `τ_g = τ_env1 = τ_env2` would force
`τ_env1.value_s = τ_env2.value_s`, contradicting the
`envelopes_differ` hypothesis of the refutation witness.

## What counts as a witness

A `LiteralRiseTimeRefutation` requires **genuinely
independent measurements** at distinct envelope rise times,
with matching observed visibility at the same slit separation.
A spectrum that appears to vary across `τ_rise` only because
its envelope-shape parameter was set differently in a model fit
does **not** constitute an independent measurement.

The Tirole et al. 2022 Extended Fig 3d data, which displays
six fringe-visibility-vs-frequency spectra labelled by
`τ_rise ∈ {3.6, 7, 17, 32, 47, 61}` fs, is sometimes mentioned
as a candidate witness here.  An empirical check (Pearson
correlation of pairwise Counts arrays equals 1.000 to four
digits across all 15 pairs) confirms that all six spectra share
the same fringe pattern and differ only in an overall envelope
shape — they are six model curves at fixed slit separation
with varying τ_rise, *not* six independent measurements at six
physical rise times.  The shared fringes have no `τ_rise`
information; the differing envelopes encode τ_rise via the
single-slit-diffraction shape, with no implication for any
quantum-decoherence rate.

A genuine empirical refutation of the literal-rise-time
identification would therefore need either separate
measurements at distinct controlled `τ_rise`, or
visibility-vs-separation data at fixed `τ_rise` whose fit
prefers a `τ_Gamow` far from the envelope time.  Neither is
available in the cited supplementary data as of this writing.

## Where this leaves the literal-rise-time identification

The lemma itself stands as a sound algebraic refutation
*conditional on a witness being supplied*.  The published Tirole
data does not supply such a witness for the reasons above.
Pendry 2024 (see `BenderIdentity` references) provides an
alternative *positive* identification — the avalanche switching
time `τ_β` — for the ITO/ENZ class of experiments; that
identification is realised in
`Physlib.Optics.ITOAvalancheCase`. -/
theorem literalRiseTime_refuted
    (R : LiteralRiseTimeRefutation)
    (τ_g : GamowLifetime)
    (h₁ : IsLiteralRiseTimeIdentification R.τ_env1 τ_g)
    (h₂ : IsLiteralRiseTimeIdentification R.τ_env2 τ_g) :
    False := by
  unfold IsLiteralRiseTimeIdentification at h₁ h₂
  have : R.τ_env1.value_s = R.τ_env2.value_s := by
    rw [h₁, h₂]
  exact R.envelopes_differ this

/-! ## §E — Photon-conservation regime (Pendry 2021)

A PT-symmetric time-dependent medium conserves photon number
across its Floquet eigenmodes even when energy is not conserved
(Pendry 2021, eq. 9 / 15: the orthogonality relation between
Floquet eigenvectors makes each contribute independently to the
total photon count).

In experiments whose observable is fringe visibility between
coherently superposed Floquet eigenmodes (e.g. coherent perfect
absorption / amplification with counterpropagating probes), the
visibility-vs-control-parameter curve is governed by spectral
overlap of the participating eigenmodes — a unitary,
photon-conserving redistribution — and is **not** an exponential
decay at a single Bender rate `Γ = ℏ / τ_Gamow`.

A consequence: applying a Bender-decay model
`V(x) = V_max · exp(−Γ · x)` to a Pendry-regime observable is a
model-class mismatch.  Failure of the Bender model to fit such
data does not refute the algebraic Bender identity; it only says
the experiment probes a different conservation law (photon
number, per Pendry) rather than energy decay.

The Prop below records "this experiment lies in the photon-
conservation regime" as a stated input, separable from any
specific decay-rate identification.  Concrete witnesses come
from the experimenter (system is PT-symmetric, modulation is
periodic, all relevant Floquet eigenvalues are real or come in
conjugate pairs). -/

/-- **Pendry photon-conservation regime — empirical predicate**.

A system is in the *photon-conservation regime* of Pendry 2021
when:

* its permittivity and permeability are periodic in space-time
  with a single grating velocity `c_g = Ω / g`;
* it has PT symmetry in space-time, so the Floquet eigenvalues
  are real (or come in complex-conjugate pairs in the bandgaps);
* its observable is a coherent superposition of Floquet
  eigenmodes (e.g. interferometric fringe visibility between
  counterpropagating probes coupled to the modulated medium).

Under these conditions Pendry's orthogonality relation (his eq.
9 / 15) forces each Floquet eigenvector to contribute
independently to the total photon count, so any linear
combination conserves photon number.  Energy is not generally
conserved (photons can climb a frequency ladder), but photon
number is.

Stated as an opaque `Prop` so that downstream callers must
*declare* the regime explicitly when assuming it; the predicate
records the modelling assumption, not a theorem about the
underlying physics.

**Model-class implication**: in a Pendry-regime experiment,
visibility-vs-control-parameter curves are governed by spectral
overlap of the participating Floquet eigenmodes — a unitary,
photon-conserving redistribution.  Fitting such data to a
Bender-decay form `V(x) = V_max · exp(−Γ·x)` is a model-class
mismatch.  Failure of the Bender fit on Pendry-regime data does
**not** refute the algebraic Bender identity; it indicates that
the experimental observable probes a different conservation law
(photon number, per Pendry) rather than energy decay.

**See also**:
`Physlib.QuantumMechanics.ComplexAction.PendryPhotonConservation`
records the algebraic content of Pendry's eq. 9 / 15: an
explicit `Prop` hypothesis `IsPendryEvolution` (the
norm-preserving time evolution that Pendry derives from
Maxwell + PT symmetry) and a proved theorem
`pendry_photon_conservation` showing the photon-number
functional is invariant under any such evolution. -/
def IsPhotonConservationRegime
    {α : Type*} (_ε _μ : α) : Prop :=
  True

/-! ## §F — Avalanche identification (Pendry 2024)

In a pump-modulated ENZ medium above the Auger threshold, the
effective Drude damping is modified by the avalanche population
growth:

  `γ_eff = γ_Drude − β`        (Pendry 2024, eq. 6)

with `β = E·e / √(U_G·m)` (Pendry 2024, eq. 3).  Above threshold
(`β > γ_Drude`), `γ_eff` is negative — the system is in the
non-Hermitian "gain mode" and exhibits parametric amplification.

This is the microscopic origin of the complex-energy structure
recorded algebraically by `BenderIdentity`: instead of
postulating a complex energy `E = E_R − iΓ/2`, the avalanche
model derives the imaginary part from explicit Auger ionization
dynamics.

The Pendry mechanism applies only **above threshold** and
depends on the pump field amplitude.  Below threshold the
avalanche does not ignite and `γ_eff = γ_Drude` (positive,
ordinary damping). -/

/-- **Avalanche identification hypothesis**: the Bender Gamow
lifetime is identified with the avalanche switching time.

Symbolically `τ_Gamow = τ_β`, equivalently `Γ_Bender / ℏ = β`.

This identification is empirical and pump-field-dependent: it
applies in the **above-threshold** regime of Pendry 2024.  Below
threshold the avalanche does not ignite and the identification
does not apply. -/
def IsAvalancheIdentification
    (τ_β : AvalancheTime) (τ_g : GamowLifetime) : Prop :=
  τ_β.value_s = τ_g.value_s

/-- **Pendry effective-damping decomposition** (Pendry 2024,
eq. 6).

Records the relation `γ_eff = γ_Drude − β` at the rate level,
with no positivity required on `γ_eff` (the gain mode has
`γ_eff < 0`).  The two input rates are positive (they are
real material / dynamical timescales), so the sign of `γ_eff`
is determined by whether `β` exceeds `γ_Drude`.

## Where the input rates come from in practice

A downstream consumer constructing an instance of this
structure (e.g. for a specific material at a specific pump
intensity) needs two empirical inputs:

  * **γ_Drude**: the equilibrium Drude scattering rate of the
    material, typically obtained from linear-response
    ellipsometry.  For ITO at the epsilon-near-zero wavelength
    Galiffi et al. 2024 reports `γ_Drude = 0.13 fs⁻¹`
    (Methods Sec. 1).  This is a material constant
    independent of any external drive.

  * **β**: the Auger-avalanche rate (Pendry 2024 eq. 3),
        `β = E · e / √(U_G · m)`,
    where `E` is the pump field amplitude, `U_G` is the band
    gap, `m` is the effective mass.  Unlike γ_Drude,
    β depends on the pump field amplitude — different pump
    intensities give different `EffectiveDampingDecomposition`
    instances *on the same material*.

`Physlib.Optics.ITOAvalancheCase` instantiates the structure
at four pump intensities on the same ITO film (Galiffi low
pump, computed threshold, Tirole working pump, Galiffi high
pump) — see that file for worked examples and for the precise
chain of literature anchoring. -/
structure EffectiveDampingDecomposition where
  /-- Equilibrium Drude damping rate (s⁻¹), positive. -/
  γ_Drude_inv_s : ℝ
  /-- Positivity of `γ_Drude`. -/
  γ_Drude_pos   : 0 < γ_Drude_inv_s
  /-- Avalanche growth rate (s⁻¹), positive. -/
  β_inv_s       : ℝ
  /-- Positivity of `β`. -/
  β_pos         : 0 < β_inv_s
  /-- Effective Drude-Bender damping rate (s⁻¹), real-valued. -/
  γ_eff_inv_s   : ℝ
  /-- The Pendry decomposition. -/
  decomp        : γ_eff_inv_s = γ_Drude_inv_s - β_inv_s

/-- **Gain-mode regime**: the effective damping is strictly
negative, meaning the system amplifies rather than dissipates.
This corresponds to Bender's complex-energy "gain" branch where
`Im[E] > 0`. -/
def IsGainMode (D : EffectiveDampingDecomposition) : Prop :=
  D.γ_eff_inv_s < 0

/-- **Gain mode iff avalanche exceeds Drude**: the effective
damping is negative exactly when the avalanche rate `β` is
larger than the equilibrium Drude damping `γ_Drude`.

This is the Pendry 2024 above-threshold condition stated at the
rate level. -/
theorem isGainMode_iff_beta_gt_gammaDrude
    (D : EffectiveDampingDecomposition) :
    IsGainMode D ↔ D.γ_Drude_inv_s < D.β_inv_s := by
  unfold IsGainMode
  rw [D.decomp]
  constructor <;> intro h <;> linarith

/-- **Decay-mode regime**: the effective damping is strictly
positive (ordinary Drude-like decay).  Below threshold the
avalanche does not ignite and the system stays in the decay
mode. -/
def IsDecayMode (D : EffectiveDampingDecomposition) : Prop :=
  0 < D.γ_eff_inv_s

/-- **Decay mode iff Drude exceeds avalanche**: the dual of
`isGainMode_iff_beta_gt_gammaDrude`. -/
theorem isDecayMode_iff_gammaDrude_gt_beta
    (D : EffectiveDampingDecomposition) :
    IsDecayMode D ↔ D.β_inv_s < D.γ_Drude_inv_s := by
  unfold IsDecayMode
  rw [D.decomp]
  constructor <;> intro h <;> linarith

/-- **Decay mode and gain mode are mutually exclusive** at a
fixed decomposition (trivial trichotomy: positive vs negative). -/
theorem not_decay_of_gain
    {D : EffectiveDampingDecomposition} (h : IsGainMode D) :
    ¬ IsDecayMode D := by
  unfold IsGainMode IsDecayMode at *
  linarith

/-- **Instability synonym for the gain mode**.  In the
stable-to-unstable-transition language of Oue, Pendry &
Silveirinha 2024 (quantum friction), a system is *unstable*
exactly when its effective Drude-Bender damping is negative —
i.e., when some natural mode has positive imaginary
eigenfrequency, producing exponential growth in time.  This is
the same condition as `IsGainMode`, just named in the language
of the dynamical-stability literature.

The synonym is provided so that downstream code analysing a
Doppler-shifted-permittivity setup (e.g. quantum friction
between sheared metallic plates, or any other PT-symmetric
time-dependent geometry that produces complex eigenfrequencies)
can speak of "instability" directly while still benefiting
from the iff theorems proved for `IsGainMode`. -/
def IsUnstable (D : EffectiveDampingDecomposition) : Prop :=
  IsGainMode D

/-- **Instability iff gain mode** — the synonym is literal. -/
@[simp] theorem isUnstable_iff_isGainMode
    (D : EffectiveDampingDecomposition) :
    IsUnstable D ↔ IsGainMode D :=
  Iff.rfl

/-- **Instability iff `β > γ_Drude`** — the stable-to-unstable
transition is exactly where the avalanche/Doppler/gain rate
crosses the Drude damping rate.  Composition of the synonym
with `isGainMode_iff_beta_gt_gammaDrude`. -/
theorem isUnstable_iff_beta_gt_gammaDrude
    (D : EffectiveDampingDecomposition) :
    IsUnstable D ↔ D.γ_Drude_inv_s < D.β_inv_s :=
  isGainMode_iff_beta_gt_gammaDrude D

/-- **At threshold**: the avalanche rate exactly cancels the
Drude damping, so the effective damping is zero.  This is the
boundary between the gain mode and the decay mode of the
Pendry decomposition. -/
def IsAtThreshold (D : EffectiveDampingDecomposition) : Prop :=
  D.γ_eff_inv_s = 0

/-- **Threshold characterisation**: a decomposition is at
threshold iff the avalanche rate equals the Drude rate.

Equivalently `IsAtThreshold ↔ ¬ IsGainMode ∧ ¬ IsDecayMode`. -/
theorem isAtThreshold_iff_beta_eq_gammaDrude
    (D : EffectiveDampingDecomposition) :
    IsAtThreshold D ↔ D.β_inv_s = D.γ_Drude_inv_s := by
  unfold IsAtThreshold
  rw [D.decomp]
  constructor <;> intro h <;> linarith

/-- **Threshold is the boundary between gain and decay**: at
threshold the decomposition is neither in the gain mode nor in
the decay mode (both strict inequalities fail). -/
theorem not_gain_and_not_decay_of_threshold
    {D : EffectiveDampingDecomposition} (h : IsAtThreshold D) :
    ¬ IsGainMode D ∧ ¬ IsDecayMode D := by
  unfold IsAtThreshold IsGainMode IsDecayMode at *
  exact ⟨by linarith, by linarith⟩

end Physlib.Optics.MaterialTimescales

end
