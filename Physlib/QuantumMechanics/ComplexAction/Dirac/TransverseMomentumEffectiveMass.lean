/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.SpinDensityFunctionalOperators
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.CondensedMatter.TightBindingChain.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

meta import Zil

/-!
# Transverse momentum as effective mass — Cruz–Carrillo-Bastos–Villavicencio 2020

Cruz, Carrillo-Bastos, and Villavicencio, *Time diffraction and Zitterbewegung of
two-dimensional massless Dirac excitations*, Phys. Rev. B **101** (2020) 115415.  A
quantum-shutter study of graphene-type massless Dirac matter whose central claim is
structural: at fixed transverse momentum `k_y`, the two-dimensional *massless* mode
behaves as a one-dimensional *massive* one — `k_y` acts as the mass, the Zitterbewegung
beats at `Ω_Z = 2k_y v_F`, the diffraction-in-time rides at `Ω_D = (k − k_y)v_F`, both
vanish at normal incidence (`k_y = 0`), and the effective mass is *tunable by the
incidence angle*.

Formalized here (units `v_F = 1` at the operator level; `v_F` explicit in the scalar
frequency identities):

* **§A — the identification is a spin rotation.**  The graphene mode Hamiltonian
  `H = k_x σ_x + k_y σ_y` is carried by the rotation `U = (1 − iσ_x)/√2` onto
  `k_x σ_x + k_y σ_z` — exactly the repository's one-dimensional massive Dirac form
  (`KleinGordonDiracFactorization.diracHamiltonian`) with mass `k_y`
  (`transverse_momentum_is_mass`).  The paper's "effective mass" is a theorem: the two
  Hamiltonians are the same operator.
* **§B — the trembling operator is the transverse momentum.**  The Zitterbewegung part
  of the velocity, `H·σ_x − k_x·1`, equals `k_y·(σ_y σ_x)` exactly
  (`transverseTrembling_eq`) and vanishes iff `k_y = 0`
  (`transverseTrembling_eq_zero_iff`) — the two-dimensional face of the
  trembling-equals-mass identity `zitterVelocity1_oneD`, and the reason the paper sees
  no Zitterbewegung and a straight mean trajectory at normal incidence.
* **§C — the beat frequency is the effective rest gap.**  The paper's
  `Ω_Z = 2k_y v_F` is the rest-frame Zitterbewegung frequency of the effective mass
  `m* = ℏk_y/v_F` (`cruz_beat_is_zitterbewegung`, through the trinity's
  `zitterbewegung_rest_eq_two_compton` with `c := v_F`), and the crossover with the
  diffraction-in-time frequency `Ω_D = (k − k_y)v_F` happens exactly at `k = 3k_y`
  (`frequency_crossover_iff`), i.e. `sin φ = 1/3`, `tan φ = 1/√8`
  (`crossover_tan`) — the paper's `φ = arctan(1/√8)`.
* **§D — the external input as an experimental dial.**  Every effective mass
  `0 < m ≤ k` is realized by some incidence angle (`effectiveMass_dial`,
  `k·sin φ = m` at `φ = arcsin(m/k)`).  The covariant no-go proved that no internal
  equation selects the mass value; in Dirac matter the selection is made by the
  *preparation* — the incidence angle is the external input of
  `dilation_covariant_determination_absurd` made into a laboratory knob, and the
  Compton-clock anchor for the mode is set by the experimenter.
* **§E — the CAT/EPT link through Unruh.**  The displacement entropy of the effective
  mass is exactly `2πk_B·k_y·Δx` — the transverse momentum is the Verlinde entropy
  gradient (`transverseMomentum_is_entropy_gradient`); the Unruh temperature at the
  mode's invariant speed matches the transverse-mass clock exactly at `a = k_y·v_F²`
  (`effectiveUnruh_matches_clock`); and the statement-12 chain instantiates as the
  mode's entropic inertia (`effectiveNewton_from_unruh`).  The speed slot is occupied
  by theorem, not analogy.
* **§F — the speed isolated, the force label eliminated.**  `v_F = Ω_Z/(2k_y)` is an
  output (`fermiVelocity_isolated`); mass and matching acceleration restate in
  observables; and the second law is stated with the force wrapper unfolded — "force"
  names the composite `T·ΔS/Δx`, adding nothing (`entropic_law_observables_only`).
* **§G — the inverse-square law.**  The mode's holographic coupling is an output
  (`modeCoupling_isolated`, `G* = Ω_Z³/(8ℏk_y⁵)`); the statement-13 composite
  instantiates in observables (`inverseSquare_law_observables_only`); with the mode's
  own coupling the composite is `ℏ`-free: `M·v_F²/(k_y·R²)` (`inverseSquare_cascade`).
* **§H — holographically re-evaluated.**  With `G` in area-per-bit form the screen's
  `R²` cancels the inverse square's for any bit count — distance enters Newton's law
  only through the screen's information content
  (`inverseSquare_R_only_through_bits`); the mode's count is the Compton tiling
  `N* = 4π(k_yR)²` (`modeBitCount_comptonCells`), and substituting it re-derives the
  cascade (`inverseSquare_holographic`).
* **§I — the speed decomposed to the lattice.**  The tight-binding chain's proven
  spectrum has band slope `2ta·sin(ka)` (`bandProfile_hasDerivAt`); at the band centre
  the slope is exactly `2ta` — `v_F` is twice the hopping times the spacing, not a
  primitive (`fermiVelocity_decomposed`), and the beats read the lattice:
  `Ω_Z = 4·t·a·k_y` (`beat_reads_lattice`).

**Honest layering, with its search.**  Formalized: the effective-mass identification,
the trembling identity, the frequency dictionary, the dial, the Unruh/entropy chain,
the observables-only restatements, the inverse-square law with its holographic
anatomy, and the lattice decomposition of the speed.  Not formalized: the
quantum-shutter *solution* itself — the Laplace/Bromwich inversion, the Bessel-series
spinors (paper Eqs. 4–10), the diffraction-in-time and beat asymptotics (Eqs. 12–14)
with their `t^{−1/2}` decay, and the Lommel-function form.  Searched before fencing:
grep `moshinsky`/`diffraction in time`/`quantum shutter` finds only the unrelated
Dirac-oscillator citation in `InvertedDiracOscillator`; the repository has no Bessel
`J_n` infrastructure to weld a shutter solution to.  The `t^{−1/2}` transient envelope
is adjacent to the temporal double-slit arc (`Physlib/Optics/`), which carries the
CAT/EPT time-slit programme this paper's diffraction-in-time face would extend.
-/

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass

open Matrix
open Physlib.QuantumMechanics.SpinDensityFunctionalOperators
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ### §A — the effective-mass identification is a spin rotation -/

/-- **The graphene mode Hamiltonian** at wave vector `(k_x, k_y)` (units `v_F = 1`):
`H = k_x σ_x + k_y σ_y` — the two-dimensional massless Dirac form, paper Eq. (1) at one
momentum mode, valley `η = +1`. -/
def grapheneModeHamiltonian (kx ky : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (kx : ℂ) • pauliX + (ky : ℂ) • pauliY

/-- **The massless 2-D dispersion**: `H² = (k_x² + k_y²)·1` — the mass shell of the
would-be massive system, with `k_y` in the mass slot. -/
theorem grapheneModeHamiltonian_sq (kx ky : ℝ) :
    grapheneModeHamiltonian kx ky * grapheneModeHamiltonian kx ky
      = ((kx ^ 2 + ky ^ 2 : ℝ) : ℂ) • 1 := by
  unfold grapheneModeHamiltonian
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [pauliX_sq, pauliY_sq, pauliX_mul_pauliY, pauliY_mul_pauliX]
  push_cast
  rw [smul_smul, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  module

/-- `σ_z·σ_x = i·σ_y` — the cyclic Pauli product the intertwining needs. -/
theorem pauliZ_mul_pauliX : pauliZ * pauliX = Complex.I • pauliY := by
  unfold pauliZ pauliX pauliY
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The spin rotation** `W = 1 − iσ_x` — the (unnormalized) rotation by `π/2` about
the `x` axis, the paper's §II spin-rotation extension specialized to the axis that
carries `σ_y ↦ σ_z`.  Unnormalized like the repository's `fwOperator`; its modulus is
the scalar `2`. -/
def spinRotationX : Matrix (Fin 2) (Fin 2) ℂ := 1 - Complex.I • pauliX

/-- **The modulus of the rotation**: `W·W̄ = 2·1` with `W̄ = 1 + iσ_x` — a positive
scalar, so `W` is invertible; the normalized rotation is `W/√2`. -/
theorem spinRotationX_modulus :
    spinRotationX * (1 + Complex.I • pauliX) = (2 : ℂ) • 1 := by
  unfold spinRotationX pauliX
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring_nf

/-- **The transverse momentum is the mass** (paper §II): the spin rotation intertwines
the two-dimensional massless mode Hamiltonian `k_xσ_x + k_yσ_y` with the
one-dimensional massive Dirac form `k_xσ_x + k_yσ_z`,

  `W·H_graphene = H_massive·W`,

with `k_y` in the mass slot — the same intertwining shape as the exact Foldy–Wouthuysen
reduction (`fw_intertwine`).  The "effective mass" is not an analogy: the two
Hamiltonians are the same operator up to the invertible rotation, so every mass theorem
of the repository (rest gap, trembling identity, connection strength, contour system)
instantiates at `m = k_y`. -/
theorem transverse_momentum_is_mass (kx ky : ℝ) :
    spinRotationX * grapheneModeHamiltonian kx ky
      = ((kx : ℂ) • pauliX + (ky : ℂ) • pauliZ) * spinRotationX := by
  unfold spinRotationX grapheneModeHamiltonian pauliX pauliY pauliZ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    (try simp only [Complex.I_sq]) <;>
    (try ring)

/-! ### §B — the trembling operator is the transverse momentum -/

/-- **The transverse trembling operator**: the Zitterbewegung part of the velocity
along `x`, `η = H·σ_x − k_x·1` — the drift `k_x` subtracted from `H` times the velocity
operator `σ_x`, mirroring `zitterVelocity1`. -/
def transverseTrembling (kx ky : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  grapheneModeHamiltonian kx ky * pauliX - (kx : ℂ) • 1

/-- **The trembling operator equals the transverse momentum times `σ_yσ_x`** — Cruz's
central claim as an operator identity: everything that trembles is `k_y`.  The
two-dimensional face of `zitterVelocity1_oneD` (`η₁ = m·βα₁`) with `m = k_y`. -/
theorem transverseTrembling_eq (kx ky : ℝ) :
    transverseTrembling kx ky = (ky : ℂ) • (pauliY * pauliX) := by
  unfold transverseTrembling grapheneModeHamiltonian
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, pauliX_sq]
  abel

/-- **No transverse momentum, no Zitterbewegung**: the trembling operator vanishes
exactly at normal incidence `k_y = 0` — the paper's Fig. 4(b) flat profile and the
straight mean trajectory `⟨x⟩ = v_F t/2` at `φ = 0`, and the reason diffraction in time
is absent for the truly massless one-dimensional case. -/
theorem transverseTrembling_eq_zero_iff (kx ky : ℝ) :
    transverseTrembling kx ky = 0 ↔ ky = 0 := by
  rw [transverseTrembling_eq, pauliY_mul_pauliX]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simp [pauliZ, Matrix.smul_apply] at h00
    exact_mod_cast h00
  · intro h
    rw [h]
    simp

/-! ### §C — the beat frequency is the effective rest gap -/

/-- **The effective Compton frequency of the transverse mass**: for
`m* = ℏk_y/v_F`, the Compton clock ticks at `ω_C = k_y·v_F`. -/
theorem effectiveCompton_frequency (ky vF ħ : ℝ) (hvF : vF ≠ 0) (hħ : ħ ≠ 0) :
    comptonFrequency (ħ * ky / vF) vF ħ = ky * vF := by
  unfold comptonFrequency
  field_simp
  try ring

/-- **The paper's beat frequency `Ω_Z = 2k_y v_F` is the rest Zitterbewegung frequency
of the effective mass** — the trinity's `ω_Z = 2ω_C` with `c := v_F` and
`m := ℏk_y/v_F`.  The terahertz quantum beats of the graphene shutter are the same
Compton-scale trembling as the vacuum electron's, scaled by the effective mass the
transverse momentum provides. -/
theorem cruz_beat_is_zitterbewegung (ky vF ħ : ℝ)
    (hky : 0 ≤ ky) (hvF : 0 < vF) (hħ : 0 < ħ) :
    zitterbewegungFrequency 0 (ħ * ky / vF) vF ħ = 2 * (ky * vF) := by
  rw [zitterbewegung_rest_eq_two_compton _ _ _ (by positivity)]
  rw [effectiveCompton_frequency ky vF ħ hvF.ne' hħ.ne']

/-- **The diffraction-in-time frequency** `Ω_D = (k − k_y)v_F` of the paper's
Eq. (12). -/
def timeDiffractionFrequency (k ky vF : ℝ) : ℝ := (k - ky) * vF

/-- **The frequency crossover `Ω_Z = Ω_D` happens exactly at `k = 3k_y`** — the paper's
Fig. 5(a) crossing condition. -/
theorem frequency_crossover_iff (k ky vF : ℝ) (hvF : vF ≠ 0) :
    2 * (ky * vF) = timeDiffractionFrequency k ky vF ↔ k = 3 * ky := by
  unfold timeDiffractionFrequency
  constructor
  · intro h
    have h2 : (2 * ky) * vF = (k - ky) * vF := by
      ring_nf
      ring_nf at h
      linarith [h]
    have h3 := mul_right_cancel₀ hvF h2
    linarith
  · intro h
    rw [h]
    ring

/-- **The crossover incidence angle satisfies `tan φ = 1/√8`** (paper Fig. 5): at the
crossing, `k_y = k/3`, i.e. `sin φ = 1/3`, and for a forward-moving mode
(`cos φ > 0`) this is the paper's `φ = arctan(1/√8)`. -/
theorem crossover_tan (φ : ℝ) (hsin : Real.sin φ = 1 / 3) (hcos : 0 < Real.cos φ) :
    Real.tan φ = 1 / Real.sqrt 8 := by
  have hpyth := Real.sin_sq_add_cos_sq φ
  have hcos2 : Real.cos φ ^ 2 = 8 / 9 := by
    rw [hsin] at hpyth
    nlinarith [hpyth]
  have hs8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hs8nn : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hfactor : (Real.cos φ - Real.sqrt 8 / 3) * (Real.cos φ + Real.sqrt 8 / 3) = 0 := by
    nlinarith [hcos2, hs8]
  have hcosval : Real.cos φ = Real.sqrt 8 / 3 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · nlinarith [hcos, hs8nn]
  rw [Real.tan_eq_sin_div_cos, hsin, hcosval]
  field_simp

/-! ### §D — the external input as an experimental dial -/

/-- **Every effective mass up to `k` is realized by an incidence angle**: for
`0 < m ≤ k` there is `φ ∈ [0, π/2]` with `k·sin φ = m`.  The covariant no-go
(`dilation_covariant_determination_absurd`) proved that no internal equation of the
scale-covariant kinematics selects the mass value; in Dirac matter the selection is
made by the *preparation* — the incidence angle is the external input made into a
laboratory knob, and the mode's Compton-clock anchor is set by the experimenter. -/
theorem effectiveMass_dial (k m : ℝ) (h0 : 0 < m) (hmk : m ≤ k) :
    ∃ φ : ℝ, 0 ≤ φ ∧ φ ≤ Real.pi / 2 ∧ k * Real.sin φ = m := by
  have hk : 0 < k := lt_of_lt_of_le h0 hmk
  refine ⟨Real.arcsin (m / k), Real.arcsin_nonneg.mpr (by positivity),
    Real.arcsin_le_pi_div_two _, ?_⟩
  rw [Real.sin_arcsin
    (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (by positivity))
    ((div_le_one hk).mpr hmk)]
  field_simp

/-! ### §E — the CAT/EPT link: Unruh temperature and the entropic inertia of the mode -/

/-- **The transverse momentum is the Verlinde entropy gradient**: the displacement
entropy of the effective mass `m* = ℏk_y/v_F`, with the mode's invariant speed `v_F` in
the light-speed slot, is

  `ΔS = 2π·k_B·k_y·Δx`

— every parameter cancels except the transverse momentum.  Each unit of displacement
costs `2πk_B` of entropy per unit `k_y`: what the shutter's transverse momentum stores
is displacement entropy, the CAT/EPT reading of the Cruz effective mass.  The speed
slot is occupied by theorem, not analogy: every identity in this arc is quantified over
the speed, exactly as the condensate results (`zbwAmplitude_mul_frequency`) carry
`λ_C·ω_C = c` at an arbitrary carrier speed. -/
theorem transverseMomentum_is_entropy_gradient (ℏ kB ky vF Δx : ℝ)
    (hℏ : ℏ ≠ 0) (hvF : vF ≠ 0) :
    Physlib.Thermodynamics.verlindeDisplacementEntropy ℏ kB (ℏ * ky / vF) vF Δx
      = 2 * Real.pi * kB * ky * Δx := by
  unfold Physlib.Thermodynamics.verlindeDisplacementEntropy
  field_simp
  try ring

/-- **The Unruh temperature at the mode's invariant speed reads the transverse-mass
clock exactly at the Compton acceleration `a = k_y·v_F²`** — which is `v_F·Ω_Z/2` in
terms of the paper's beat frequency.  The next instance of the Unruh–clock matching
pattern (`unruh_eq_comptonTemperature_iff`, whose Yukawa and topological instances live
in `HiggsClockThreeOrigins`), with the matching acceleration set by the incidence
angle. -/
theorem effectiveUnruh_matches_clock {ℏ kB ky vF a : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hvF : 0 < vF) :
    Physlib.Thermodynamics.unruhTemperature ℏ kB vF a
        = Physlib.Thermodynamics.comptonTemperature (ℏ * ky / vF) vF kB
      ↔ a = ky * vF ^ 2 := by
  rw [Physlib.Thermodynamics.unruh_eq_comptonTemperature_iff hℏ hkB hvF]
  rw [show ℏ * ky / vF * vF ^ 3 / ℏ = ky * vF ^ 2 from by
    have h1 := hℏ.ne'
    have h2 := hvF.ne'
    field_simp
    try ring]

/-- **The entropic second law for the graphene quasiparticle**: `F = m*·a` from the
Unruh temperature at the mode's invariant speed and the transverse-momentum
displacement entropy — the CAT/EPT thermodynamic force law (the ledger's statement 12,
`newton_second_law_from_verlinde_unruh`) instantiated at the effective mass.  The
mode's inertia is entropic, its source is the transverse momentum, and the whole chain
— entropy gradient, matching acceleration, inertia — is dialed by the incidence
angle. -/
theorem effectiveNewton_from_unruh {ℏ kB ky vF Δx a : ℝ}
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hky : 0 < ky) (hvF : 0 < vF) (hΔx : 0 < Δx) :
    Physlib.Thermodynamics.verlindeEntropicForce
        (Physlib.Thermodynamics.unruhTemperature ℏ kB vF a)
        (Physlib.Thermodynamics.verlindeDisplacementEntropy ℏ kB (ℏ * ky / vF) vF Δx)
        Δx
      = (ℏ * ky / vF) * a :=
  Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh hℏ hkB (by positivity)
    hvF hΔx

/-! ### §F — the speed isolated, and the force label eliminated -/

/-- **The invariant speed is an output**: solving the beat relation `Ω_Z = 2k_y·v_F`
for the speed gives `v_F = Ω_Z/(2k_y)` — the mode's invariant speed is the ratio of two
observables, the beat frequency and the transverse momentum.  Once the clock is read,
nothing about the speed is an input. -/
theorem fermiVelocity_isolated (ky vF Ω : ℝ) (hky : ky ≠ 0)
    (hΩ : Ω = 2 * (ky * vF)) : vF = Ω / (2 * ky) := by
  rw [hΩ]
  field_simp

/-- **The effective mass from observables only**: eliminating the speed,
`m* = 2ℏk_y²/Ω_Z` — the mass is the transverse momentum squared over the beat
frequency, times `2ℏ`. -/
theorem effectiveMass_isolated (ℏ ky vF Ω : ℝ) (hky : ky ≠ 0) (hvF : vF ≠ 0)
    (hΩ : Ω = 2 * (ky * vF)) : ℏ * ky / vF = 2 * ℏ * ky ^ 2 / Ω := by
  rw [hΩ]
  field_simp
  try ring

/-- **The Unruh-matching acceleration from observables only**: `a* = Ω_Z²/(4k_y)`. -/
theorem matchingAcceleration_isolated (ky vF Ω : ℝ) (hky : ky ≠ 0)
    (hΩ : Ω = 2 * (ky * vF)) : ky * vF ^ 2 = Ω ^ 2 / (4 * ky) := by
  rw [hΩ]
  field_simp
  try ring

/-- **The entropic second law in mode observables only, with the force label
eliminated.**  "Force" is not a formalizable concept: `verlindeEntropicForce` is
definitionally the composite `T·ΔS/Δx`, so the law's entire formal content is an
identity between two composites —

  temperature × entropy gradient = mass × acceleration

— and the word "force" names either side, adding nothing.  Stated here without the
force wrapper and with the speed eliminated (`v_F = Ω/(2k_y)`, `m* = 2ℏk_y²/Ω`):
every quantity is an observable of the mode. -/
theorem entropic_law_observables_only (ℏ kB ky Ω Δx a : ℝ)
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hky : 0 < ky) (hΩ : 0 < Ω) (hΔx : 0 < Δx) :
    Physlib.Thermodynamics.unruhTemperature ℏ kB (Ω / (2 * ky)) a
        * Physlib.Thermodynamics.verlindeDisplacementEntropy ℏ kB
            (2 * ℏ * ky ^ 2 / Ω) (Ω / (2 * ky)) Δx / Δx
      = (2 * ℏ * ky ^ 2 / Ω) * a := by
  have h := Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh
    (ℏ := ℏ) (kB := kB) (m := 2 * ℏ * ky ^ 2 / Ω) (c := Ω / (2 * ky))
    (Δx := Δx) (a := a) hℏ hkB (by positivity) (by positivity) hΔx
  unfold Physlib.Thermodynamics.verlindeEntropicForce at h
  exact h

/-! ### §G — the inverse-square law at the effective mass, coupling included -/

/-- **The mode's holographic coupling is an output**: the anchor cascade `G = ℏc/m²`
instantiated at the effective mass and the mode's invariant speed gives

  `G* = v_F³/(ℏk_y²) = Ω_Z³/(8ℏk_y⁵)`

— the coupling determined by the clock and the transverse momentum, exactly as the
anchor chain derives `G` from one scale (`newtonG_isolated`: the holographic count is
the unique bit count compatible with Newton's form). -/
theorem modeCoupling_isolated (ℏ ky vF Ω : ℝ) (hℏ : ℏ ≠ 0) (hky : ky ≠ 0)
    (hvF : vF ≠ 0) (hΩ : Ω = 2 * (ky * vF)) :
    ℏ * vF / (ℏ * ky / vF) ^ 2 = Ω ^ 3 / (8 * ℏ * ky ^ 5) := by
  rw [hΩ]
  field_simp
  try ring

/-- **The inverse-square composite at the effective mass, in observables only** — the
ledger's statement-13 chain (`newton_law_of_gravity_from_verlinde`) instantiated at
`m* = 2ℏk_y²/Ω` and the mode's invariant speed, with the force wrapper unfolded:

  screen temperature × entropy gradient = `G·M·m*/R²`.

The inverse square in `R` is the geometric face of the screen; the mass slot is filled
by observables; "force" names the composite. -/
theorem inverseSquare_law_observables_only (M G ℏ kB ky Ω R Δx : ℝ)
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hky : 0 < ky) (hΩ : 0 < Ω) (hR : 0 < R)
    (hΔx : 0 < Δx) :
    Physlib.Thermodynamics.verlindeGravityTemperature M G ℏ (Ω / (2 * ky)) R kB
        * Physlib.Thermodynamics.verlindeDisplacementEntropy ℏ kB
            (2 * ℏ * ky ^ 2 / Ω) (Ω / (2 * ky)) Δx / Δx
      = G * M * (2 * ℏ * ky ^ 2 / Ω) / R ^ 2 := by
  have h := Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde
    (M := M) (G := G) (ℏ := ℏ) (c := Ω / (2 * ky)) (R := R) (kB := kB)
    (m := 2 * ℏ * ky ^ 2 / Ω) (Δx := Δx) hℏ hkB (by positivity) hR hΔx
  unfold Physlib.Thermodynamics.verlindeEntropicForce at h
  exact h

/-- **The cascade closed**: with the mode's own holographic coupling in the `G` slot,
the inverse-square composite collapses to

  `M·v_F²/(k_y·R²)`

— `ℏ` cancels completely.  Source mass and screen geometry outside, transverse
momentum inside, no coupling constant left: Newton's inverse square for the
quasiparticle is a reading of one observable, one dialed scale, and geometry. -/
theorem inverseSquare_cascade (M ℏ ky vF R : ℝ) (hℏ : ℏ ≠ 0) (hky : ky ≠ 0)
    (hvF : vF ≠ 0) (hR : R ≠ 0) :
    (ℏ * vF / (ℏ * ky / vF) ^ 2) * M * (ℏ * ky / vF) / R ^ 2
      = M * vF ^ 2 / (ky * R ^ 2) := by
  field_simp
  try ring

/-! ### §H — re-evaluated with the holographic Newton constant: distance enters only
through the bit count

Under the program's information typing the coupling slot is where the inverse nat
lives (`G : L³T⁻²M⁻¹I⁻¹`): writing `G` in its holographic area-per-bit form
`A·c³/(ℏN)` makes the per-bit charge explicit, and the three identities below show
what the inverse-square law looks like from that side. -/

/-- **With the coupling in area-per-bit form, the radius cancels from the
inverse-square composite**: for any bit count `N`, substituting `G = A·c³/(ℏN)` with
the spherical screen `A = 4πR²` gives

  `G·M·m*/R² = 4π·M·v_F²·k_y/N`

— the screen's `R²` cancels the inverse square's, so the distance dependence of
Newton's law lives entirely in the bit count.  The inverse square is the statement
that a sphere's information content grows as its area. -/
theorem inverseSquare_R_only_through_bits (M ℏ ky vF R N : ℝ)
    (hℏ : ℏ ≠ 0) (hky : ky ≠ 0) (hvF : vF ≠ 0) (hR : R ≠ 0) (hN : N ≠ 0) :
    (4 * Real.pi * R ^ 2 * vF ^ 3 / (ℏ * N)) * M * (ℏ * ky / vF) / R ^ 2
      = 4 * Real.pi * M * vF ^ 2 * ky / N := by
  field_simp
  try ring

/-- **The mode's bit count is the Compton-cell tiling**: with `N* = 4π(k_y·R)²` — the
spherical screen tiled by cells of the mode's Compton scale `1/k_y` — the area-per-bit
coupling equals the anchor coupling `ℏv_F/m*²` at every radius.  `R` cancels
identically: area-per-bit is radius-independent because the count grows with the
area — the G-free Compton-cell count of the anchor chain, at the dialed scale. -/
theorem modeBitCount_comptonCells (ℏ ky vF R : ℝ)
    (hℏ : ℏ ≠ 0) (hky : ky ≠ 0) (hvF : vF ≠ 0) (hR : R ≠ 0) :
    4 * Real.pi * R ^ 2 * vF ^ 3 / (ℏ * (4 * Real.pi * (ky * R) ^ 2))
      = ℏ * vF / (ℏ * ky / vF) ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  try ring

/-- **The cascade re-derived through information**: substituting the Compton-cell
count `N* = 4π(k_yR)²` into the bit-form composite recovers exactly the §G result
`M·v_F²/(k_y·R²)`.  Newton's inverse square for the mode, holographically: the
coupling is area-per-bit, the count is the Compton tiling, and the distance dependence
is the tiling's growth. -/
theorem inverseSquare_holographic (M ky vF R : ℝ)
    (hky : ky ≠ 0) (hvF : vF ≠ 0) (hR : R ≠ 0) :
    4 * Real.pi * M * vF ^ 2 * ky / (4 * Real.pi * (ky * R) ^ 2)
      = M * vF ^ 2 / (ky * R ^ 2) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  try ring

/-! ### §I — the speed decomposed: the lattice under the Fermi velocity -/

/-- **The band profile** of the tight-binding chain on the wave-number line:
`E(k) = E₀ − 2t·cos(ka)` — the continuum reading of the chain's proven spectrum. -/
noncomputable def bandProfile (T : CondensedMatter.TightBindingChain) (k : ℝ) : ℝ :=
  T.E0 - 2 * T.t * Real.cos (k * T.a)

/-- The band profile agrees with the chain's eigenvalues at the quantized wave numbers
— the continuum function is the spectrum proven from the microscopic Hamiltonian
(`hamiltonian_energyEigenstate`), definitionally. -/
theorem bandProfile_eq_energyEigenvalue (T : CondensedMatter.TightBindingChain)
    (k : T.QuantaWaveNumber) : bandProfile T k = T.energyEigenvalue k := rfl

/-- **The group-velocity slope of the band**: `dE/dk = 2t·a·sin(ka)`. -/
theorem bandProfile_hasDerivAt (T : CondensedMatter.TightBindingChain) (k : ℝ) :
    HasDerivAt (bandProfile T) (2 * T.t * T.a * Real.sin (k * T.a)) k := by
  unfold bandProfile
  have hcos : HasDerivAt (fun q : ℝ => Real.cos (q * T.a))
      (-Real.sin (k * T.a) * T.a) k := by
    have hlin : HasDerivAt (fun q : ℝ => q * T.a) T.a k := by
      simpa using (hasDerivAt_id k).mul_const T.a
    have h := (Real.hasDerivAt_cos (k * T.a)).comp k hlin
    refine h.congr_deriv ?_
    ring
  have h := (hcos.const_mul (2 * T.t)).const_sub T.E0
  refine h.congr_deriv ?_
  ring

/-- **The Fermi velocity decomposed**: at the band centre `k₀ = π/(2a)` the slope is
exactly `2t·a` — in `ℏ = 1` units, `v_F = 2·(hopping)·(spacing)`.  The invariant speed
of the emergent Dirac mode is not primitive: it is two lattice parameters, read off the
spectrum the chain's Hamiltonian proves.  The replacement chain for `v_F` is now
complete in both directions — upward into observables (`v_F = Ω_Z/2k_y`,
`fermiVelocity_isolated`) and downward into the lattice (`v_F = 2ta`). -/
theorem fermiVelocity_decomposed (T : CondensedMatter.TightBindingChain) :
    HasDerivAt (bandProfile T) (2 * T.t * T.a) (Real.pi / (2 * T.a)) := by
  have ha : T.a ≠ 0 := T.a_pos.ne'
  have h := bandProfile_hasDerivAt T (Real.pi / (2 * T.a))
  rw [show Real.pi / (2 * T.a) * T.a = Real.pi / 2 from by field_simp; try ring] at h
  rw [Real.sin_pi_div_two, mul_one] at h
  exact h

/-- **The beat frequency reads the lattice**: combining the observable isolation
`v_F = Ω_Z/(2k_y)` with the microscopic decomposition `v_F = 2ta` gives

  `Ω_Z = 4·t·a·k_y`

— the terahertz quantum beats of the shutter measure the product of hopping and spacing
(`ℏ = 1`).  Clock above, lattice below, the speed eliminable from either side. -/
theorem beat_reads_lattice (t a ky Ω vF : ℝ)
    (hΩ : Ω = 2 * (ky * vF)) (hvF : vF = 2 * t * a) :
    Ω = 4 * t * a * ky := by
  rw [hΩ, hvF]
  ring

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.fermiVelocity_decomposed where
  derives @ "claim:the-fermi-velocity-is-not-primitive-it-is-twice-the-hopping-times-the-spacing-the-band-slope-at-the-centre-of-the-spectrum-proven-from-the-tight-binding-hamiltonian",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:CondensedMatter.TightBindingChain.energyEigenvalue",
  supported_by @ "lean:CondensedMatter.TightBindingChain.hamiltonian_energyEigenstate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.bandProfile_eq_energyEigenvalue"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.beat_reads_lattice where
  derives @ "claim:the-beat-frequency-is-four-times-hopping-times-spacing-times-transverse-momentum-the-terahertz-beats-measure-the-lattice",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:cruz-carrillo-bastos-villavicencio-2020-time-diffraction-and-zitterbewegung-of-two-dimensional-massless-dirac-excitations-prb-101-115415",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.fermiVelocity_isolated"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.inverseSquare_R_only_through_bits where
  derives @ "claim:with-the-area-per-bit-coupling-the-radius-cancels-from-the-inverse-square-composite-so-distance-enters-newtons-law-only-through-the-screens-bit-count",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.holographicBits",
  supported_by @ "lean:Physlib.Thermodynamics.HolographicScreenEntropy.newton_form_forces_bekensteinHawking"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.modeBitCount_comptonCells where
  derives @ "claim:the-modes-bit-count-is-four-pi-times-the-squared-product-of-transverse-momentum-and-radius-the-compton-cell-tiling-of-the-screen-making-area-per-bit-radius-independent",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassGravitationalConstant.newtonG_area_per_bit_inference",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.newtonG_isolated"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.inverseSquare_holographic where
  caveat @ "claim:the-holographic-reading-cites-the-bousso-covariant-bound-whose-local-flux-hypothesis-is-ansatz-loaded",
  discloses @ "lean:Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.generalizedEntropy_monotone",
  discloses @ "lean:Physlib.Thermodynamics.LightSheet.bousso_covariant_bound",
  derives @ "claim:newtons-inverse-square-for-the-mode-rederived-through-information-the-coupling-is-area-per-bit-the-count-is-the-compton-tiling-and-the-distance-dependence-is-the-tilings-growth",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.HolographicScreenEntropy.screenEntropy_bekensteinHawking"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.modeCoupling_isolated where
  derives @ "claim:the-modes-holographic-coupling-is-an-output-the-beat-frequency-cubed-over-eight-hbar-times-the-fifth-power-of-the-transverse-momentum-the-anchor-cascade-at-the-dialed-scale",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.newtonG_isolated",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchoredClock"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.inverseSquare_law_observables_only where
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  caveat @ "claim:the-algebra-is-exact-but-the-physical-reading-consumes-the-verlinde-entropic-force-derivation-whose-displacement-entropy-ansatz-is-ansatz-loaded",
  discloses @ "lean:Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde",
  formalizes @ "claim:the-newton-inverse-square-law-instantiates-at-the-effective-mass-in-observables-only-as-the-composite-identity-screen-temperature-times-entropy-gradient-equals-the-inverse-square-form",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.inverseSquare_cascade where
  derives @ "claim:with-the-modes-own-holographic-coupling-the-inverse-square-composite-is-hbar-free-source-mass-times-speed-squared-over-transverse-momentum-times-radius-squared",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.NewtonGIsolation.newtonG_isolated"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.fermiVelocity_isolated where
  derives @ "claim:the-modes-invariant-speed-is-an-output-the-ratio-of-the-beat-frequency-to-twice-the-transverse-momentum-not-an-input",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:cruz-carrillo-bastos-villavicencio-2020-time-diffraction-and-zitterbewegung-of-two-dimensional-massless-dirac-excitations-prb-101-115415"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.entropic_law_observables_only where
  caveat @ "claim:the-algebra-is-exact-but-the-physical-reading-consumes-the-verlinde-entropic-force-derivation-whose-displacement-entropy-ansatz-is-ansatz-loaded",
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  formalizes @ "claim:force-is-an-eliminable-label-the-formal-content-of-the-entropic-second-law-is-the-identity-between-the-temperature-entropy-composite-and-the-mass-acceleration-composite-stated-in-mode-observables-only",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  supported_by @ "lean:Physlib.Thermodynamics.verlindeEntropicForce"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.transverseMomentum_is_entropy_gradient where
  formalizes @ "claim:the-transverse-momentum-is-the-verlinde-displacement-entropy-gradient-of-the-effective-mass-two-pi-kb-of-entropy-per-unit-momentum-and-displacement-with-every-other-parameter-cancelling",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:cruz-carrillo-bastos-villavicencio-2020-time-diffraction-and-zitterbewegung-of-two-dimensional-massless-dirac-excitations-prb-101-115415",
  supported_by @ "lean:Physlib.Thermodynamics.verlindeDisplacementEntropy"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.effectiveUnruh_matches_clock where
  derives @ "claim:the-analogue-unruh-temperature-reads-the-transverse-mass-clock-exactly-at-the-compton-acceleration-ky-times-vf-squared-half-the-beat-frequency-times-vf",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.unruh_eq_comptonTemperature_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.HiggsClockThreeOrigins.unruh_eq_higgsClockTemperature_iff"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.effectiveNewton_from_unruh where
  caveat @ "claim:the-algebra-is-exact-but-the-physical-reading-consumes-the-verlinde-entropic-force-derivation-whose-displacement-entropy-ansatz-is-ansatz-loaded",
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  derives @ "claim:the-graphene-quasiparticles-inertia-is-entropic-newtons-second-law-from-the-unruh-temperature-at-the-modes-invariant-speed-with-the-transverse-momentum-as-the-entropy-source",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.zbwAmplitude_mul_frequency"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.transverse_momentum_is_mass where
  formalizes @ "claim:the-two-dimensional-massless-dirac-mode-at-fixed-transverse-momentum-is-unitarily-the-one-dimensional-massive-dirac-mode-with-the-transverse-momentum-in-the-mass-slot",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:cruz-carrillo-bastos-villavicencio-2020-time-diffraction-and-zitterbewegung-of-two-dimensional-massless-dirac-excitations-prb-101-115415",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization.diracHamiltonian"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.transverseTrembling_eq_zero_iff where
  derives @ "claim:the-transverse-trembling-operator-is-the-transverse-momentum-times-the-spin-product-and-vanishes-exactly-at-normal-incidence-the-two-dimensional-face-of-trembling-equals-mass",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.zitterVelocity1_oneD_eq_zero_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.foldyConnectionStrength_eq_zero_iff",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.mean_position_linear"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.cruz_beat_is_zitterbewegung where
  derives @ "claim:the-terahertz-quantum-beat-frequency-of-the-graphene-shutter-is-the-rest-zitterbewegung-frequency-of-the-effective-mass-supplied-by-the-transverse-momentum",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton",
  supported_by @ "paper:cruz-carrillo-bastos-villavicencio-2020-time-diffraction-and-zitterbewegung-of-two-dimensional-massless-dirac-excitations-prb-101-115415"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.effectiveMass_dial where
  derives @ "claim:every-effective-mass-up-to-the-wave-number-is-realized-by-an-incidence-angle-so-in-dirac-matter-the-external-mass-input-of-the-covariant-system-is-a-laboratory-knob",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitonMassRoleSeparation.dilation_covariant_determination_absurd",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchoredClock",
  caveat @ "claim:the-quantum-shutter-solution-with-its-bessel-series-diffraction-in-time-asymptotics-and-inverse-square-root-decay-is-not-formalized-searched-moshinsky-and-shutter-vocabulary-with-only-an-unrelated-dirac-oscillator-citation"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass

end

end
