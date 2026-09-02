/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
public import Physlib.QuantumMechanics.ComplexAction.ComplexActionContourUnification
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZitterbewegungOperatorConsistency
public import Physlib.QuantumMechanics.ComplexAction.Dirac.FoldyWouthuysenExact
public import Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

meta import Zil

/-!
# The canonical representation — Zitterbewegung, position, and the energy-sign metric

Lock, *Relativistic invariance and Zitterbewegung*, Am. J. Phys. **52** (1984) 253: the
trembling motion is a property of the Dirac representation, not of the particle.  The
three sections carry that result and what follows from it:

* `RepresentationDichotomy` — in the canonical (Foldy–Wouthuysen) representation the
  velocity commutes with the Hamiltonian and the mean position moves linearly, while the
  Dirac representation trembles; the trembling operator vanishes exactly on the null
  mass shell.
* `PositionOperator` — the Newton–Wigner position operator is the repository's time
  operator read in momentum, with Lock's wave-packet integrals, the Bogoliubov energy
  derivative, and the Foldy connection whose strength at rest is the Zitterbewegung
  amplitude.
* `EnergySignMetric` — the metric on energy-sign states: the momentum-line length `π/2`,
  the rest-frame and Euclidean faces, the Nagao–Nielsen contour system with its
  spacetime and tetrad readings, and the Yukawa-clock and dilation-group weights.
-/

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung

section RepresentationDichotomy

/-!
# Zitterbewegung is representation-contingent — Lock 1984

Lock, *Relativistic invariance and Zitterbewegung*, Am. J. Phys. **52** (1984) 223.  The
paper's question is not what Zitterbewegung does but why it exists at all, and its answer
is a dichotomy: relativistic invariance forces a choice between a simple position operator
and simple (local) interactions — one can never take both options at once — whereas
Galilean invariance grants both in the same representation.  Both energy signs are
*necessary but not sufficient* for the trembling: the canonical (Foldy) representation has
the full sign spectrum and no Zitterbewegung.

Formalized here, at the single-momentum-mode level where the repository's Dirac carriers
live (`FourSpinorDiracHamiltonian`, `FoldyWouthuysenExact`):

* **§A — the canonical representation is trembling-free (Lock Eq. 2.16).**  The canonical
  Hamiltonian is the Foldy–Wouthuysen image `Eβ` (`fw_intertwine`), and Lock's group
  velocity `V_G = c²ΔP/E` becomes the operator `(p/E)·β`.  It commutes with the canonical
  Hamiltonian, and `canonical_velocity_heisenberg_constant` upgrades this through
  `heisenbergConj_eq_self_iff_commute`: every evolution commuting with the energy sign
  leaves the canonical velocity fixed.  `mean_position_linear` is then Eq. (2.16) itself:
  a position with constant mean velocity moves as `R₀ + V_G·t` — no Zitterbewegung.
* **§B — the Dirac representation trembles, and the trembling is the mass.**  For 1-D
  motion the Zitterbewegung part of the Dirac velocity collapses to
  `η₁ = m·βα₁` (`zitterVelocity1_oneD`): the trembling operator *is* the mass term, so it
  vanishes exactly when `m = 0` (`zitterVelocity1_oneD_eq_zero_iff`) and the Dirac
  velocity fails to be conserved at every massive mode
  (`dirac_velocity_not_conserved`).  `representation_dichotomy` packages the two halves:
  one particle, two position operators — the canonical one inert, the Dirac one trembling
  — which is Lock's §V: the energy-sign spectrum (shared through `fw_intertwine`) cannot
  decide the Zitterbewegung; the choice of position operator does.
* **§B′ — both intuitive hopes force the null mode (Lock §V).**  `trembling_free_iff_null`:
  the 1-D mode Hamiltonian commutes with both the velocity `α₁` and the energy sign `β`
  exactly when `p = 0` and `m = 0` — position-simple and sign-preserving together happen
  only for the vanishing Hamiltonian.  The Galilean contrast (Lock Eq. 3.5):
  `galileanModeSymbol_central` — the free Galilean mode symbol `(p²/2m)·1` is scalar, so
  *every* operator is a constant of its motion and both hopes hold at once.  The pair of
  statements, identical question with opposite answers, is the paper's summary claim.
* **§C — the Foldy–Wouthuysen dressing is nontrivial at every moving mode (Lock
  Eq. 3.3).**  `fwOperator_scalar_iff`: the FW operator is a scalar matrix exactly at
  `p = 0`; `fwOperator_momentum_injective`: distinct momenta give distinct FW operators.
  This is the mode-level mechanism of Lock's §III — a local interaction, carried to the
  canonical representation, is conjugated by momentum-dependent non-scalar rotations and
  cannot stay a multiple of the identity between modes; locality and simple position
  cannot share a representation.

**Honest layering.**  Formalized: the operator dichotomy at a momentum mode, the 1-D
trembling-equals-mass identity, and the non-scalarity and injectivity of the FW dressing.
The Newton–Wigner position operator `X̂ = iℏ∇_P` and Lock's wave-packet mean position
(2.16) are carried by the `PositionOperator` section — the name-based search that first
declared them absent missed that the repository already held the operator under a
different reading (the Fujiwara time operator in the energy representation *is* the
position operator in the momentum representation); the follow-up structural search found
it.  Still open: the three-dimensional `d³p` packet integrals and the integral-kernel form
of the dressed interaction (3.3).  Lock's Darwin-term reading (4.1) is already formalized
in `PauliEquationSpinOrbit` and is linked, not repeated.
-/

open Matrix spaceTime
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZitterbewegungOperatorConsistency

/-! ### §A — the canonical representation is trembling-free (Lock 2.16) -/

/-- **The canonical (Foldy) Hamiltonian at a momentum mode**: `h₀ = E·β` — the energy-sign
operator times the on-shell energy, the exact Foldy–Wouthuysen image of the Dirac
Hamiltonian (`fw_intertwine`).  Lock Eq. (2.22) written after diagonalization. -/
def canonicalHamiltonian (E : ℝ) : Matrix (Fin 4) (Fin 4) ℂ := (E : ℂ) • diracBeta

/-- **The canonical velocity operator**: Lock's group velocity `V_G = c²ΔP/E` of
Eq. (2.16) at a mode — the energy sign `β` times `p/E` (units `c = 1`). -/
noncomputable def canonicalVelocity1 (p E : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((p / E : ℝ) : ℂ) • diracBeta

/-- **The canonical velocity commutes with the canonical Hamiltonian** — both are
multiples of the energy sign.  This is the operator core of Lock's Eq. (2.16): in the
canonical representation nothing in the velocity can oscillate. -/
theorem canonicalVelocity1_commute (p E : ℝ) :
    canonicalHamiltonian E * canonicalVelocity1 p E
      = canonicalVelocity1 p E * canonicalHamiltonian E := by
  unfold canonicalHamiltonian canonicalVelocity1
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, mul_comm]

/-- **The canonical velocity is a constant of every sign-preserving motion**: any unitary
that commutes with the energy sign — in particular every evolution generated by the
canonical Hamiltonian — leaves the canonical velocity fixed under Heisenberg conjugation.
Lock's Eq. (2.16) first two terms: the mean motion is inert. -/
theorem canonical_velocity_heisenberg_constant (p E : ℝ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : Uᴴ * U = 1)
    (hUβ : U * diracBeta = diracBeta * U) :
    heisenbergConj U (canonicalVelocity1 p E) = canonicalVelocity1 p E := by
  refine (heisenbergConj_eq_self_iff_commute U (canonicalVelocity1 p E) hU).mpr ?_
  unfold canonicalVelocity1
  rw [Matrix.smul_mul, Matrix.mul_smul, hUβ]

/-- **Lock Eq. (2.16)**: a mean position whose velocity is a constant moves in a straight
line, `⟨X(t)⟩ = R₀ + V_G·t` — the canonical-representation wave packet has no
Zitterbewegung. -/
theorem mean_position_linear (X : ℝ → ℝ) (vG : ℝ)
    (hX : ∀ t, HasDerivAt X vG t) (t : ℝ) :
    X t = X 0 + vG * t := by
  have hd : ∀ s, HasDerivAt (fun u => X u - vG * u) 0 s := by
    intro s
    have h := (hX s).sub ((hasDerivAt_id s).const_mul vG)
    refine h.congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (f := fun u => X u - vG * u)
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simp only [mul_zero, sub_zero] at hconst
  linarith [hconst]

/-! ### §B — the Dirac representation trembles, and the trembling is the mass -/

/-- **The 1-D trembling operator is the mass term**: for motion along one axis the
Zitterbewegung part of the Dirac velocity collapses to `η₁ = m·βα₁`.  The trembling
carries the mass and nothing else — the operator form of the Compton-clock reading that
rest energy is what oscillates. -/
theorem zitterVelocity1_oneD (p m : ℝ) :
    zitterVelocity1 p 0 0 m = (m : ℂ) • (diracBeta * diracAlpha1) := by
  unfold zitterVelocity1 diracHamiltonian4
  push_cast
  rw [zero_smul, zero_smul, add_zero, add_zero, Matrix.add_mul,
    Matrix.smul_mul, Matrix.smul_mul, diracAlpha1_sq]
  abel

/-- The product `βα₁` in concrete form — the matrix whose nonvanishing tells the mass
apart from zero in the trembling operator. -/
theorem diracBeta_mul_diracAlpha1_concrete :
    diracBeta * diracAlpha1
      = !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0] := by
  rw [diracBeta, γ0, diracAlpha1_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- **The 1-D trembling vanishes exactly when the mass does**: `η₁ = 0 ↔ m = 0`.  A
massless 1-D mode moves at the invariant speed with nothing to oscillate against; a
massive one trembles.  The mass is the Zitterbewegung source. -/
theorem zitterVelocity1_oneD_eq_zero_iff (p m : ℝ) :
    zitterVelocity1 p 0 0 m = 0 ↔ m = 0 := by
  rw [zitterVelocity1_oneD]
  constructor
  · intro h
    have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) h
    rw [diracBeta_mul_diracAlpha1_concrete] at h03
    simp [Matrix.smul_apply] at h03
    exact_mod_cast h03
  · intro h
    rw [h]
    simp

/-- **The Dirac velocity is not conserved at any massive mode**: `α₁` fails to commute
with the 1-D Dirac Hamiltonian whenever `m ≠ 0`.  The commutator is `2η₁ = 2m·βα₁`
(`velocity_heisenberg_derivative`), and the mass keeps it from vanishing — the trembling
half of Lock's dichotomy. -/
theorem dirac_velocity_not_conserved (p m : ℝ) (hm : m ≠ 0) :
    diracHamiltonian4 p 0 0 m * diracAlpha1 ≠ diracAlpha1 * diracHamiltonian4 p 0 0 m := by
  intro h
  have hd := velocity_heisenberg_derivative p 0 0 m
  rw [h, sub_self] at hd
  have hz : zitterVelocity1 p 0 0 m = 0 := by
    have h2 : ((2 : ℂ))⁻¹ • ((2 : ℂ) • zitterVelocity1 p 0 0 m)
        = ((2 : ℂ))⁻¹ • (0 : Matrix (Fin 4) (Fin 4) ℂ) := by rw [← hd]
    rwa [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul, smul_zero] at h2
  exact hm ((zitterVelocity1_oneD_eq_zero_iff p m).mp hz)

/-- **Lock's §V dichotomy at a mode**: one particle, two position operators.  The
canonical velocity commutes with the canonical Hamiltonian while the Dirac velocity fails
to commute with the Dirac Hamiltonian — although the two Hamiltonians are the same
operator through the Foldy–Wouthuysen rotation (`fw_intertwine`), so their energy-sign
spectra coincide.  Both signs are therefore necessary but not sufficient for
Zitterbewegung: what decides it is which operator is called position. -/
theorem representation_dichotomy (p m E : ℝ) (hm : m ≠ 0) :
    canonicalHamiltonian E * canonicalVelocity1 p E
        = canonicalVelocity1 p E * canonicalHamiltonian E
      ∧ diracHamiltonian4 p 0 0 m * diracAlpha1
        ≠ diracAlpha1 * diracHamiltonian4 p 0 0 m :=
  ⟨canonicalVelocity1_commute p E, dirac_velocity_not_conserved p m hm⟩

/-! ### §B′ — both intuitive hopes force the null mode -/

/-- The 1-D commutator of the Dirac Hamiltonian with the energy sign:
`Hβ − βH = −2p·βα₁` — the transport term is what mixes the energy signs. -/
theorem hamiltonian_beta_commutator_oneD (p m : ℝ) :
    diracHamiltonian4 p 0 0 m * diracBeta - diracBeta * diracHamiltonian4 p 0 0 m
      = ((-2 * p : ℝ) : ℂ) • (diracBeta * diracAlpha1) := by
  have hab : diracAlpha1 * diracBeta = -(diracBeta * diracAlpha1) :=
    eq_neg_of_add_eq_zero_left diracAlpha1_beta_anticomm
  unfold diracHamiltonian4
  push_cast
  rw [zero_smul, zero_smul, add_zero, add_zero, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    hab, diracBeta_sq]
  rw [smul_neg]
  module

/-- **Position-simple and sign-preserving together force the null mode** (Lock §V): the
1-D Dirac Hamiltonian commutes with both the velocity `α₁` and the energy sign `β` exactly
when `m = 0` and `p = 0` — i.e. never, for an actual particle.  The mass feeds the
velocity commutator, the momentum feeds the sign commutator, and killing both kills the
Hamiltonian.  Relativistic invariance offers the two intuitive hopes only jointly with the
trivial dynamics. -/
theorem trembling_free_iff_null (p m : ℝ) :
    (diracHamiltonian4 p 0 0 m * diracAlpha1 = diracAlpha1 * diracHamiltonian4 p 0 0 m
        ∧ diracHamiltonian4 p 0 0 m * diracBeta = diracBeta * diracHamiltonian4 p 0 0 m)
      ↔ (m = 0 ∧ p = 0) := by
  constructor
  · rintro ⟨hα, hβ⟩
    have hm : m = 0 := by
      by_contra hm
      exact dirac_velocity_not_conserved p m hm hα
    refine ⟨hm, ?_⟩
    have hc := hamiltonian_beta_commutator_oneD p m
    rw [hβ, sub_self] at hc
    have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) hc.symm
    rw [diracBeta_mul_diracAlpha1_concrete] at h03
    simp [Matrix.smul_apply] at h03
    linarith [h03]
  · rintro ⟨hm, hp⟩
    subst hm hp
    have h0 : diracHamiltonian4 0 0 0 0 = 0 := by
      unfold diracHamiltonian4
      push_cast
      simp
    rw [h0]
    simp

/-- **The free Galilean mode symbol** `p²/2m·1` — Lock Eq. (3.5) at a momentum mode: a
scalar matrix, because the Galilean free Hamiltonian carries no energy-sign or spin
structure. -/
noncomputable def galileanModeSymbol (p m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((p ^ 2 / (2 * m) : ℝ) : ℂ) • 1

/-- **Galilean invariance grants both hopes at once** (Lock Eq. 3.5 and §V): the free
Galilean mode symbol is scalar, so *every* operator commutes with it — every position is
simple and every interaction stays local in the same representation.  The identical
question answered oppositely by `trembling_free_iff_null` is the paper's dichotomy. -/
theorem galileanModeSymbol_central (p m : ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    galileanModeSymbol p m * A = A * galileanModeSymbol p m := by
  unfold galileanModeSymbol
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-! ### §C — the Foldy–Wouthuysen dressing is nontrivial at every moving mode -/

/-- **The FW operator is scalar exactly at rest** (Lock Eq. 3.3's mechanism): the
canonical-representation map is a multiple of the identity — and so dresses nothing — if
and only if the mode momentum vanishes.  At every moving mode the rotation is genuinely
matrix-valued, which is what converts a local interaction into a nonlocal one between
canonical modes. -/
theorem fwOperator_scalar_iff (p1 p2 p3 m E : ℝ) :
    (∃ c : ℂ, fwOperator p1 p2 p3 m E = c • 1) ↔ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    rw [fwOperator_concrete] at hc
    have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 2) hc
    have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) hc
    simp [Matrix.smul_apply] at h02 h03
    have hre := congrArg Complex.re h03
    have him := congrArg Complex.im h03
    simp at hre him
    refine ⟨by exact_mod_cast hre, by linarith [him], by exact_mod_cast h02⟩
  · rintro ⟨h1, h2, h3⟩
    subst h1 h2 h3
    refine ⟨((E + m : ℝ) : ℂ), ?_⟩
    unfold fwOperator diracComplexStructure alphaDotP diracHamiltonian4
    simp

/-- **The FW dressing is momentum-resolved**: equal FW operators force equal momenta (and
equal scalar parts `E + m`).  Lock Eq. (3.3): the interaction matrix element between
canonical modes at `p` and `q` is conjugated by *different* rotations on each side, so a
local interaction cannot remain local in the canonical representation. -/
theorem fwOperator_momentum_injective (p1 p2 p3 q1 q2 q3 m m' E E' : ℝ)
    (h : fwOperator p1 p2 p3 m E = fwOperator q1 q2 q3 m' E') :
    p1 = q1 ∧ p2 = q2 ∧ p3 = q3 ∧ E + m = E' + m' := by
  rw [fwOperator_concrete, fwOperator_concrete] at h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 2) h
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) h
  simp at h00 h02 h03
  have hre := congrArg Complex.re h03
  have him := congrArg Complex.im h03
  simp at hre him
  exact ⟨hre, by linarith [him], by exact_mod_cast h02, by exact_mod_cast h00⟩

end RepresentationDichotomy

section PositionOperator

/-!
# The Newton–Wigner position operator and Lock's wave-packet mean position

Lock's canonical representation (Am. J. Phys. **52** (1984) 223, Eqs. 2.9–2.16) rests on the
position operator `X̂ = iℏ∇_P` acting on momentum-space wave functions.  The repository
already carries this operator — under a different physical reading.
`FujiwaraTimeEnergyOperator` packages `iℏ∂` on `L²(ℝ)` with a dense Schwartz core
(`timeOperator`, built from `−momentumCLM` via `schwartzSubmodule`), proves the exact CCR
against multiplication by the spectral variable (`time_energy_ccr`), symmetry, unboundedness,
the Robertson uncertainty, and the generalized eigenkets `e^{−iEt/ℏ}`
(`generalizedTimeKet_eigen`).  Reading the spectral variable as momentum instead of energy,
that operator *is* the Newton–Wigner position operator, the multiplication operator *is* the
momentum operator, and Fujiwara's time kets *are* Lock's localized position eigenstates
`⟨p|R⟩ = e^{−ipR/ℏ}` of Eqs. (2.12–2.14).  §A records the identification as definitions;
the inherited theorems are cited, not restated.

The genuinely new content:

* **§B — Lock Eq. (2.16) as an integral theorem.**  For a single-sign wave packet
  `ψ_t(p) = e^{−iE(p)t/ℏ}·a(p)`, the position density `ψ̄_t·(iℏ∂_p ψ_t)` splits pointwise
  into the static part plus `t·E′(p)·|a(p)|²` (`evolvedPacket_position_density`) — the
  evolution phase cancels exactly, no trembling survives — and integrating gives
  `⟨X̂⟩(t) = R₀ + V_G·t` with `V_G = ∫ E′(p)|a(p)|² dp`
  (`meanPosition_linear_wavePacket`).  The dispersion weld `bogoliubovEnergy_hasDerivAt`
  supplies `E′(p) = p/E(p)` — Lock's group velocity `c²p/E` in natural units, the same
  `p/E` carried by `canonicalVelocity1`.
* **§C — Lock Eq. (2.24)'s third term is the Foldy–Wouthuysen connection.**  In a
  transformed representation the position operator is
  `x̂ = Ŵ X̂ Ŵ⁻¹ = iℏ∂_p + iℏ Ŵ(∂_p Ŵ⁻¹)`: the second term is a gauge connection from the
  momentum-dependence of the rotation.  For the two-level Foldy–Wouthuysen rotation by the
  half Bogoliubov angle `φ = ½·arctan(p/m)`, the connection is exactly off-diagonal
  (`foldyRotation_connection`: `W·∂W⁻¹ = φ′·[[0,−1],[1,0]]`), with strength
  `ℏφ′ = ℏm/(2(m²+p²)) = ℏm/2E²` (`bogoliubovAngle_hasDerivAt`).  It vanishes exactly when
  the mass does (`foldyConnectionStrength_eq_zero_iff` — the packet-level face of
  `zitterVelocity1_oneD_eq_zero_iff`), and at rest its value is `ℏ/2m` — the observed
  Zitterbewegung amplitude, half the reduced Compton wavelength
  (`foldyConnectionStrength_rest`, welding `zbwAmplitude`).  This is the operator mechanism
  of Lock's (2.24): the energy-sign-mixing part of the transformed position has amplitude
  `ℏm/2E²` and oscillates at the gap frequency, which is the Zitterbewegung.

**Honest layering.**  One momentum dimension throughout, matching the repository's `L²(ℝ)`
operator packaging; the three-dimensional `d³p` integrals and the integral-kernel form of
the dressed interaction remain open.  The §C connection is stated at the rotation-matrix
level; composing it against the packaged `L²` operator needs matrix-valued Schwartz
machinery the repository does not yet carry.
-/

open Complex MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation

/-! ### §A — the operator, by identification -/

/-- **The momentum-representation Hilbert space** `L²(ℝ)` — the same carrier as the energy
representation; only the physical reading of the spectral variable changes. -/
abbrev MomentumHilbert := EnergyHilbert

/-- **The Newton–Wigner position operator** `X̂ = iℏ∂_p` on momentum-space wave functions —
Lock Eq. (2.9).  This *is* the Fujiwara time operator with the spectral variable read as
momentum: densely defined on the Schwartz core, symmetric
(`timeOperator_isSymmetric`), unbounded (`timeOperator_isUnbounded`), with exact CCR
`[X̂, P̂] = iℏ` against the multiplication operator (`time_energy_ccr`) and the Robertson
uncertainty (`time_energy_uncertainty`). -/
def newtonWignerPosition : MomentumHilbert →ₗ.[ℂ] MomentumHilbert := timeOperator

/-- **The momentum operator in its own representation**: multiplication by `p` — the
`energyOperator` under the momentum reading. -/
def momentumMultiplication : MomentumHilbert →ₗ.[ℂ] MomentumHilbert := energyOperator

/-- **Lock's localized position eigenstate** `⟨p|R⟩ = e^{−ipR/ℏ}` (Eqs. 2.12–2.14) — the
generalized eigenfunction of `X̂` at position `R`: Fujiwara's `generalizedTimeKet` under
the momentum reading, with eigenvalue equation `generalizedTimeKet_eigen` and unit modulus
`generalizedTimeKet_modulus` (single-sign Fourier content, as Lock requires). -/
def localizedPositionKet (R : ℝ) : ℝ → ℂ := generalizedTimeKet R

/-! ### §B — Lock Eq. (2.16): the wave-packet mean position is linear in time -/

/-- **The evolved single-sign wave packet** `ψ_t(p) = e^{−iE(p)t/ℏ}·a(p)` — Lock's
Eq. (2.15) at one energy sign, one momentum dimension. -/
def evolvedPacket (ħ t : ℝ) (E : ℝ → ℝ) (a : ℝ → ℂ) (p : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((E p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)) * a p

/-- The evolution phase is unimodular: conjugate times itself is `1`. -/
lemma evolutionPhase_conj_mul (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-Complex.I * (θ : ℂ)))
        * Complex.exp (-Complex.I * (θ : ℂ)) = 1 := by
  rw [← Complex.exp_conj]
  rw [show (starRingEnd ℂ) (-Complex.I * (θ : ℂ)) = Complex.I * (θ : ℂ) by
    simp [map_mul]]
  rw [← Complex.exp_add]
  rw [show Complex.I * (θ : ℂ) + -Complex.I * (θ : ℂ) = 0 from by ring]
  exact Complex.exp_zero

/-- The packet's momentum-derivative, from the derivatives of the dispersion and the
amplitude. -/
lemma evolvedPacket_hasDerivAt (ħ t : ℝ) (E : ℝ → ℝ) (E' : ℝ → ℝ) (a a' : ℝ → ℂ) (p : ℝ)
    (hE : HasDerivAt E (E' p) p) (ha : HasDerivAt a (a' p) p) :
    HasDerivAt (evolvedPacket ħ t E a)
      (Complex.exp (-Complex.I * ((E p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ))
        * ((-Complex.I * ((E' p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)) * a p + a' p)) p := by
  have hEc : HasDerivAt (fun q => ((E q : ℝ) : ℂ)) ((E' p : ℝ) : ℂ) p := hE.ofReal_comp
  have hphase : HasDerivAt
      (fun q => -Complex.I * ((E q : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ))
      (-Complex.I * ((E' p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)) p := by
    have h := (hEc.const_mul (-Complex.I)).mul_const ((t / ħ : ℝ) : ℂ)
    refine h.congr_deriv ?_
    ring
  have hexp := hphase.cexp
  have h := hexp.mul ha
  refine h.congr_deriv ?_
  ring

/-- **The pointwise position density of the evolved packet** — the heart of Lock's
Eq. (2.16).  The evolution phase cancels between the conjugate and the derivative, leaving
the static density plus the drift term:

  `ψ̄_t·(iℏ ∂_p ψ_t) = ā·(iℏ a′) + t·E′(p)·|a(p)|²`.

No cross term at a single energy sign — nothing oscillates. -/
theorem evolvedPacket_position_density (ħ t : ℝ) (E E' : ℝ → ℝ) (a a' : ℝ → ℂ) (p : ℝ)
    (hE : HasDerivAt E (E' p) p) (ha : HasDerivAt a (a' p) p) (hħ : ħ ≠ 0) :
    (starRingEnd ℂ) (evolvedPacket ħ t E a p)
        * (Complex.I * (ħ : ℂ) * deriv (evolvedPacket ħ t E a) p)
      = (starRingEnd ℂ) (a p) * (Complex.I * (ħ : ℂ) * a' p)
        + ((E' p * t : ℝ) : ℂ) * ((Complex.normSq (a p) : ℝ) : ℂ) := by
  have hd := (evolvedPacket_hasDerivAt ħ t E E' a a' p hE ha).deriv
  rw [hd]
  unfold evolvedPacket
  rw [map_mul]
  set c := Complex.exp (-Complex.I * ((E p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)) with hc
  have hphase : (starRingEnd ℂ) c * c = 1 := by
    rw [hc, show -Complex.I * ((E p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)
        = -Complex.I * ((E p * (t / ħ) : ℝ) : ℂ) from by push_cast; ring]
    exact evolutionPhase_conj_mul (E p * (t / ħ))
  have hns : (starRingEnd ℂ) (a p) * a p = ((Complex.normSq (a p) : ℝ) : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj (a p)
  calc (starRingEnd ℂ) c * (starRingEnd ℂ) (a p)
        * (Complex.I * (ħ : ℂ) * (c * ((-Complex.I * ((E' p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)) * a p + a' p)))
      = ((starRingEnd ℂ) c * c)
        * ((starRingEnd ℂ) (a p) * (Complex.I * (ħ : ℂ) * ((-Complex.I * ((E' p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)) * a p + a' p))) := by
        ring
    _ = (starRingEnd ℂ) (a p) * (Complex.I * (ħ : ℂ) * a' p)
        + ((ħ : ℂ) * ((E' p : ℝ) : ℂ) * ((t / ħ : ℝ) : ℂ)) * ((starRingEnd ℂ) (a p) * a p) := by
        rw [hphase, one_mul]
        have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
        ring_nf
        rw [Complex.I_sq]
        ring
    _ = (starRingEnd ℂ) (a p) * (Complex.I * (ħ : ℂ) * a' p)
        + ((E' p * t : ℝ) : ℂ) * ((Complex.normSq (a p) : ℝ) : ℂ) := by
        rw [hns]
        congr 1
        rw [show ((t / ħ : ℝ) : ℂ) = (t : ℂ) / (ħ : ℂ) from by push_cast; ring]
        have hħc : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
        field_simp
        push_cast
        ring

/-- **Lock Eq. (2.16): the mean position of a single-sign packet is `R₀ + V_G·t`.**
Integrating the pointwise density: the mean position at time `t` is the initial mean
position plus `t` times the group-velocity expectation `V_G = ∫ E′(p)|a(p)|² dp`.  The
canonical-representation wave packet moves in a straight line — the integral form of the
operator statement `canonicalVelocity1_commute`, and the sense in which Zitterbewegung
never arises in the canonical representation. -/
theorem meanPosition_linear_wavePacket (ħ t : ℝ) (E E' : ℝ → ℝ) (a a' : ℝ → ℂ)
    (hE : ∀ p, HasDerivAt E (E' p) p) (ha : ∀ p, HasDerivAt a (a' p) p) (hħ : ħ ≠ 0)
    (h1 : Integrable (fun p => (starRingEnd ℂ) (a p) * (Complex.I * (ħ : ℂ) * a' p)))
    (h2 : Integrable (fun p => ((E' p * Complex.normSq (a p) : ℝ) : ℂ))) :
    (∫ p, (starRingEnd ℂ) (evolvedPacket ħ t E a p)
        * (Complex.I * (ħ : ℂ) * deriv (evolvedPacket ħ t E a) p))
      = (∫ p, (starRingEnd ℂ) (a p) * (Complex.I * (ħ : ℂ) * a' p))
        + (t : ℂ) * ∫ p, ((E' p * Complex.normSq (a p) : ℝ) : ℂ) := by
  have hcongr : (fun p => (starRingEnd ℂ) (evolvedPacket ħ t E a p)
      * (Complex.I * (ħ : ℂ) * deriv (evolvedPacket ħ t E a) p))
      = fun p => (starRingEnd ℂ) (a p) * (Complex.I * (ħ : ℂ) * a' p)
        + (t : ℂ) * ((E' p * Complex.normSq (a p) : ℝ) : ℂ) := by
    funext p
    rw [evolvedPacket_position_density ħ t E E' a a' p (hE p) (ha p) hħ]
    push_cast
    ring
  rw [hcongr, integral_add h1 (h2.const_mul (t : ℂ)), integral_const_mul]

/-- **The relativistic group velocity**: the on-shell dispersion `E(p) = √(m² + p²)`
(natural units, `bogoliubovEnergy`) has derivative `E′(p) = p/E(p)` — Lock's
`V_G = c²p/E`, and the scalar carried by the canonical velocity operator
`canonicalVelocity1`. -/
theorem bogoliubovEnergy_hasDerivAt (m p : ℝ) (hm : m ≠ 0) :
    HasDerivAt (fun q => bogoliubovEnergy m q) (p / bogoliubovEnergy m p) p := by
  have hne : m ^ 2 + p ^ 2 ≠ 0 := by positivity
  have hinner : HasDerivAt (fun q : ℝ => m ^ 2 + q ^ 2) (2 * p) p := by
    have h := (hasDerivAt_pow 2 p).const_add (m ^ 2)
    refine h.congr_deriv ?_
    push_cast
    ring
  have h := (Real.hasDerivAt_sqrt hne).comp p hinner
  have hsqrt_pos : 0 < Real.sqrt (m ^ 2 + p ^ 2) := by
    apply Real.sqrt_pos.mpr
    positivity
  refine HasDerivAt.congr_deriv (by exact h) ?_
  unfold bogoliubovEnergy
  field_simp

/-! ### §C — Lock Eq. (2.24): the transformed position carries the FW connection -/

/-- **The half Bogoliubov angle** `φ(p) = ½·arctan(p/m)` — the rotation angle of the
two-level Foldy–Wouthuysen transformation (`cos²φ = (E+m)/2E`, the `bogoliubovU2`
weight). -/
def bogoliubovAngle (m p : ℝ) : ℝ := Real.arctan (p / m) / 2

/-- **The angle's momentum-derivative is the connection strength**:
`φ′(p) = m/(2(m²+p²)) = m/2E²`. -/
theorem bogoliubovAngle_hasDerivAt (m p : ℝ) (hm : m ≠ 0) :
    HasDerivAt (bogoliubovAngle m) (m / (2 * (m ^ 2 + p ^ 2))) p := by
  have harg : HasDerivAt (fun q : ℝ => q / m) (1 / m) p := by
    have h := (hasDerivAt_id p).div_const m
    refine h.congr_deriv ?_
    ring
  have h := ((Real.hasDerivAt_arctan (p / m)).comp p harg).div_const 2
  have hne : (1 : ℝ) + (p / m) ^ 2 ≠ 0 := by positivity
  refine HasDerivAt.congr_deriv (by exact h) ?_
  field_simp
  try ring

/-- **The two-level Foldy–Wouthuysen rotation** by angle `φ`. -/
def foldyRotation (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos φ, Real.sin φ; -Real.sin φ, Real.cos φ]

/-- **The connection is exactly off-diagonal**: `W(φ)·(∂W⁻¹) = φ′·[[0,−1],[1,0]]`, where
`∂W⁻¹ = φ′·[[−sin φ, −cos φ],[cos φ, −sin φ]]` is the entrywise momentum-derivative of the
inverse rotation.  This is the operator source of Lock Eq. (2.24)'s third term: the
transformed position `x̂ = iℏ∂_p + iℏW(∂W⁻¹)` acquires a purely energy-sign-mixing piece,
which evolves at the gap frequency — the Zitterbewegung. -/
theorem foldyRotation_connection (φ φd : ℝ) :
    foldyRotation φ
        * (φd • !![-Real.sin φ, -Real.cos φ; Real.cos φ, -Real.sin φ])
      = φd • !![0, -1; 1, 0] := by
  have hcore : foldyRotation φ * !![-Real.sin φ, -Real.cos φ; Real.cos φ, -Real.sin φ]
      = !![0, -1; 1, 0] := by
    unfold foldyRotation
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linarith [Real.sin_sq_add_cos_sq φ]
  rw [Matrix.mul_smul, hcore]

/-- **The connection strength** `ℏφ′ = ℏm/(2(m²+p²)) = ℏm/2E²` — the amplitude of the
energy-sign-mixing part of the transformed position operator. -/
def foldyConnectionStrength (ħ m p : ℝ) : ℝ := ħ * m / (2 * (m ^ 2 + p ^ 2))

/-- **At rest the connection strength is the Zitterbewegung amplitude**:
`ℏ/2m` — half the reduced Compton wavelength, the amplitude observed directly in the
condensate analogue (`zbwAmplitude`, `zbwAmplitude_eq_half_comptonWavelength`). -/
theorem foldyConnectionStrength_rest (ħ m : ℝ) (hm : m ≠ 0) :
    foldyConnectionStrength ħ m 0 = zbwAmplitude m 1 ħ := by
  unfold foldyConnectionStrength zbwAmplitude
  rw [show m * 1 = m from mul_one m]
  field_simp
  try ring

/-- **The connection vanishes exactly when the mass does** — the wave-packet face of
`zitterVelocity1_oneD_eq_zero_iff`: massless modes have no energy-sign-mixing position
component and no Zitterbewegung; the mass is the source. -/
theorem foldyConnectionStrength_eq_zero_iff (ħ m p : ℝ) (hħ : ħ ≠ 0) :
    foldyConnectionStrength ħ m p = 0 ↔ m = 0 := by
  unfold foldyConnectionStrength
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hden
    · rcases mul_eq_zero.mp hnum with h' | h'
      · exact absurd h' hħ
      · exact h'
    · nlinarith [sq_nonneg m, sq_nonneg p, hden]
  · intro h
    rw [h]
    simp

end PositionOperator

section EnergySignMetric

/-!
# The energy-sign quantum metric: entanglement distance, QIF rest frame, Euclidean weight

The Lock arc left three loose wires into the rest of the repository: the
Foldy–Wouthuysen connection (a momentum-dependent rotation), the quantum-inertial-frame
(QIF) sector (metric structure from quantum-informational data), and the Euclidean path
integral (Cameron weights, and the gravitational saddle whose value is the horizon
entropy).  This module joins them.

* **§A — the metric from state distinguishability.**  The FW rotation prepares the
  energy-sign state `u(p) = (cos φ(p), sin φ(p))` at each momentum, with
  `φ = ½·arctan(p/m)`.  The overlap between modes is `cos(φ(p) − φ(q))`
  (`energySignState_overlap`), so the angle difference is an information distance on the
  momentum line: symmetric, triangular, and separating exactly when the mass is nonzero
  (`energySignDistance_eq_zero_iff` — massless modes carry a degenerate metric, the
  metric face of "no mass, no Zitterbewegung").  Its density is the FW connection:
  `energySignDistance_integral` shows the distance is the integral of `m/(2(m²+p²))` —
  **the entanglement metric on momentum space and the Zitterbewegung amplitude are the
  same object**, the geometric face of `foldyConnectionStrength`.  This is the
  state-distinguishability face of distance-from-information; the bond-count face is
  `CalibratedDistance.IsEntanglementCalibrated` (`r = ℓ·log K`).
* **§B — the compactification.**  The total information length of the momentum line is
  `π/2` for *every* positive mass (`energySign_momentumLine_length`): the energy-sign
  qubit sweeps a fixed quarter turn from `p = −∞` to `p = +∞`.  The mass sets only where
  the metric concentrates (the scale `|p| ≲ m`, which is the Zitterbewegung localization
  scale), never the total — a mass-independent geometric invariant of the free Dirac
  bundle.
* **§C — the QIF welds.**  `canonicalHamiltonian_is_restFrame`: the canonical (Foldy)
  Hamiltonian *is* the rest-frame Dirac Hamiltonian at mass `E` — the FW rotation is the
  quantum boost-to-rest, the operator face of `RestFrameQIFConsistency.boost_to_rest_frame`.
  `restMassSq_onShell`: the QIF metric norm `E² − p²` of on-shell frame data is `m²` —
  the same invariant that is the trembling operator (`zitterVelocity1_oneD`) and the §A
  metric scale.  One mass, four faces: Lorentzian norm, rest-frame gap, trembling
  amplitude, metric concentration.
* **§D — the Euclidean weight.**  The evolved packet's Lorentzian phase continues, at
  imaginary time, to a positive damping factor `e^{−E(p)τ/ℏ}`
  (`euclideanPacket_eq_wick_rotation`, `euclideanPacket_norm`) — the one-mode Cameron
  weight of the Euclidean path integral (`QuantumInertialFrameEuclidean.euclideanCameronWeight`),
  at the rest energy the Compton envelope `e^{−mc²τ/ℏ}`.  The gravitational face of the
  same functional is already formalized: the Euclidean saddle action *is* the horizon
  entropy (`lovelockHorizonEntropy_einstein_eq_euclideanSaddleAction`).  The chain
  packet phase → Euclidean weight → saddle value → entropy is what "the quantum gravity
  path integral processes information" means at the level the repository carries.

* **§E — the three faces of the Compton scale, and the Bell imprint.**  The trinity
  module carries the time face (`ω_Z = 2ω_C`) and the space–time conversion
  (`λ_C·ω_C = c`); this module's connection strength is the momentum face, and
  `foldyConnectionStrength_rest_eq_half_comptonWavelength` joins it to the trinity's
  wavelength through the observed condensate amplitude.  `compton_three_faces` assembles
  all three.  The vacuum Bell envelope of `ComptonVacuumBell` decays over the *same*
  `λ_C` at the local-Lorentz-gauge-invariant proper separation, and
  `vacuumBell_at_trembling_amplitude` shows the trembling amplitude is imprinted on it
  universally: at proper separation equal to the Zitterbewegung amplitude the envelope
  sits at `C₀·e^{−1/2}`, for every mass.

* **§F — the Nagao–Nielsen contour system.**  The Foldy–Dirac mass-shell contour
  `q = E + i|p|` carries two quadratic invariants: the NN Lorentzian form
  `L(q) = E² − p²`, which is *the same function* as the QIF metric norm
  (`contour_lorentzianForm_eq_restMassSq`), and the modulus `|q|² = E² + p²`.  On shell
  `L(q) = m²` (the NN energy–momentum relation), and the closing equation
  `foldyConnectionStrength · (|q|² + L(q)) = ℏm`
  (`connection_times_contour_invariants`) determines the trembling amplitude from the
  contour data.  `nagao_nielsen_contour_system` assembles the four equations; its unique
  rest solution is the Compton momentum face `λ_C/2`.

* **§G — the system on spacetime.**  The NN energy–momentum form re-evaluated with the
  spacetime metrics: the Minkowski contraction of the four-momentum, the QIF norm, and
  the contour's Lorentzian form are one quadratic form (`fourMomentum_minkowski_norm`);
  the flat tetrad reconstructs `η` (`tetradMetric_identity`); and the mass-shell relation
  is the local-Lorentz-gauge-invariant tetrad evaluation, holding in every frame
  (`nn_massShell_every_frame`).  `contour_system_spacetime` re-assembles the system in
  the three metric presentations — the trembling amplitude inherits local Lorentz gauge
  invariance from the tetrad metric.

* **§H — the Yukawa Compton clock and the dilation group.**  At the Yukawa mass fixed
  by the clock identification `m_Y = ℏω/c²` (`DiracCartanComptonYukawaBridge`), the
  system's energy–momentum equation is the clock relation
  (`contour_massShell_yukawaClock`) and the trembling amplitude is the clock reading
  `c²/2ω` (`connection_rest_yukawaClock`).  Under the dilation group
  (`ScaleDilationLogMetric`) the on-shell energy has weight `+1`, the contour form
  `+2`, and the connection strength `−1` — the closing equation is weight-balanced and
  holds on every dilation orbit; the scale-metric distance between wavelength and
  amplitude is the dilaton invariant `log 2`
  (`scaleDistance_wavelength_amplitude`, `contour_system_yukawa_dilaton`).

**Honest layering.**  §A–§B are exact and self-contained (two-level state geometry; no
claim that this is the full Fubini–Study machinery on projective Hilbert space).  §C–§H
are welds: the QIF worldline theory, the full Cameron-weight functional, the
gravitational saddle, the gauge-invariant Bell decay, the contour path-integral weights,
the tetrad-metric gauge theory, the Yukawa mass-clock identification, and the dilation
log-metric live in their own modules and are joined here by identities, not re-derived.
-/

open Real Matrix Filter
open Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung
open Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation
open Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
open Physlib.QuantumMechanics.ComplexAction.ComplexActionContourUnification
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric

/-! ### §A — the metric from state distinguishability -/

/-- **The energy-sign state** prepared by the FW rotation at angle `φ`: the two-level
unit vector `(cos φ, sin φ)` giving the positive/negative energy content of a mode. -/
def energySignState (φ : ℝ) : Fin 2 → ℝ := ![Real.cos φ, Real.sin φ]

/-- **The overlap between energy-sign states is the cosine of the angle difference** —
state distinguishability depends only on the relative FW angle. -/
theorem energySignState_overlap (φ ψ : ℝ) :
    energySignState φ ⬝ᵥ energySignState ψ = Real.cos (φ - ψ) := by
  simp [energySignState, dotProduct, Fin.sum_univ_two]
  rw [Real.cos_sub]

/-- **The information distance between momentum modes**: the FW angle separation
`|φ(p) − φ(q)|` — zero overlap deficit, zero distance. -/
def energySignDistance (m p q : ℝ) : ℝ :=
  |bogoliubovAngle m p - bogoliubovAngle m q|

theorem energySignDistance_comm (m p q : ℝ) :
    energySignDistance m p q = energySignDistance m q p :=
  abs_sub_comm _ _

theorem energySignDistance_triangle (m p q r : ℝ) :
    energySignDistance m p q ≤ energySignDistance m p r + energySignDistance m r q :=
  abs_sub_le _ _ _

/-- **The metric separates modes exactly when the mass is nonzero**: for `m ≠ 0` the
distance vanishes only at equal momenta (the arctangent is injective); for `m = 0` every
distance is zero — massless modes have a fully degenerate energy-sign metric, the metric
face of "no mass, no Zitterbewegung". -/
theorem energySignDistance_eq_zero_iff (m p q : ℝ) (hm : m ≠ 0) :
    energySignDistance m p q = 0 ↔ p = q := by
  unfold energySignDistance bogoliubovAngle
  rw [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h
    have h2 : Real.arctan (p / m) = Real.arctan (q / m) := by linarith [h]
    have h3 := Real.arctan_injective h2
    field_simp at h3
    exact h3
  · intro h
    rw [h]

/-- **The distance is the integral of the connection strength** — the entanglement metric
on momentum space has density `φ′(p) = m/(2(m²+p²))`, which is `foldyConnectionStrength`
divided by `ℏ`: the metric that state distinguishability puts on the momentum line and
the amplitude of the position operator's energy-sign-mixing part are one object. -/
theorem energySignDistance_integral (m p q : ℝ) (hm : 0 < m) (hpq : p ≤ q) :
    energySignDistance m p q = ∫ x in p..q, m / (2 * (m ^ 2 + x ^ 2)) := by
  have hmono : bogoliubovAngle m p ≤ bogoliubovAngle m q := by
    unfold bogoliubovAngle
    have hdiv : p / m ≤ q / m := by gcongr
    have harc := Real.arctan_le_arctan_iff.mpr hdiv
    linarith [harc]
  have hftc : (∫ x in p..q, m / (2 * (m ^ 2 + x ^ 2)))
      = bogoliubovAngle m q - bogoliubovAngle m p := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => bogoliubovAngle_hasDerivAt m x hm.ne') ?_
    have hcont : Continuous fun x : ℝ => m / (2 * (m ^ 2 + x ^ 2)) := by
      refine Continuous.div continuous_const (by fun_prop) fun x => ?_
      positivity
    exact hcont.intervalIntegrable p q
  rw [hftc]
  unfold energySignDistance
  rw [abs_sub_comm, abs_of_nonneg (by linarith [hmono])]

/-! ### §B — the compactification: total length `π/2`, for every mass -/

/-- The symmetric-interval distance in closed form: `|arctan(R/m)|`. -/
theorem energySignDistance_symm_interval (m R : ℝ) :
    energySignDistance m (-R) R = |Real.arctan (R / m)| := by
  unfold energySignDistance bogoliubovAngle
  rw [neg_div, Real.arctan_neg]
  rw [show -Real.arctan (R / m) / 2 - Real.arctan (R / m) / 2
      = -(Real.arctan (R / m)) from by ring]
  rw [abs_neg]

/-- **The momentum line has total information length `π/2` in the energy-sign metric, for
every positive mass.**  The energy-sign qubit sweeps a fixed quarter turn from `p = −∞`
to `p = +∞`; the mass sets where the metric concentrates (`|p| ≲ m`, the Zitterbewegung
localization scale) but never the total — a mass-independent invariant of the free Dirac
bundle. -/
theorem energySign_momentumLine_length (m : ℝ) (hm : 0 < m) :
    Tendsto (fun R => energySignDistance m (-R) R) atTop (nhds (π / 2)) := by
  have harg : Tendsto (fun R : ℝ => R / m) atTop atTop :=
    tendsto_id.atTop_div_const hm
  have htan : Tendsto (fun R : ℝ => Real.arctan (R / m)) atTop (nhds (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg
  have habs : Tendsto (fun R : ℝ => |Real.arctan (R / m)|) atTop (nhds |π / 2|) :=
    htan.abs
  rw [abs_of_nonneg (by positivity)] at habs
  exact habs.congr fun R => (energySignDistance_symm_interval m R).symm

/-! ### §C — the QIF welds: rest frame and metric norm -/

/-- **The canonical representation is the quantum rest frame**: the canonical (Foldy)
Hamiltonian `E·β` is definitionally the rest-frame Dirac Hamiltonian at mass `E`.  The
FW rotation that produces it is the quantum boost-to-rest — the operator face of the QIF
statement `RestFrameQIFConsistency.boost_to_rest_frame` that every subluminal frame
boosts to rest. -/
theorem canonicalHamiltonian_is_restFrame (E : ℝ) :
    canonicalHamiltonian E = diracHamiltonian4 0 0 0 E :=
  (restFrame_hamiltonian E).symm

/-- **The QIF metric norm of on-shell frame data is the mass**: `E² − p² = m²` for
`E = √(m² + p²)`.  The invariant that the quantum-inertial-frame sector reads as the
Lorentzian metric norm (`restMass_is_metric_norm`) is the same quantity that is the
trembling operator (`zitterVelocity1_oneD`), the rest gap, and the §A metric scale. -/
theorem restMassSq_onShell (m p : ℝ) :
    restMassSq (bogoliubovEnergy m p) p = m ^ 2 := by
  unfold restMassSq bogoliubovEnergy
  rw [Real.sq_sqrt (by positivity)]
  ring

/-! ### §D — the Euclidean weight: the packet phase continued to imaginary time -/

/-- **The Euclidean packet**: the evolved packet at imaginary time — a positive damping
`e^{−E(p)τ/ℏ}` replacing the unimodular phase. -/
def euclideanPacket (ħ τ : ℝ) (E : ℝ → ℝ) (a : ℝ → ℂ) (p : ℝ) : ℂ :=
  ((Real.exp (-(E p * τ / ħ)) : ℝ) : ℂ) * a p

/-- **The Euclidean packet is the Wick rotation of the evolved packet**: substituting
`t = −iτ` into the Lorentzian phase `e^{−iE·t/ℏ}` yields exactly the real damping
`e^{−Eτ/ℏ}` — the analytic continuation joining the §B packet dynamics of
the `PositionOperator` section to the Euclidean path-integral weight. -/
theorem euclideanPacket_eq_wick_rotation (ħ τ : ℝ) (E : ℝ → ℝ) (a : ℝ → ℂ) (p : ℝ) :
    euclideanPacket ħ τ E a p
      = Complex.exp (-Complex.I * ((E p : ℝ) : ℂ)
          * (-Complex.I * ((τ / ħ : ℝ) : ℂ))) * a p := by
  unfold euclideanPacket
  congr 1
  rw [show -Complex.I * ((E p : ℝ) : ℂ) * (-Complex.I * ((τ / ħ : ℝ) : ℂ))
      = ((-(E p * τ / ħ) : ℝ) : ℂ) from by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring]
  push_cast
  ring

/-- **The Euclidean weight is a positive damping of the amplitude** — the one-mode
Cameron weight: `‖ψ_E(p)‖ = e^{−E(p)τ/ℏ}·‖a(p)‖`.  At the rest energy this is the
Compton envelope `e^{−mc²τ/ℏ}`; the gravitational face of the same Euclidean functional
is the saddle whose value is the horizon entropy. -/
theorem euclideanPacket_norm (ħ τ : ℝ) (E : ℝ → ℝ) (a : ℝ → ℂ) (p : ℝ) :
    ‖euclideanPacket ħ τ E a p‖ = Real.exp (-(E p * τ / ħ)) * ‖a p‖ := by
  unfold euclideanPacket
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-! ### §E — the three faces of the Compton scale, and the Bell imprint -/

/-- **The connection strength at rest is half the trinity's Compton wavelength** — the
momentum face joined to the space face through the observed condensate amplitude:
`foldyConnectionStrength(0) = zbwAmplitude = λ_C/2` (units `c = 1`). -/
theorem foldyConnectionStrength_rest_eq_half_comptonWavelength (ħ m : ℝ) (hm : m ≠ 0) :
    foldyConnectionStrength ħ m 0 = comptonWavelength m 1 ħ / 2 := by
  rw [foldyConnectionStrength_rest ħ m hm, zbwAmplitude_eq_half_comptonWavelength]

/-- **The three faces of the Compton scale** (units `c = 1`): the time face — the
Zitterbewegung frequency is twice the Compton clock; the conversion — wavelength times
frequency is the invariant speed; the momentum face — the FW connection strength at rest
is half the wavelength.  One invariant, three proven readings, each living in its own
sector (clock, propagation, position-operator geometry). -/
theorem compton_three_faces (m ħ : ℝ) (hm : 0 < m) (hħ : ħ ≠ 0) :
    zitterbewegungFrequency 0 m 1 ħ = 2 * comptonFrequency m 1 ħ
      ∧ comptonWavelength m 1 ħ * comptonFrequency m 1 ħ = 1
      ∧ foldyConnectionStrength ħ m 0 = comptonWavelength m 1 ħ / 2 :=
  ⟨zitterbewegung_rest_eq_two_compton m 1 ħ hm.le,
   comptonWavelength_mul_comptonFrequency m 1 ħ hm.ne' one_ne_zero hħ,
   foldyConnectionStrength_rest_eq_half_comptonWavelength ħ m hm.ne'⟩

/-- **The trembling amplitude is imprinted on the vacuum Bell envelope, universally**: at
proper separation equal to the Zitterbewegung amplitude (the rest connection strength),
the Compton-decay Bell envelope sits at `C₀·e^{−1/2}` — the same value for every mass,
because the amplitude is half the decay length.  Through
`ComptonVacuumBell.vacuumBell_compton_tetrad_gauge_invariant` the separation at which
this happens is a local-Lorentz-gauge-invariant proper distance, so the imprint is
frame-independent. -/
theorem vacuumBell_at_trembling_amplitude (C₀ m ħ : ℝ) (hm : m ≠ 0) (hħ : ħ ≠ 0) :
    chshEnvelope (C₀ * Real.exp (-(foldyConnectionStrength ħ m 0 / comptonWavelength m 1 ħ)))
      = chshEnvelope (C₀ * Real.exp (-(1 / 2 : ℝ))) := by
  rw [foldyConnectionStrength_rest_eq_half_comptonWavelength ħ m hm]
  have hlam : comptonWavelength m 1 ħ ≠ 0 := by
    unfold comptonWavelength
    simp [hm, hħ]
  have hr : comptonWavelength m 1 ħ / 2 / comptonWavelength m 1 ħ = 1 / 2 := by
    field_simp
  rw [hr]

/-! ### §F — the Nagao–Nielsen contour system: the trembling amplitude from the
contour's two invariants -/

/-- **The Nagao–Nielsen Lorentzian form of the Foldy–Dirac contour is the QIF metric
norm**: `L(E + i|p|) = E² − p² = restMassSq E p`, at every `(E, p)`.  The contour's
quadratic form and the quantum-inertial-frame metric norm are one function. -/
theorem contour_lorentzianForm_eq_restMassSq (E p : ℝ) :
    lorentzianForm (foldyDiracMassShellContour E p 0 0) = restMassSq E p := by
  rw [foldyDiracMassShellContour_lorentzianForm]
  unfold spatialMomentumSq restMassSq
  ring

/-- **On shell, the contour's Lorentzian form is the mass squared** — the Nagao–Nielsen
energy–momentum relation `L(q) = m²` for `q = E(p) + i|p|` at the on-shell energy. -/
theorem contour_lorentzianForm_onShell (m p : ℝ) :
    lorentzianForm (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0) = m ^ 2 := by
  rw [contour_lorentzianForm_eq_restMassSq]
  exact restMassSq_onShell m p

/-- **The contour's modulus**: `|E + i|p||² = E² + p²` — the second quadratic invariant
of the Nagao–Nielsen contour, the Euclidean companion of the Lorentzian form. -/
theorem contour_normSq (E p : ℝ) :
    Complex.normSq (foldyDiracMassShellContour E p 0 0) = E ^ 2 + p ^ 2 := by
  unfold foldyDiracMassShellContour
  rw [Complex.normSq_add_mul_I]
  rw [Real.sq_sqrt (spatialMomentumSq_nonneg p 0 0)]
  unfold spatialMomentumSq
  ring

/-- **The system's closing equation**: the Foldy–Wouthuysen connection strength times the
*sum of the contour's two invariants* is `ℏm`:

  `foldyConnectionStrength · (|q|² + L(q)) = ℏ·m`,  `q = E(p) + i|p|` on shell.

The sum `|q|² + L(q) = 2E²` is twice the squared on-shell energy, so the trembling
amplitude is fully determined by the Nagao–Nielsen contour data — and conversely the
contour invariants can be read off the Zitterbewegung. -/
theorem connection_times_contour_invariants (ħ m p : ℝ) (hm : m ≠ 0) :
    foldyConnectionStrength ħ m p
        * (Complex.normSq (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0)
          + lorentzianForm (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0))
      = ħ * m := by
  rw [contour_normSq, contour_lorentzianForm_onShell]
  have hE2 : bogoliubovEnergy m p ^ 2 = m ^ 2 + p ^ 2 := Real.sq_sqrt (by positivity)
  rw [hE2]
  unfold foldyConnectionStrength
  have hne : m ^ 2 + p ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The Nagao–Nielsen contour system** — the momentum face of the Compton scale written
as a system of equations with the NN energy–momentum and contour data (units `c = 1`,
`q = E(p) + i|p|` the Foldy–Dirac mass-shell contour):

1. `L(q) = restMassSq E p` — the NN Lorentzian form is the QIF metric norm;
2. `L(q) = m²` on shell — the NN energy–momentum relation;
3. `foldyConnectionStrength · (|q|² + L(q)) = ℏm` — the trembling amplitude from the
   contour's two invariants;
4. `foldyConnectionStrength(0) = λ_C/2` — the rest solution of the system is the
   Compton face, closing the loop with `compton_three_faces`.

Solving 2–3 at `p = 0` gives `|q|² + L(q) = 2m²`, hence the amplitude `ℏ/2m`: the
Zitterbewegung scale is the unique rest solution of the contour system.  The contour's
history weight, with imaginary action `|p|` and entropy `S_ent = 2|p|/ℏ`, is the
already-formalized `foldyDiracContourWeight_eq_historyWeight`. -/
theorem nagao_nielsen_contour_system (ħ m p : ℝ) (hm : 0 < m) :
    lorentzianForm (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0)
        = restMassSq (bogoliubovEnergy m p) p
      ∧ lorentzianForm (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0) = m ^ 2
      ∧ foldyConnectionStrength ħ m p
          * (Complex.normSq (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0)
            + lorentzianForm (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0))
        = ħ * m
      ∧ foldyConnectionStrength ħ m 0 = comptonWavelength m 1 ħ / 2 :=
  ⟨contour_lorentzianForm_eq_restMassSq _ _,
   contour_lorentzianForm_onShell m p,
   connection_times_contour_invariants ħ m p hm.ne',
   foldyConnectionStrength_rest_eq_half_comptonWavelength ħ m hm.ne'⟩

/-! ### §G — the system on spacetime: Minkowski metric and tetrad metric faces -/

/-- **The `1+1` four-momentum** `k = (E, p)` on the spacetime index type — the vector the
spacetime metrics contract. -/
def fourMomentum (E p : ℝ) : (Fin 1 ⊕ Fin 1) → ℝ := Sum.elim ![E] ![p]

/-- **The Minkowski face of the NN energy–momentum form**: the flat spacetime metric
`η = diag(1, −1)` contracts the four-momentum to `E² − p² = restMassSq E p` — the same
function as the contour's Lorentzian form (`contour_lorentzianForm_eq_restMassSq`).  The
NN contour form, the QIF norm, and the Minkowski quadratic form are one object. -/
theorem fourMomentum_minkowski_norm (E p : ℝ) :
    fourMomentum E p ⬝ᵥ (minkowskiMatrix *ᵥ fourMomentum E p) = restMassSq E p := by
  unfold fourMomentum restMassSq minkowskiMatrix
  simp [LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.diagonal]
  ring

/-- **The flat tetrad reconstructs the Minkowski metric**: `g[1] = 1ᵀ·η·1 = η` — the
identity cotetrad is flat spacetime, the Levi-Civita-trivial case of the tetrad
metric. -/
theorem tetradMetric_identity :
    tetradMetric (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) = minkowskiMatrix := by
  unfold tetradMetric
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- **The tetrad face**: at the flat tetrad, the proper-separation quadratic form of the
four-momentum is the QIF norm `restMassSq` — the tetrad spacetime metric evaluates the
NN energy–momentum form. -/
theorem fourMomentum_properSeparation_flat (E p : ℝ) :
    properSeparationSq (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (fourMomentum E p)
      = restMassSq E p := by
  unfold properSeparationSq
  rw [tetradMetric_identity]
  exact fourMomentum_minkowski_norm E p

/-- **The NN mass-shell relation holds in every local Lorentz frame**: for any
`Λ ∈ SO(1,1)`, the tetrad quadratic form of the on-shell four-momentum in the rotated
frame `Λ·1` is `m²`.  The system's energy–momentum equation is not a coordinate
statement — it is the local-Lorentz-gauge-invariant tetrad evaluation, the same
invariance that `ComptonVacuumBell` proves for the Bell-decay separation. -/
theorem nn_massShell_every_frame (m p : ℝ)
    {Λ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ} (hΛ : Λ ∈ LorentzGroup 1) :
    properSeparationSq (Λ * 1) (fourMomentum (bogoliubovEnergy m p) p) = m ^ 2 := by
  rw [properSeparationSq_lorentz_gauge hΛ, fourMomentum_properSeparation_flat]
  exact restMassSq_onShell m p

/-- **The contour system, re-evaluated on spacetime** (units `c = 1`): the Nagao–Nielsen
energy–momentum equation of `nagao_nielsen_contour_system` holds identically in three
metric presentations —

1. the contour's Lorentzian form equals the Minkowski contraction of the four-momentum;
2. the tetrad form of the on-shell four-momentum is `m²` in *every* local Lorentz frame;
3. the closing equation `foldyConnectionStrength · (|q|² + L(q)) = ℏm` is untouched by
   the frame choice, since both invariants are built from the frame-independent `(E, p)`
   scalars.

The trembling amplitude therefore inherits local Lorentz gauge invariance from the
tetrad metric: every observer extracts the same `ℏm/2E²` from the contour data. -/
theorem contour_system_spacetime (ħ m p : ℝ) (hm : 0 < m)
    {Λ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ} (hΛ : Λ ∈ LorentzGroup 1) :
    lorentzianForm (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0)
        = fourMomentum (bogoliubovEnergy m p) p
            ⬝ᵥ (minkowskiMatrix *ᵥ fourMomentum (bogoliubovEnergy m p) p)
      ∧ properSeparationSq (Λ * 1) (fourMomentum (bogoliubovEnergy m p) p) = m ^ 2
      ∧ foldyConnectionStrength ħ m p
          * (Complex.normSq (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0)
            + lorentzianForm (foldyDiracMassShellContour (bogoliubovEnergy m p) p 0 0))
        = ħ * m := by
  refine ⟨?_, nn_massShell_every_frame m p hΛ,
    connection_times_contour_invariants ħ m p hm.ne'⟩
  rw [contour_lorentzianForm_eq_restMassSq, fourMomentum_minkowski_norm]

/-! ### §H — the Yukawa Compton clock and the dilation group -/

/-- The Yukawa mass identified with the Compton clock is nonzero for a ticking clock. -/
theorem yukawaMass_ne_zero (D : DiracCartanComptonYukawaData) (hω : D.omega ≠ 0) :
    yukawaMass D.y D.v ≠ 0 := by
  rw [D.massClock]
  unfold comptonMass
  exact div_ne_zero (mul_ne_zero D.hbar_ne hω) (pow_ne_zero 2 D.c_ne)

/-- **The contour system reads the Yukawa Compton clock**: at the Yukawa mass fixed by
the clock identification `m_Y = ℏω/c²`, the on-shell NN Lorentzian form is the squared
clock mass — the energy–momentum equation of the system *is* the clock relation. -/
theorem contour_massShell_yukawaClock (D : DiracCartanComptonYukawaData) (p : ℝ) :
    lorentzianForm (foldyDiracMassShellContour
        (bogoliubovEnergy (yukawaMass D.y D.v) p) p 0 0)
      = comptonMass D.omega D.c D.hbar ^ 2 := by
  rw [contour_lorentzianForm_onShell, D.massClock]

/-- **The Yukawa fermion's trembling amplitude is set by the clock frequency**:
`ℏ/2m_Y = c²/2ω`.  The rest solution of the contour system, evaluated at the
Yukawa–Compton mass, is half the inverse clock frequency (times `c²`) — the
Zitterbewegung scale of the Yukawa-massed fermion is a clock reading. -/
theorem connection_rest_yukawaClock (D : DiracCartanComptonYukawaData)
    (hω : D.omega ≠ 0) :
    foldyConnectionStrength D.hbar (yukawaMass D.y D.v) 0
      = D.c ^ 2 / (2 * D.omega) := by
  have hmY := yukawaMass_ne_zero D hω
  have hres := yukawaClock_restEnergy D
  rw [foldyConnectionStrength_rest D.hbar _ hmY]
  unfold zbwAmplitude
  field_simp
  linear_combination hres

/-- **The on-shell energy is homogeneous of degree one under the dilation group**:
`E(μm, μp) = μ·E(m, p)`. -/
theorem bogoliubovEnergy_dilation (μ m p : ℝ) (hμ : 0 ≤ μ) :
    bogoliubovEnergy (μ * m) (μ * p) = μ * bogoliubovEnergy m p := by
  unfold bogoliubovEnergy
  rw [show (μ * m) ^ 2 + (μ * p) ^ 2 = μ ^ 2 * (m ^ 2 + p ^ 2) from by ring,
    Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ]

/-- **The connection strength carries dilation weight `−1`** — it scales as a length:
`foldyConnectionStrength(μm, μp) = foldyConnectionStrength(m, p)/μ`.  The contour's
Lorentzian form carries weight `+2` (`contourForm_dilation`), and the closing equation
`connection · (|q|² + L) = ℏm` is weight-balanced: `(−1) + 2 = +1`, matching `ℏm`. -/
theorem foldyConnectionStrength_dilation (ħ μ m p : ℝ) (hm : m ≠ 0) (hμ : μ ≠ 0) :
    foldyConnectionStrength ħ (μ * m) (μ * p) = foldyConnectionStrength ħ m p / μ := by
  unfold foldyConnectionStrength
  have h1 : m ^ 2 + p ^ 2 ≠ 0 := by positivity
  field_simp
  try ring

/-- **The contour form carries dilation weight `+2`** — the mass-squared weight. -/
theorem contourForm_dilation (μ E p : ℝ) :
    lorentzianForm (foldyDiracMassShellContour (μ * E) (μ * p) 0 0)
      = μ ^ 2 * lorentzianForm (foldyDiracMassShellContour E p 0 0) := by
  rw [contour_lorentzianForm_eq_restMassSq, contour_lorentzianForm_eq_restMassSq]
  unfold restMassSq
  ring

/-- **The dilaton-invariant of the system is `log 2`**: in the scale (log) metric — the
metric the dilation group acts on by isometries (`dilation_isometry`) — the distance
between the Compton wavelength and the trembling amplitude is exactly `log 2`, for every
mass.  The dimensionful faces of the system all slide along dilation orbits; their
ratios, like the Bell half-fall imprint `e^{−1/2}` and this `log 2`, are the
scale-invariant observables. -/
theorem scaleDistance_wavelength_amplitude (ħ m : ℝ) (hm : m ≠ 0) (hħ : ħ ≠ 0) :
    scaleDistance (comptonWavelength m 1 ħ) (foldyConnectionStrength ħ m 0)
      = Real.log 2 := by
  rw [foldyConnectionStrength_rest_eq_half_comptonWavelength ħ m hm]
  unfold scaleDistance
  have hlam : comptonWavelength m 1 ħ ≠ 0 := by
    unfold comptonWavelength
    simp [hm, hħ]
  rw [show comptonWavelength m 1 ħ / (comptonWavelength m 1 ħ / 2) = 2 from by
    field_simp]
  exact abs_of_nonneg (Real.log_nonneg one_le_two)

/-- **The contour system with the Yukawa Compton clock and the dilation group**: the
energy–momentum equation reads the clock (`L(q) = m_Y² = (ℏω/c²)²`); the trembling
amplitude is the clock reading `c²/2ω`; the closing equation holds on the whole dilation
orbit `(μm_Y, μp)`; and the scale-metric distance between wavelength and amplitude is
the dilaton invariant `log 2`. -/
theorem contour_system_yukawa_dilaton (D : DiracCartanComptonYukawaData)
    (hω : D.omega ≠ 0) (μ p : ℝ) (hμ : 0 < μ) :
    lorentzianForm (foldyDiracMassShellContour
        (bogoliubovEnergy (yukawaMass D.y D.v) p) p 0 0)
      = comptonMass D.omega D.c D.hbar ^ 2
      ∧ foldyConnectionStrength D.hbar (yukawaMass D.y D.v) 0
        = D.c ^ 2 / (2 * D.omega)
      ∧ foldyConnectionStrength D.hbar (μ * yukawaMass D.y D.v) (μ * p)
          * (Complex.normSq (foldyDiracMassShellContour
              (bogoliubovEnergy (μ * yukawaMass D.y D.v) (μ * p)) (μ * p) 0 0)
            + lorentzianForm (foldyDiracMassShellContour
              (bogoliubovEnergy (μ * yukawaMass D.y D.v) (μ * p)) (μ * p) 0 0))
        = D.hbar * (μ * yukawaMass D.y D.v)
      ∧ scaleDistance (comptonWavelength (yukawaMass D.y D.v) 1 D.hbar)
          (foldyConnectionStrength D.hbar (yukawaMass D.y D.v) 0)
        = Real.log 2 :=
  ⟨contour_massShell_yukawaClock D p,
   connection_rest_yukawaClock D hω,
   connection_times_contour_invariants D.hbar _ _
     (mul_ne_zero hμ.ne' (yukawaMass_ne_zero D hω)),
   scaleDistance_wavelength_amplitude D.hbar _ (yukawaMass_ne_zero D hω) D.hbar_ne⟩

end EnergySignMetric

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.representation_dichotomy where
  formalizes @ "claim:zitterbewegung-is-representation-contingent-the-canonical-velocity-commutes-with-the-canonical-hamiltonian-while-the-dirac-velocity-fails-to-commute-although-both-hamiltonians-share-the-energy-sign-spectrum-through-the-foldy-wouthuysen-rotation",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.fw_intertwine",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.velocity_heisenberg_derivative",
  caveat @ "claim:the-newton-wigner-operator-and-the-one-dimensional-wave-packet-mean-position-are-carried-by-newtonwignerpositionoperator-the-three-dimensional-packet-integrals-and-the-dressed-interaction-kernel-remain-open"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.zitterVelocity1_oneD where
  formalizes @ "claim:the-one-dimensional-trembling-part-of-the-dirac-velocity-is-exactly-the-mass-times-beta-alpha-so-the-zitterbewegung-operator-vanishes-precisely-when-the-mass-does",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.zitterVelocity1",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.trembling_free_iff_null where
  derives @ "claim:the-one-dimensional-dirac-mode-hamiltonian-commutes-with-both-velocity-and-energy-sign-exactly-when-momentum-and-mass-vanish-so-position-simple-and-sign-preserving-hold-jointly-only-for-trivial-dynamics",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.galileanModeSymbol_central where
  formalizes @ "claim:the-free-galilean-mode-symbol-is-scalar-so-every-operator-is-a-constant-of-its-motion-and-position-simplicity-and-interaction-locality-hold-in-the-same-representation",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.fwOperator_scalar_iff where
  derives @ "claim:the-foldy-wouthuysen-operator-is-a-scalar-matrix-exactly-at-vanishing-momentum-so-the-canonical-representation-map-dresses-every-moving-mode-nontrivially-and-local-interactions-cannot-stay-local",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.fwOperator_concrete",
  caveat @ "claim:the-integral-kernel-form-of-the-dressed-interaction-between-canonical-modes-is-not-formalized-this-is-the-mode-level-mechanism"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.meanPosition_linear_wavePacket where
  formalizes @ "claim:the-newton-wigner-position-operator-on-momentum-space-wave-functions-is-the-fujiwara-time-operator-under-the-energy-to-momentum-reading-and-the-single-sign-packet-mean-position-is-initial-position-plus-group-velocity-times-time",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.time_energy_ccr",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.generalizedTimeKet_eigen",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.canonicalVelocity1_commute",
  caveat @ "claim:one-momentum-dimension-matching-the-repositorys-l2-packaging-the-three-dimensional-packet-integrals-remain-open"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.evolvedPacket_position_density where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.canonicalVelocity1_commute",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.evolutionPhase_conj_mul",
  formalizes @ "claim:the-evolution-phase-cancels-pointwise-in-the-position-density-of-a-single-sign-packet-so-nothing-oscillates-in-the-canonical-representation",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.bogoliubovEnergy_hasDerivAt where
  derives @ "claim:the-on-shell-dispersion-derivative-is-momentum-over-energy-the-group-velocity-that-the-canonical-velocity-operator-carries",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation.bogoliubovEnergy"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.foldyRotation_connection where
  derives @ "claim:the-transformed-position-operator-acquires-a-purely-off-diagonal-foldy-wouthuysen-connection-the-operator-source-of-lock-two-twenty-fours-oscillating-third-term",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.fw_intertwine"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.foldyConnectionStrength_rest where
  derives @ "claim:the-rest-value-of-the-foldy-wouthuysen-connection-strength-is-half-the-reduced-compton-wavelength-the-observed-zitterbewegung-amplitude",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.zbwAmplitude_eq_half_comptonWavelength"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.foldyConnectionStrength_eq_zero_iff where
  derives @ "claim:the-foldy-wouthuysen-connection-vanishes-exactly-when-the-mass-does-the-wave-packet-face-of-the-trembling-equals-mass-identity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.zitterVelocity1_oneD_eq_zero_iff"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.contour_massShell_yukawaClock where
  derives @ "claim:the-contour-systems-energy-momentum-equation-at-the-yukawa-mass-is-the-compton-clock-relation-the-lorentzian-form-reads-the-squared-clock-mass",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.yukawaClock_restEnergy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.isolated_yukawa_from_compton_clock"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.connection_rest_yukawaClock where
  derives @ "claim:the-yukawa-fermions-trembling-amplitude-is-half-the-inverse-clock-frequency-the-zitterbewegung-scale-is-a-clock-reading",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.DiracCartanComptonYukawaBridge.diracHamiltonian4_sq_yukawaClock"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.foldyConnectionStrength_dilation where
  derives @ "claim:the-connection-strength-carries-dilation-weight-minus-one-and-the-contour-form-weight-plus-two-so-the-closing-equation-is-weight-balanced-under-the-dilation-group",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.dilationGroupHom"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.scaleDistance_wavelength_amplitude where
  derives @ "claim:the-scale-metric-distance-between-the-compton-wavelength-and-the-trembling-amplitude-is-log-two-for-every-mass-a-dilaton-invariant-of-the-contour-system",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.dilation_isometry",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ScaleDilationLogMetric.entropicProperDistance_eq_scaleDistance"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.contour_system_yukawa_dilaton where
  derives @ "claim:the-contour-system-instantiated-at-the-yukawa-compton-clock-holds-on-every-dilation-orbit-with-the-log-two-scale-invariant",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsVEVStationary_of_sq_eq_higgsVEVSqFromPotential",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HiggsBoson.higgsVEVSqFromPotential",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitonMassRoleSeparation.yukawaMass_underdetermined",
  caveat @ "claim:the-potential-stationarity-fixing-the-vacuum-value-v-squared-equals-mu-squared-over-lambda-is-carried-by-particles-higgsboson-and-cited-not-rederived-the-mass-value-itself-is-not-fixed-by-the-yukawa-relation-which-is-exactly-solvable-for-every-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.fourMomentum_minkowski_norm where
  formalizes @ "claim:the-minkowski-contraction-of-the-four-momentum-the-qif-norm-and-the-nagao-nielsen-contour-form-are-one-quadratic-form",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.contour_lorentzianForm_eq_restMassSq"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.nn_massShell_every_frame where
  derives @ "claim:the-nagao-nielsen-mass-shell-relation-is-the-local-lorentz-gauge-invariant-tetrad-evaluation-of-the-four-momentum-holding-in-every-frame",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell.properSeparationSq_lorentz_gauge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity.tetradMetric_lorentz_gauge"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.contour_system_spacetime where
  derives @ "claim:the-contour-system-holds-identically-in-the-contour-minkowski-and-tetrad-presentations-so-the-trembling-amplitude-is-local-lorentz-gauge-invariant",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  caveat @ "claim:one-plus-one-dimensional-flat-tetrad-base-the-curved-tetrad-evaluation-with-nontrivial-cotetrad-fields-is-carried-by-the-canonical-tetrad-gravity-sector"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.contour_lorentzianForm_eq_restMassSq where
  formalizes @ "claim:the-nagao-nielsen-lorentzian-form-of-the-foldy-dirac-contour-is-the-quantum-inertial-frame-metric-norm-at-every-energy-and-momentum",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexActionContourUnification.foldyDiracMassShellContour_lorentzianForm",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency.restMassSq"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.connection_times_contour_invariants where
  derives @ "claim:the-foldy-wouthuysen-connection-strength-times-the-sum-of-the-contours-two-quadratic-invariants-is-hbar-times-mass-so-the-trembling-amplitude-is-determined-by-the-nagao-nielsen-contour-data",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexActionContourUnification.foldyDiracContourWeight_eq_historyWeight"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.nagao_nielsen_contour_system where
  derives @ "claim:the-momentum-face-of-the-compton-scale-is-the-unique-rest-solution-of-the-nagao-nielsen-contour-system-joining-the-energy-momentum-relation-the-qif-metric-norm-and-the-trembling-amplitude",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  caveat @ "claim:one-momentum-dimension-on-shell-scalar-system-the-operator-valued-contour-deformation-of-the-full-path-integral-is-carried-by-the-contour-unification-module"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.compton_three_faces where
  derives @ "claim:the-compton-scale-has-three-proven-faces-the-clock-frequency-the-propagation-wavelength-and-the-momentum-space-connection-strength-joined-in-one-theorem",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength_mul_comptonFrequency",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.BoseEinsteinZitterbewegungObservation.zbwAmplitude_eq_half_comptonWavelength"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.vacuumBell_at_trembling_amplitude where
  derives @ "claim:at-proper-separation-equal-to-the-zitterbewegung-amplitude-the-vacuum-bell-envelope-sits-at-the-universal-e-to-minus-one-half-value-for-every-mass-and-the-separation-is-local-lorentz-gauge-invariant",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell.vacuumBell_compton_tetrad_gauge_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell.properSeparationSq_lorentz_gauge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope.chshEnvelope",
  caveat @ "claim:the-gauge-invariance-of-the-separation-is-carried-by-the-tetrad-module-this-theorem-evaluates-the-envelope-at-the-amplitude-scale"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.energySignDistance_integral where
  formalizes @ "claim:the-information-distance-between-momentum-modes-is-the-integral-of-the-foldy-wouthuysen-connection-strength-so-the-entanglement-metric-on-momentum-space-and-the-zitterbewegung-amplitude-are-the-same-object",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:lock-1984-relativistic-invariance-and-zitterbewegung-am-j-phys-52-223",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.bogoliubovAngle_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.CalibratedDistance.IsEntanglementCalibrated",
  caveat @ "claim:two-level-state-geometry-on-the-momentum-line-not-the-full-fubini-study-machinery-on-projective-hilbert-space"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.energySignDistance_eq_zero_iff where
  derives @ "claim:the-energy-sign-metric-separates-momentum-modes-exactly-when-the-mass-is-nonzero-the-metric-face-of-no-mass-no-zitterbewegung",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.zitterVelocity1_oneD_eq_zero_iff"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.energySign_momentumLine_length where
  derives @ "claim:the-momentum-line-has-total-information-length-pi-over-two-in-the-energy-sign-metric-for-every-positive-mass-the-mass-sets-the-concentration-scale-never-the-total",
  epistemic_status @ "consistency-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.canonicalHamiltonian_is_restFrame where
  formalizes @ "claim:the-canonical-representation-is-the-quantum-rest-frame-and-the-foldy-wouthuysen-rotation-is-the-quantum-boost-to-rest",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency.boost_to_rest_frame",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian.fw_intertwine"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.restMassSq_onShell where
  derives @ "claim:the-qif-metric-norm-of-on-shell-frame-data-is-the-mass-the-invariant-shared-by-the-lorentzian-norm-the-rest-gap-the-trembling-operator-and-the-momentum-metric-scale",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency.restFrame_qif_consistency",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.zitterVelocity1_oneD"

zil attach Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.euclideanPacket_eq_wick_rotation where
  derives @ "claim:the-evolved-packets-lorentzian-phase-continues-at-imaginary-time-to-the-euclidean-cameron-weight-whose-gravitational-saddle-value-is-the-horizon-entropy",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung.evolvedPacket",
  supported_by @ "lean:Physlib.Relativity.Special.QuantumInertialFrameEuclidean.euclideanCameronWeight",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSCFT.WaldJacobsonMyersLovelockEntropy.lovelockHorizonEntropy_einstein_eq_euclideanSaddleAction",
  caveat @ "claim:one-mode-analytic-continuation-the-full-cameron-weight-functional-and-the-gravitational-saddle-live-in-their-own-modules-and-are-joined-not-rederived"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Dirac.CanonicalRepresentationZitterbewegung

end

end
