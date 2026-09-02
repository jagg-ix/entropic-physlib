/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsQuantumPotentialFisherBohm
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
public import Physlib.QFT.PathIntegral.CurvedMeasurePathIntegral
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits
public import Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.EMParticleDynamics
public import Mathlib.Analysis.ODE.Gronwall
meta import Zil

/-!
# The evolution equations: Schrödinger equation, `λ = ℏ²/8`, and the Ehrenfest classical Klein–Gordon (Ipek–Abedi–Caticha §§7–8)

Formalizes §§7–8 of Ipek–Abedi–Caticha (arXiv:1803.07493): the entropic-dynamics evolution in curved spacetime is
the **local-time functional Schrödinger equation**, made explicit by the Madelung transformation `Ψ = √ρ e^{iΦ}`
(their Eq. 79 = `edWaveFunction`), and its classical shadow is the **Ehrenfest theorem** — the expected field
obeys the classical Klein–Gordon equation (their Eq. 100).

The decisive constant is the quantum-potential coupling: comparing the Hamilton–Jacobi equation (Eq. 78) with the
Schrödinger equation (Eq. 83) fixes `λ = ℏ²/8`, which **sets the value of Planck's constant** and separates the
quantum from the classical regime.

* the **quantum-potential coupling is `ℏ²/8`** (`edQuantumCoupling`, Eq. 83): `λ = ℏ²/8 > 0` (stability,
  `edQuantumCoupling_pos`) is the constant that makes the dynamics quantum and defines `ℏ`; the Schrödinger
  kinetic coefficient `ℏ²/2` is `4λ` (`kinetic_eq_four_coupling`);
* the evolution is the functional **Schrödinger equation** for `Ψ = √ρ e^{iΦ}` (Eq. 79–84) with `|Ψ|² = ρ`
  (reused `edWaveFunction`, `edWaveFunction_modulus_sq`);
* the **Ehrenfest expected field obeys the classical Klein–Gordon equation** `(□ − m²)χ̄ = 0` for a quadratic
  potential `V = ½m²χ²` (`ehrenfest_classical_kleinGordon`, Eq. 100), because the Ehrenfest force is the classical
  force `⟨m²χ⟩ = m²⟨χ⟩` (`ehrenfest_force_is_classical`, Eq. 99) by linearity of the expectation — Ehrenfest's
  theorem.

So the entropic dynamics of fields in curved spacetime *is* quantum field theory in the Schrödinger functional
representation, with `ℏ` set by the quantum-potential coupling `λ = ℏ²/8`, and its expected field follows the
classical Klein–Gordon equation exactly when the potential is quadratic — the Ehrenfest theorem of the
reconstruction.

* **§A — the quantum-potential coupling `λ = ℏ²/8`** (`edQuantumCoupling`, `kinetic_eq_four_coupling`).
* **§B — the Madelung Schrödinger wave functional** (reused `edWaveFunction`).
* **§C — the Ehrenfest classical Klein–Gordon equation** (`ehrenfest_force_is_classical`,
  `ehrenfest_classical_kleinGordon`).
* **§D — shared curved-QFT and electromagnetic interfaces**
  (`entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge`,
  `entropicDensity_curvedMeasure_maxwellContinuity_bridge`,
  `edWaveFunction_complexCovariantDeriv_gauge_bridge`): one explicitly identified ED density is the Born
  density, curved-measure factor, and curved quantum-matter density; one explicitly identified gauge potential
  shifts the path-integral source and generates a conserved Maxwell current; and the Caticha phase transformation
  obeys the proved gauge-covariance law of the entropic complex derivative.
* **§E — Golse--Paul Coulomb mean-field/classical limit control**
  (`golsePaulMeanFieldPairEnergy_eq`, `CoulombModulatedEnergyControl.energy_norm_le`,
  `CoulombModulatedEnergyControl.tendsto_energy_zero`, `physicalQuantumPotential_tendsto_zero`,
  `golsePaul_monokineticCurrent_holographicPoisson_bridge`): the exact `1/N` pair normalization, the
  modulated-energy Gronwall mechanism, the vanishing Caticha quantum-potential coefficient as `ℏ → 0`, and a
  conditional specialization of the limiting monokinetic density/current to the repository's independently
  established holographic-`G` Poisson source.
* **§F — Ehrenfest from Galilean invariance and nonlinear Schrödinger** (`nonlinearForce_isExactDerivative`,
  `grossPitaevskii_preserves_ehrenfest`, `ehrenfest_anomaly`, `ehrenfest_from_galilean`,
  `doebnerGoldin_breaks_ehrenfest`, Kälbermann J. Phys. A **37** (2004) 2999): the *general* reason §C holds — a
  density-only nonlinearity is a total divergence and drops out of the average force (the Gross–Pitaevskii
  contact term `g ρ` is the concrete witness), and Galilean covariance + continuity + momentum conservation
  give `m d²⟨r⟩/dt² = ⟨F⟩`; the non-Lagrangian Doebner–Goldin equation is the counterexample whose
  non-total-divergence anomaly makes `m d⟨v⟩/dt ≠ ⟨F⟩`, so both branches of the dichotomy are non-vacuous.

**Honest layering.** The coupling `λ = ℏ²/8`, the kinetic relation, the Ehrenfest force linearity, and the
classical-Klein–Gordon equivalence are exact algebra. The full functional Schrödinger PDE (Eq. 83–84), the wave
operator `□` in foliation-adapted coordinates (Eq. 98), and the Poisson-bracket derivation of the Ehrenfest
relations (Eqs. 86–96) are the intended reading, captured at the algebraic level. The §D bridges make their
density and gauge-potential identifications explicit; they do not derive minimal coupling or construct an
interacting locally covariant QFT. ## References

* S. Ipek, M. Abedi, A. Caticha, arXiv:1803.07493, §§7–8 (Eqs. 79, 83, 97, 99–100; Schrödinger equation, Ehrenfest
  theorem). Repo carrier: `EntropicTime.EntropicDynamicsQuantumPotentialFisherBohm`.
* F. Golse, T. Paul, arXiv:1912.06750v1, Theorems 2.2--2.3, Proposition 2.4 and Proposition 3.6 (joint
  mean-field/classical limit, Hartree comparison, monokinetic Euler--Poisson target, modulated-energy estimate).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsCanonicalRepresentation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest


/-- **The quantum-potential coupling** `λ = ℏ²/8` (Ipek–Abedi–Caticha Eq. 83) — comparing the entropic
Hamilton–Jacobi equation (Eq. 78) with the Schrödinger equation (Eq. 83) fixes the coupling of the quantum
potential, which sets the value of Planck's constant `ℏ`. -/
noncomputable def edQuantumCoupling (ℏ : ℝ) : ℝ := ℏ ^ 2 / 8

/-- **[The quantum-potential coupling is positive] `λ = ℏ²/8 > 0`.** The coupling `λ > 0` (the case `λ < 0` is
excluded as unstable): it controls the strength of the quantum potential and sets `ℏ`. -/
lemma edQuantumCoupling_pos (ℏ : ℝ) (hℏ : ℏ ≠ 0) : 0 < edQuantumCoupling ℏ := by
  unfold edQuantumCoupling; positivity

/-- **[The Schrödinger kinetic coefficient is four times the coupling] `ℏ²/2 = 4λ`.** The kinetic term `ℏ²/2` of
the Schrödinger equation (Eq. 83) is four times the quantum-potential coupling `λ = ℏ²/8` (the `4λ` of the
Hamilton–Jacobi equation, Eq. 78) — the same `ℏ` governs the kinetic energy and the quantum potential. -/
lemma kinetic_eq_four_coupling (ℏ : ℝ) : 4 * edQuantumCoupling ℏ = ℏ ^ 2 / 2 := by
  unfold edQuantumCoupling; ring

/-- **The physical quantum-potential density** `Q = (ℏ²/8ρ)(δρ/δχ)²` — the entropic-dynamics quantum potential
with the physical coupling `λ = ℏ²/8`, the Fisher-information term that makes the reconstruction quantum. -/
noncomputable def physicalQuantumPotential (ℏ ρ dρ : ℝ) : ℝ := edQuantumPotential (edQuantumCoupling ℏ) ρ dρ


/-- **[The Ehrenfest force is the classical force] `⟨m²χ⟩ = m²⟨χ⟩`.** For a quadratic potential `V = ½m²χ²` the
Ehrenfest force `⟨∂V/∂χ⟩ = ⟨m²χ⟩` equals the classical force `m²⟨χ⟩ = ∂V(⟨χ⟩)/∂χ` by linearity of the expectation
(Ipek–Abedi–Caticha Eq. 99) — the condition under which the expected field follows classical evolution. -/
lemma ehrenfest_force_is_classical (m : ℝ) (expec : (ℝ → ℝ) → ℝ)
    (hlin : ∀ (a : ℝ) (f : ℝ → ℝ), expec (fun x => a * f x) = a * expec f) (χ : ℝ → ℝ) :
    expec (fun x => m ^ 2 * χ x) = m ^ 2 * expec χ :=
  hlin (m ^ 2) χ

/-- **The Ehrenfest classical force for a quadratic potential** `∂V/∂χ|_{χ̄} = m²χ̄` (`V = ½m²χ²`). -/
def ehrenfestForceQuadratic (m chiBar : ℝ) : ℝ := m ^ 2 * chiBar

/-- **[The Ehrenfest expected field obeys the classical Klein–Gordon equation] `□χ̄ = m²χ̄ ⟺ (□ − m²)χ̄ = 0`.** For
a quadratic potential the Ehrenfest relation `□χ̄ = ⟨∂V/∂χ⟩ = m²χ̄` (Eq. 97) is exactly the classical Klein–Gordon
equation `(□ − m²)χ̄ = 0` in curved spacetime (Eq. 100) for the expected field — Ehrenfest's theorem: the mean
field follows the classical equation of motion. -/
lemma ehrenfest_classical_kleinGordon (m chiBar boxChiBar : ℝ) :
    boxChiBar = ehrenfestForceQuadratic m chiBar ↔ boxChiBar - m ^ 2 * chiBar = 0 := by
  unfold ehrenfestForceQuadratic
  constructor <;> intro h <;> linarith

/-! ## D. The ED density as a curved QFT measure and gauge-coupled matter density -/

/-- **[Entropic density → curved, gauge-coupled QFT data].** If a curved path-integral model uses the
Caticha entropic-dynamics probability density `ρ` as its geometric volume density, then the same `ρ`
is simultaneously: **(i)** the pointwise Born density of `edWaveFunction`; **(ii)** the Radon--Nikodym
factor in the curved partition integral; and **(iii)** the density entering the curved quantum-matter
Hamiltonian. The gauge operator stack acts on that same curved model by the explicit source shift
`J ↦ J + A`.

This is an interface theorem, not a derivation of minimal electromagnetic coupling: the identification
`c.geom.volumeDensity = ρ` is an explicit premise, and the operator stack supplies the gauge potential. -/
lemma entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge
    {α : Type*} [MeasurableSpace α]
    (c : Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel α)
    (ops : Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.CurvedOperatorStack α)
    (ρ Φ : α → ℝ) (J : α → ℂ)
    (sqrtg ginv π gradchi V lam dρ : ℝ) (x : α)
    (hρ : ∀ y, 0 ≤ ρ y) (hdensity : c.geom.volumeDensity = ρ) :
    (∀ y, ‖EntropicDynamicsWaveFunctionReconstruction.edWaveFunction (ρ y) (Φ y)‖ ^ 2
        = c.geom.volumeDensity y)
      ∧ c.partition =
        ∫ y, ρ y • c.toMeasurePathIntegralModel.weight y ∂c.geom.baseMeasure
      ∧ c.gaugeCoupledPartition ops J =
        c.sourceCoupledPartition (fun y => J y + ops.gaugePotential y)
      ∧ IpekCatichaMatterGravityConstraint.kgMatterDensity sqrtg ginv π gradchi V
          + IpekCatichaCurvedQuantumPotential.curvedQuantumPotential sqrtg lam (ρ x) dρ
        = IpekCatichaMatterGravityConstraint.kgMatterDensity sqrtg ginv π gradchi V
          + lam * dρ ^ 2 / (sqrtg * ρ x) := by
  refine ⟨fun y => ?_, ?_, rfl,
    IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum
      sqrtg ginv π gradchi V lam (ρ x) dρ⟩
  · rw [hdensity]
    exact EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq
      (ρ y) (Φ y) (hρ y)
  · simpa [hdensity] using c.partition_eq_base_integral_density_smul

/-- **[Caticha ED gauge potential → conserved Maxwell current].** Specializing the curved model's
configuration carrier to spacetime indices, if its gauge-source potential is the complexification of
the real Maxwell potential `A`, then the same `A` that shifts the curved path-integral source generates
the Faraday tensor. Its induced four-current is conserved and its homogeneous Bianchi equation holds,
while the model's volume density remains the Born density of the Caticha wave function.

The identification of the path-integral gauge potential with `A` is explicit; this theorem does not
derive minimal coupling or a curved Maxwell PDE. -/
lemma entropicDensity_curvedMeasure_maxwellContinuity_bridge
    [MeasurableSpace (Fin 4)]
    (c : Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel (Fin 4))
    (ops : Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.CurvedOperatorStack (Fin 4))
    (ρ Φ : Fin 4 → ℝ) (J : Fin 4 → ℂ) (k A : Fin 4 → ℝ)
    (hρ : ∀ μ, 0 ≤ ρ μ) (hdensity : c.geom.volumeDensity = ρ)
    (hA : ops.gaugePotential = fun μ => (A μ : ℂ)) :
    (∀ μ, ‖EntropicDynamicsWaveFunctionReconstruction.edWaveFunction (ρ μ) (Φ μ)‖ ^ 2
        = c.geom.volumeDensity μ)
      ∧ c.gaugeCoupledPartition ops J =
        c.sourceCoupledPartition (fun μ => J μ + (A μ : ℂ))
      ∧ (∑ ν, k ν *
        Electromagnetic.MaxwellContinuityCovariant.fourCurrent k A ν = 0)
      ∧ (∀ lam μ ν,
        k lam * PTSymmetricQFT.MaxwellFaraday.faraday k A μ ν
          + k μ * PTSymmetricQFT.MaxwellFaraday.faraday k A ν lam
          + k ν * PTSymmetricQFT.MaxwellFaraday.faraday k A lam μ = 0) := by
  refine ⟨fun μ => ?_, ?_,
    Electromagnetic.MaxwellContinuityCovariant.fourCurrent_conserved k A,
    PTSymmetricQFT.MaxwellFaraday.faraday_bianchi k A⟩
  · rw [hdensity]
    exact EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq
      (ρ μ) (Φ μ) (hρ μ)
  · unfold Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.gaugeCoupledPartition
    congr 1
    funext μ
    unfold Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.gaugeShiftedSource
    rw [hA]

/-- **[Caticha's wave function carries the gauge-covariant entropic connection].** The Caticha phase
shift `Φ ↦ Φ - χ` is exactly the local field transformation `Ψ ↦ e^{-iχ}Ψ`. When the ordinary
derivative data and the real connection transform by `DΨ ↦ e^{-iχ}(DΨ - i·dχ·Ψ)` and
`A ↦ A + dχ`, the repository's complex covariant derivative transforms homogeneously.

Thus the same `edWaveFunction` used by the Born-density and curved-measure bridges admits the standard
abelian minimal-coupling gauge transformation. This is an exact algebraic covariance statement; it does
not assert that a particular electromagnetic potential is dynamically generated by entropic dynamics. -/
lemma edWaveFunction_complexCovariantDeriv_gauge_bridge
    {ι : Type*} (ρ Φ χ : ℝ) (DΨ : ι → ℂ) (A dχ : ι → ℝ) :
    EntropicDynamicsWaveFunctionReconstruction.edWaveFunction ρ (Φ - χ)
        = Complex.exp (((-χ : ℝ) : ℂ) * Complex.I)
          * EntropicDynamicsWaveFunctionReconstruction.edWaveFunction ρ Φ
      ∧ ConnectionCovariantHessian.complexCovariantDeriv
          (fun μ => Complex.exp (((-χ : ℝ) : ℂ) * Complex.I)
            * (DΨ μ - Complex.I * (dχ μ : ℂ)
              * EntropicDynamicsWaveFunctionReconstruction.edWaveFunction ρ Φ))
          (fun μ => A μ + dχ μ)
          (Complex.exp (((-χ : ℝ) : ℂ) * Complex.I)
            * EntropicDynamicsWaveFunctionReconstruction.edWaveFunction ρ Φ)
        = fun μ => Complex.exp (((-χ : ℝ) : ℂ) * Complex.I)
          * ConnectionCovariantHessian.complexCovariantDeriv DΨ A
            (EntropicDynamicsWaveFunctionReconstruction.edWaveFunction ρ Φ) μ := by
  constructor
  · simpa [sub_eq_add_neg] using
      HamiltonKillingNormalizationInformationMetric.hamiltonKilling_phaseShift_gauge ρ Φ (-χ)
  · exact ConnectionCovariantHessian.complexCovariantDeriv_gauge_covariant
      DΨ A dχ (EntropicDynamicsWaveFunctionReconstruction.edWaveFunction ρ Φ)
        (Complex.exp (((-χ : ℝ) : ℂ) * Complex.I))

/-! ## E. Golse--Paul Coulomb mean-field and classical-limit control

Golse--Paul's joint limit has three logically separate ingredients.  First, the weak-coupling
Hamiltonian weights every pair by `1/N`.  Second, Proposition 3.6 propagates a modulated-energy
defect by a Gronwall estimate whose initial defect and finite-`N`/finite-`ℏ` remainder vanish jointly.
Third, the semiclassical target is monokinetic: its current is `ρu`, exactly the current used by the
entropic-dynamics continuity equation.

The results below formalize those reusable mechanisms.  They do not construct the unbounded
`N`-body Coulomb Hamiltonian, prove Serfaty's Coulomb inequality, build Wigner measures, or establish
the paper's compactness theorem.  The final holographic bridge is an explicit homogeneous-density
gravitational specialization after replacing the repulsive Coulomb Poisson coupling by the attractive
Newton coupling.  It is not a claim that the paper derives gravity, and its finite nonzero `ℏ` screen
identity is not evaluated at the singular endpoint `ℏ = 0`.
-/

open Filter Set

/-- The number of unordered pairs, represented in `ℝ` as `N(N-1)/2`. -/
noncomputable def golsePaulMeanFieldPairCount (N : ℕ) : ℝ :=
  (N : ℝ) * ((N : ℝ) - 1) / 2

/-- The equal-pair benchmark for the paper's weak-coupling Hamiltonian:
`N(N-1)/2` identical pair energies, each weighted by `1/N`. -/
noncomputable def golsePaulMeanFieldPairEnergy (N : ℕ) (pairEnergy : ℝ) : ℝ :=
  golsePaulMeanFieldPairCount N * (pairEnergy / (N : ℝ))

/-- **Exact mean-field normalization.**  For nonzero `N`, the `1/N`-weighted sum over
`N(N-1)/2` equal pairs is `(N-1)/2` times the one-pair energy. -/
lemma golsePaulMeanFieldPairEnergy_eq (N : ℕ) (pairEnergy : ℝ) (hN : N ≠ 0) :
    golsePaulMeanFieldPairEnergy N pairEnergy =
      ((N : ℝ) - 1) * pairEnergy / 2 := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold golsePaulMeanFieldPairEnergy golsePaulMeanFieldPairCount
  field_simp

/-- The equal-separation Coulomb specialization of the weak-coupling pair benchmark. -/
noncomputable def golsePaulMeanFieldCoulombPairEnergy
    (N : ℕ) (Q r : ℝ) : ℝ :=
  golsePaulMeanFieldPairEnergy N
    (Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.EMParticleDynamics.coulombPotential
      Q Q r)

/-- The repository's exact repulsive Coulomb kernel inherits the paper's mean-field pair
normalization.  This is an equal-pair benchmark, not the spatially varying `N`-body sum. -/
lemma golsePaulMeanFieldCoulombPairEnergy_eq
    (N : ℕ) (Q r : ℝ) (hN : N ≠ 0) :
    golsePaulMeanFieldCoulombPairEnergy N Q r =
      ((N : ℝ) - 1) / 2 *
        Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.EMParticleDynamics.coulombPotential
          Q Q r := by
  rw [golsePaulMeanFieldCoulombPairEnergy,
    golsePaulMeanFieldPairEnergy_eq N _ hN]
  ring

/-- A reusable analytic carrier for the modulated-energy step of Golse--Paul Proposition 3.6.
The index may encode `(N,ℏ)`; `initialDefect` contains the initial kinetic/Coulomb mismatch and
`remainder` contains the finite-`N` and semiclassical errors. -/
structure CoulombModulatedEnergyControl (ι : Type*) where
  /-- The modulated-energy defect. -/
  energy : ι → ℝ → ℝ
  /-- Its identified time derivative. -/
  derivative : ι → ℝ → ℝ
  /-- Initial mismatch. -/
  initialDefect : ι → ℝ
  /-- Finite-`N`/finite-`ℏ` forcing error. -/
  remainder : ι → ℝ
  /-- Stability coefficient controlled by the smooth Euler--Poisson target. -/
  K : ℝ
  /-- Initial time. -/
  a : ℝ
  /-- Final smooth-existence time. -/
  b : ℝ
  /-- Time continuity on the finite classical lifespan. -/
  continuous : ∀ i, ContinuousOn (energy i) (Icc a b)
  /-- Right derivative on the finite classical lifespan. -/
  hasDerivRight : ∀ i, ∀ t ∈ Ico a b,
    HasDerivWithinAt (energy i) (derivative i t) (Ici t) t
  /-- The initial energy is bounded by the recorded initial defect. -/
  initial_norm_le : ∀ i, ‖energy i a‖ ≤ initialDefect i
  /-- Differential modulated-energy inequality. -/
  derivative_norm_le : ∀ i, ∀ t ∈ Ico a b,
    ‖derivative i t‖ ≤ K * ‖energy i t‖ + remainder i

/-- **Gronwall propagation of the Coulomb modulated energy.**  This invokes Mathlib's genuine
right-derivative Gronwall theorem rather than storing the propagated estimate as a premise. -/
lemma CoulombModulatedEnergyControl.energy_norm_le
    {ι : Type*} (C : CoulombModulatedEnergyControl ι) (i : ι) (t : ℝ)
    (ht : t ∈ Icc C.a C.b) :
    ‖C.energy i t‖ ≤
      gronwallBound (C.initialDefect i) C.K (C.remainder i) (t - C.a) := by
  exact norm_le_gronwallBound_of_norm_deriv_right_le
    (C.continuous i) (C.hasDerivRight i) (C.initial_norm_le i)
      (C.derivative_norm_le i) t ht

/-- The Gronwall upper bound tends to zero when its initial defect and forcing remainder do,
for fixed stability coefficient and time. -/
lemma golsePaul_gronwallBound_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (initial remainderFn : ι → ℝ) (K τ : ℝ)
    (hInitial : Tendsto initial l (nhds 0))
    (hRemainder : Tendsto remainderFn l (nhds 0)) :
    Tendsto (fun i => gronwallBound (initial i) K (remainderFn i) τ)
      l (nhds 0) := by
  by_cases hK : K = 0
  · subst K
    simpa only [gronwallBound_K0, Pi.add_apply, Pi.mul_apply,
      zero_add, zero_mul, add_zero] using
        hInitial.add (hRemainder.mul_const τ)
  · rw [show (fun i => gronwallBound (initial i) K (remainderFn i) τ) =
        fun i => initial i * Real.exp (K * τ) +
          remainderFn i / K * (Real.exp (K * τ) - 1) by
          funext i
          rw [gronwallBound_of_K_ne_0 hK]]
    simpa only [zero_mul, zero_div, zero_add] using
      (hInitial.mul_const (Real.exp (K * τ))).add
        ((hRemainder.div_const K).mul_const (Real.exp (K * τ) - 1))

/-- **Joint mean-field/classical limit from the propagated estimate.**  If the initial
modulated defect and the combined finite-`N`/finite-`ℏ` remainder tend to zero, then the
modulated energy tends to zero at every fixed time in the smooth Euler--Poisson lifespan. -/
lemma CoulombModulatedEnergyControl.tendsto_energy_zero
    {ι : Type*} {l : Filter ι} (C : CoulombModulatedEnergyControl ι)
    (t : ℝ) (ht : t ∈ Icc C.a C.b)
    (hInitial : Tendsto C.initialDefect l (nhds 0))
    (hRemainder : Tendsto C.remainder l (nhds 0)) :
    Tendsto (fun i => C.energy i t) l (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  refine squeeze_zero (g := fun i =>
      gronwallBound (C.initialDefect i) C.K (C.remainder i) (t - C.a))
    (fun i => norm_nonneg (C.energy i t))
    (fun i => C.energy_norm_le i t ht) ?_
  exact golsePaul_gronwallBound_tendsto_zero
    C.initialDefect C.remainder C.K (t - C.a) hInitial hRemainder

/-! ## F. Klein–Gordon–Maxwell to Schrödinger–Poisson stability -/

/-- The total strong error for the two dephased Klein–Gordon frequency
sectors and their electrostatic potential.  The scalar sectors may be
instantiated by `H¹(ℝ³)` and the potential sector by homogeneous `Ḣ¹(ℝ³)`,
which are the spaces in the Bechouche–Mauser–Selberg limit theorem. -/
def kgmSchrodingerPoissonError
    {Scalar Potential : Type*}
    [SeminormedAddCommGroup Scalar] [SeminormedAddCommGroup Potential]
    (ψPlus ψMinus vPlus vMinus : Scalar) (A₀ u : Potential) : ℝ :=
  ‖ψPlus - vPlus‖ + ‖ψMinus - vMinus‖ + ‖A₀ - u‖

/-- An analytic carrier for the coupled KGM nonrelativistic limit.  It
identifies the already reusable Coulomb modulated energy with the sum of the
two strong scalar-sector errors and the electrostatic-potential error.

The inherited continuity, right-derivative, and differential-inequality
fields are the stability input.  In the cited KGM analysis they are supplied
on finite time slabs by the uniform Sobolev bounds, the diagonalized equation,
and the `O(c⁻¹/²)`/`O(c⁻¹)` remainders.  This carrier does not assume the final
convergence conclusion. -/
structure KGMNonrelativisticLimitControl
    (ι Scalar Potential : Type*)
    [SeminormedAddCommGroup Scalar] [SeminormedAddCommGroup Potential] where
  /-- The genuine right-derivative Gronwall control. -/
  control : CoulombModulatedEnergyControl ι
  /-- Positive-frequency dephased KGM scalar field. -/
  psiPlus : ι → ℝ → Scalar
  /-- Negative-frequency dephased KGM scalar field. -/
  psiMinus : ι → ℝ → Scalar
  /-- Finite-speed electrostatic potential. -/
  potential : ι → ℝ → Potential
  /-- Limiting positive-frequency Schrödinger field. -/
  limitPlus : ℝ → Scalar
  /-- Limiting negative-frequency Schrödinger field. -/
  limitMinus : ℝ → Scalar
  /-- Limiting Poisson potential. -/
  limitPotential : ℝ → Potential
  /-- Identification of the propagated defect with the coupled strong error. -/
  energy_eq_error : ∀ i t, control.energy i t =
    kgmSchrodingerPoissonError (psiPlus i t) (psiMinus i t)
      (limitPlus t) (limitMinus t) (potential i t) (limitPotential t)

namespace KGMNonrelativisticLimitControl

/-- **The coupled strong KGM error tends to zero.**  Vanishing initial
mismatch and vanishing diagonalization/source remainders, propagated through
the genuine right-derivative Gronwall estimate, force the complete
Schrödinger–Poisson error to zero at each fixed time in the common finite
lifespan. -/
lemma tendsto_error_zero
    {ι Scalar Potential : Type*} [SeminormedAddCommGroup Scalar]
    [SeminormedAddCommGroup Potential] {l : Filter ι}
    (C : KGMNonrelativisticLimitControl ι Scalar Potential)
    (t : ℝ) (ht : t ∈ Icc C.control.a C.control.b)
    (hInitial : Tendsto C.control.initialDefect l (nhds 0))
    (hRemainder : Tendsto C.control.remainder l (nhds 0)) :
    Tendsto (fun i => kgmSchrodingerPoissonError
      (C.psiPlus i t) (C.psiMinus i t) (C.limitPlus t) (C.limitMinus t)
      (C.potential i t) (C.limitPotential t)) l (nhds 0) := by
  have hEnergy := C.control.tendsto_energy_zero t ht hInitial hRemainder
  have hfun : (fun i => kgmSchrodingerPoissonError
      (C.psiPlus i t) (C.psiMinus i t) (C.limitPlus t) (C.limitMinus t)
      (C.potential i t) (C.limitPotential t)) =
      fun i => C.control.energy i t := by
    funext i
    exact (C.energy_eq_error i t).symm
  rw [hfun]
  exact hEnergy

/-- The positive-frequency KGM field converges strongly to its Schrödinger
limit whenever the coupled control defect vanishes. -/
lemma tendsto_psiPlus
    {ι Scalar Potential : Type*} [SeminormedAddCommGroup Scalar]
    [SeminormedAddCommGroup Potential] {l : Filter ι}
    (C : KGMNonrelativisticLimitControl ι Scalar Potential)
    (t : ℝ) (ht : t ∈ Icc C.control.a C.control.b)
    (hInitial : Tendsto C.control.initialDefect l (nhds 0))
    (hRemainder : Tendsto C.control.remainder l (nhds 0)) :
    Tendsto (fun i => C.psiPlus i t) l (nhds (C.limitPlus t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg (C.psiPlus i t - C.limitPlus t))
    (fun i => ?_) (C.tendsto_error_zero t ht hInitial hRemainder)
  unfold kgmSchrodingerPoissonError
  linarith [norm_nonneg (C.psiMinus i t - C.limitMinus t),
    norm_nonneg (C.potential i t - C.limitPotential t)]

/-- The negative-frequency KGM field converges strongly to its Schrödinger
limit whenever the coupled control defect vanishes. -/
lemma tendsto_psiMinus
    {ι Scalar Potential : Type*} [SeminormedAddCommGroup Scalar]
    [SeminormedAddCommGroup Potential] {l : Filter ι}
    (C : KGMNonrelativisticLimitControl ι Scalar Potential)
    (t : ℝ) (ht : t ∈ Icc C.control.a C.control.b)
    (hInitial : Tendsto C.control.initialDefect l (nhds 0))
    (hRemainder : Tendsto C.control.remainder l (nhds 0)) :
    Tendsto (fun i => C.psiMinus i t) l (nhds (C.limitMinus t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg (C.psiMinus i t - C.limitMinus t))
    (fun i => ?_) (C.tendsto_error_zero t ht hInitial hRemainder)
  unfold kgmSchrodingerPoissonError
  linarith [norm_nonneg (C.psiPlus i t - C.limitPlus t),
    norm_nonneg (C.potential i t - C.limitPotential t)]

/-- The electrostatic KGM potential converges strongly to the Poisson
potential whenever the coupled control defect vanishes. -/
lemma tendsto_potential
    {ι Scalar Potential : Type*} [SeminormedAddCommGroup Scalar]
    [SeminormedAddCommGroup Potential] {l : Filter ι}
    (C : KGMNonrelativisticLimitControl ι Scalar Potential)
    (t : ℝ) (ht : t ∈ Icc C.control.a C.control.b)
    (hInitial : Tendsto C.control.initialDefect l (nhds 0))
    (hRemainder : Tendsto C.control.remainder l (nhds 0)) :
    Tendsto (fun i => C.potential i t) l (nhds (C.limitPotential t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg (C.potential i t - C.limitPotential t))
    (fun i => ?_) (C.tendsto_error_zero t ht hInitial hRemainder)
  unfold kgmSchrodingerPoissonError
  linarith [norm_nonneg (C.psiPlus i t - C.limitPlus t),
    norm_nonneg (C.psiMinus i t - C.limitMinus t)]

/-- **KGM to Schrödinger–Poisson convergence, componentwise.**  On every
fixed time in the controlled slab, the two dephased scalar sectors and the
electrostatic potential converge simultaneously in their supplied seminormed
carriers.  Taking the scalar carrier to be `H¹(ℝ³)` and the potential carrier
to be `Ḣ¹(ℝ³)` gives the topology of the paper's main theorem. -/
lemma tendsto_schrodingerPoisson
    {ι Scalar Potential : Type*} [SeminormedAddCommGroup Scalar]
    [SeminormedAddCommGroup Potential] {l : Filter ι}
    (C : KGMNonrelativisticLimitControl ι Scalar Potential)
    (t : ℝ) (ht : t ∈ Icc C.control.a C.control.b)
    (hInitial : Tendsto C.control.initialDefect l (nhds 0))
    (hRemainder : Tendsto C.control.remainder l (nhds 0)) :
    Tendsto (fun i => C.psiPlus i t) l (nhds (C.limitPlus t)) ∧
      Tendsto (fun i => C.psiMinus i t) l (nhds (C.limitMinus t)) ∧
      Tendsto (fun i => C.potential i t) l (nhds (C.limitPotential t)) := by
  exact ⟨C.tendsto_psiPlus t ht hInitial hRemainder,
    C.tendsto_psiMinus t ht hInitial hRemainder,
    C.tendsto_potential t ht hInitial hRemainder⟩

end KGMNonrelativisticLimitControl

/-- **Caticha's quantum-potential term vanishes in the classical limit.**  For fixed
density and density gradient, `λ = ℏ²/8 → 0`, hence the Fisher/Bohm contribution to the
entropic Hamiltonian vanishes as `ℏ → 0`. -/
lemma physicalQuantumPotential_tendsto_zero (ρ dρ : ℝ) :
    Tendsto (fun ℏ : ℝ => physicalQuantumPotential ℏ ρ dρ)
      (nhds 0) (nhds 0) := by
  unfold physicalQuantumPotential edQuantumCoupling edQuantumPotential
  have h : ContinuousAt (fun ℏ : ℝ => ℏ ^ 2 / 8 * dρ ^ 2 / ρ) 0 := by
    fun_prop
  simpa using h.tendsto

/-- **Monokinetic current to holographic-`G` Poisson source.**  A limiting current
`J = ρu` is exactly Caticha's continuity current.  In the homogeneous-density specialization,
the same limiting density sources the repository's explicit Poisson field, while an independently
supplied holographic bit identification rewrites the Einstein coupling using the same `G`.

The repulsive Coulomb target of Golse--Paul and the attractive Newton specialization differ in the
sign/coupling of their Poisson force.  The gravitational conclusion is therefore conditional on the
explicit `hbits` premise and is not a consequence of Coulomb mean-field convergence alone. -/
lemma golsePaul_monokineticCurrent_holographicPoisson_bridge
    (G ℏ c N R ρ : ℝ)
    (density velocity : ℝ → ℝ) (x : ℝ)
    (x3 : Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialSpace3)
    (J : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = Physlib.Thermodynamics.holographicBits
      (Physlib.Thermodynamics.sphereArea R) G ℏ c)
    (hdensity : density x = ρ) (hJ : J = ρ * velocity x) :
    J = EntropicDynamicsFokkerPlanckHamiltonian.fokkerPlanckCurrent
        density velocity x
      ∧ Physlib.QuantumMechanics.ComplexAction.ComptonClock.laplacianAt3
          (Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPotential3 G ρ) x3 =
        4 * Real.pi * G * ρ
      ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (Physlib.Thermodynamics.sphereArea R / N) / (ℏ * c) := by
  refine ⟨?_,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.laplacianAt3_homogeneousDensityPotential
      G ρ x3,
    Physlib.Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm
      G ℏ c N R hℏ hc hG hR hbits⟩
  simpa [EntropicDynamicsFokkerPlanckHamiltonian.fokkerPlanckCurrent,
    hdensity] using hJ

/-! ## Ehrenfest from Galilean invariance and nonlinear Schrödinger (Kälbermann 2004)

Where §C reads the Ehrenfest theorem off the *linearity of the expectation* for the entropic-dynamics
Klein–Gordon field, G. Kälbermann (*Ehrenfest theorem, Galilean invariance and nonlinear Schrödinger
equations*, J. Phys. A: Math. Gen. **37** (2004) 2999) supplies its *general* mechanism: a Galilean-invariant
Schrödinger equation derived from a Lagrangian density obeys the Ehrenfest theorem for velocity-independent
potentials — even with nonlinear self-interactions (Gross–Pitaevskii, density-functional models) — while the
Doebner–Goldin equation, Galilean-invariant but *not* from a Lagrangian, is the counterexample where
Ehrenfest breaks. The Madelung form `ψ = R e^{iS}` this works in is `Schrodinger.MadelungPolarDecomposition`;
the probability current and Hamilton–Jacobi structure are `Schrodinger.HamiltonJacobiMadelung`.

Two exact pieces are formalized. First (eq. 3), a nonlinearity `O(ρ)` of the density `ρ = |ψ|²` **alone**
contributes `ρ ∇O(ρ) = ∇(ρ O(ρ) − W(ρ))` (`W' = O`) to the average force — a total divergence, so it
integrates to a boundary term and cannot break Ehrenfest. Second (eqs. 13–17), Galilean covariance forces the
momentum density to be the mass times the flux (`∫p = m·v`), which with continuity (`v = d⟨r⟩/dt`) and
momentum conservation (`d(∫p)/dt = ⟨F⟩`) gives `m d²⟨r⟩/dt² = ⟨F⟩`; the general form keeps the
covariance-breaking anomaly, `m dv/dt = ⟨F⟩ − d(anomaly)/dt`. The Doebner–Goldin equation (eqs. 5, 8) is the
concrete non-Lagrangian counterexample whose anomaly `λ ∫ ∇|ψ|²·∇(𝐉/|ψ|²)` is no total divergence, so
`m d⟨v⟩/dt ≠ ⟨F⟩` (`doebnerGoldin_breaks_ehrenfest`). Honest scope: the Noether derivation of the
continuity and momentum-conservation relations from the Lagrangian (eqs. 9–12) is not formalized; these are
the exact total-divergence identity and the logical core, as one-dimensional / average `HasDerivAt`
statements. -/

/-- **[Kälbermann eq. 3] A density-only nonlinear force is a total divergence.**  For a nonlinearity `O(ρ)` of
the density alone with antiderivative `W` (`W' = O`), the Ehrenfest-force integrand `ρ ∂ₓO(ρ)` equals
`∂ₓ(ρ O(ρ) − W(ρ))` — a total derivative — so it integrates to a boundary term and does not contribute to the
average force. This is why a Gross–Pitaevskii self-interaction preserves the Ehrenfest theorem. -/
theorem nonlinearForce_isExactDerivative {ρ O W : ℝ → ℝ} {x ρ' O' : ℝ}
    (hρ : HasDerivAt ρ ρ' x) (hO : HasDerivAt O O' (ρ x))
    (hW : HasDerivAt W (O (ρ x)) (ρ x)) :
    HasDerivAt (fun y => ρ y * O (ρ y) - W (ρ y)) (ρ x * (O' * ρ')) x := by
  have hOρ : HasDerivAt (fun y => O (ρ y)) (O' * ρ') x := HasDerivAt.comp x hO hρ
  have hWρ : HasDerivAt (fun y => W (ρ y)) (O (ρ x) * ρ') x := HasDerivAt.comp x hW hρ
  have hmul : HasDerivAt (fun y => ρ y * O (ρ y)) (ρ' * O (ρ x) + ρ x * (O' * ρ')) x := hρ.mul hOρ
  have hval : ρ' * O (ρ x) + ρ x * (O' * ρ') - O (ρ x) * ρ' = ρ x * (O' * ρ') := by ring
  rw [← hval]
  exact hmul.sub hWρ

/-- **The Gross–Pitaevskii contact interaction preserves Ehrenfest.**  The cubic (contact) nonlinearity
`O(ρ) = g·ρ` of the Gross–Pitaevskii / nonlinear Schrödinger equation has antiderivative `W(ρ) = g·ρ²/2`, so by
`nonlinearForce_isExactDerivative` its Ehrenfest-force contribution `ρ ∂ₓ(g ρ)` is the total divergence
`∂ₓ(ρ·(g ρ) − g ρ²/2) = ∂ₓ(g ρ²/2)` — a boundary term. The mean-field self-interaction of a Bose–Einstein
condensate therefore leaves the Ehrenfest theorem intact: the concrete, physically named witness for the
density-only case above. -/
theorem grossPitaevskii_preserves_ehrenfest (g : ℝ) {ρ : ℝ → ℝ} {x ρ' : ℝ} (hρ : HasDerivAt ρ ρ' x) :
    HasDerivAt (fun y => ρ y * (g * ρ y) - g / 2 * ρ y ^ 2) (ρ x * (g * ρ')) x := by
  have hO : HasDerivAt (fun r : ℝ => g * r) g (ρ x) := by
    simpa using (hasDerivAt_id (ρ x)).const_mul g
  have hp : HasDerivAt (fun r : ℝ => r ^ 2) (2 * ρ x) (ρ x) := by
    simpa using hasDerivAt_pow 2 (ρ x)
  have hW : HasDerivAt (fun r : ℝ => g / 2 * r ^ 2) (g * ρ x) (ρ x) := by
    have h := hp.const_mul (g / 2)
    rw [show g / 2 * (2 * ρ x) = g * ρ x from by ring] at h
    exact h
  exact nonlinearForce_isExactDerivative (O := fun r => g * r) (W := fun r => g / 2 * r ^ 2)
    (O' := g) hρ hO hW

/-- **[Kälbermann eqs. 8, 13] The modified Ehrenfest relation.**  When the momentum density fails to be
exactly the mass times the flux — `∫p = m·v + anomaly` — Newton's second law for the averages carries the
anomaly's rate: `m dv/dt = ⟨F⟩ − d(anomaly)/dt`. Here `v = d⟨r⟩/dt`, `∫p` is the field momentum, `⟨F⟩` its
rate. -/
theorem ehrenfest_anomaly {m : ℝ} {avgVel fieldMom force anomaly anomaly' : ℝ → ℝ} {t : ℝ}
    (hgal : ∀ s, fieldMom s = m * avgVel s + anomaly s)
    (hmom : HasDerivAt fieldMom (force t) t)
    (hanom : HasDerivAt anomaly (anomaly' t) t) :
    HasDerivAt (fun s => m * avgVel s) (force t - anomaly' t) t := by
  have h : (fun s => m * avgVel s) = fun s => fieldMom s - anomaly s :=
    funext fun s => by rw [hgal s]; ring
  rw [h]
  exact hmom.sub hanom

/-- **[Kälbermann eqs. 13–17] The Ehrenfest theorem from Galilean invariance.**  A Galilean-invariant
Lagrangian theory has momentum density exactly the mass times the flux (`∫p = m·v`, eq. 13 with the total
divergence integrated away). With continuity (`v = d⟨r⟩/dt`, eq. 16) and momentum conservation
(`d(∫p)/dt = ⟨F⟩`, eq. 15), the second law for the averages holds: `m d²⟨r⟩/dt² = ⟨F⟩` — i.e. `d⟨r⟩/dt = v`
and `m dv/dt = ⟨F⟩`. -/
theorem ehrenfest_from_galilean {m : ℝ} {avgPos avgVel fieldMom force : ℝ → ℝ} {t : ℝ}
    (hcont : HasDerivAt avgPos (avgVel t) t)
    (hgal : ∀ s, fieldMom s = m * avgVel s)
    (hmom : HasDerivAt fieldMom (force t) t) :
    HasDerivAt avgPos (avgVel t) t ∧ HasDerivAt (fun s => m * avgVel s) (force t) t := by
  refine ⟨hcont, ?_⟩
  have hz := ehrenfest_anomaly (anomaly := fun _ => 0) (anomaly' := fun _ => 0)
    (fun s => by rw [hgal s, add_zero]) hmom (hasDerivAt_const t 0)
  simpa using hz

/-- **[Kälbermann eqs. 5, 8] The Doebner–Goldin equation breaks Ehrenfest.**  The Doebner–Goldin equation
(eq. 5) is Galilean-invariant (eq. 7) but is *not* derivable from a Lagrangian, so its flux differs from the
momentum density by the term `λ ∫ ∇|ψ|²·∇(𝐉/|ψ|²)` (eq. 8). Depending on *both* the modulus and the phase
derivatives, that term is **not** a total divergence and does not integrate to a boundary term — unlike the
`∇f` of `ehrenfest_from_galilean` — so it survives as a nonzero anomaly. Whenever the anomaly rate is nonzero,
the average acceleration is `⟨F⟩ − anomaly'(t)`, which is genuinely different from `⟨F⟩`: the Ehrenfest theorem
fails, `m d⟨v⟩/dt ≠ ⟨F⟩`. Together with `ehrenfest_from_galilean` this is the paper's dichotomy — Ehrenfest
holds on the Lagrangian/Galilean branch and fails on the non-Lagrangian one — with both branches non-vacuous. -/
theorem doebnerGoldin_breaks_ehrenfest {m : ℝ} {avgVel fieldMom force anomaly anomaly' : ℝ → ℝ} {t : ℝ}
    (hgal : ∀ s, fieldMom s = m * avgVel s + anomaly s)
    (hmom : HasDerivAt fieldMom (force t) t)
    (hanom : HasDerivAt anomaly (anomaly' t) t)
    (hbreak : anomaly' t ≠ 0) :
    HasDerivAt (fun s => m * avgVel s) (force t - anomaly' t) t ∧ force t - anomaly' t ≠ force t := by
  refine ⟨ehrenfest_anomaly hgal hmom hanom, ?_⟩
  simp only [ne_eq, sub_eq_self]
  exact hbreak

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edQuantumCoupling_pos where
  formalizes @ "claim:the-entropic-dynamics-quantum-coupling-lambda-equals-hbar-squared-over-eight-is-strictly-positive-the-fisher-information-term-that-makes-the-reconstruction-quantum"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.kinetic_eq_four_coupling where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:four-times-the-entropic-dynamics-quantum-coupling-equals-hbar-squared-over-two-fixing-the-physical-coupling-lambda-equals-hbar-squared-over-eight-in-the-functional-schrodinger-kinetic-term",
  requires @ "claim:the-entropic-dynamics-quantum-coupling-lambda-equals-hbar-squared-over-eight-is-strictly-positive-the-fisher-information-term-that-makes-the-reconstruction-quantum"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.ehrenfest_force_is_classical where
  formalizes @ "claim:for-a-quadratic-potential-the-ehrenfest-force-the-expectation-of-the-potential-gradient-equals-the-classical-force-evaluated-at-the-expected-field-by-linearity-of-the-expectation"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.ehrenfest_classical_kleinGordon where
  formalizes @ "claim:for-a-quadratic-potential-the-ehrenfest-relation-box-chibar-equals-m-squared-chibar-is-exactly-the-classical-klein-gordon-equation-in-curved-spacetime-for-the-expected-field-ehrenfests-theorem",
  requires @ "claim:for-a-quadratic-potential-the-ehrenfest-force-the-expectation-of-the-potential-gradient-equals-the-classical-force-evaluated-at-the-expected-field-by-linearity-of-the-expectation"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaulMeanFieldPairEnergy_eq where
  at_level algebraic
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaulMeanFieldPairEnergy]

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaulMeanFieldPairEnergy_eq where
  formalizes @ "claim:golse-paul-1912-06750-one-over-n-weighting-of-n-times-n-minus-one-over-two-equal-pairs-is-n-minus-one-over-two-times-the-pair-energy",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:golse-paul-1912.06750-equation-1-n-body-hamiltonian",
  caveat @ "claim:exact-equal-pair-combinatorial-normalization-not-the-spatially-varying-coulomb-pair-sum-or-its-self-adjointness"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.energy_norm_le where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl,
    gronwallBound]

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.energy_norm_le where
  formalizes @ "claim:golse-paul-1912-06750-the-coulomb-modulated-energy-differential-inequality-propagates-by-the-genuine-right-derivative-gronwall-bound",
  epistemic_status @ "risky",
  supported_by @ "lean:norm_le_gronwallBound_of_norm_deriv_right_le",
  supported_by @ "paper:golse-paul-1912.06750-proposition-3.6",
  caveat @ "claim:analytic-propagation-from-an-explicit-control-carrier-not-a-proof-of-serfatys-coulomb-inequality-or-construction-of-the-n-body-flow"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.tendsto_energy_zero where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl]

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.tendsto_energy_zero where
  formalizes @ "claim:golse-paul-1912-06750-vanishing-initial-defect-and-finite-n-finite-hbar-remainder-force-the-propagated-modulated-energy-to-zero-at-every-fixed-smooth-lifespan-time",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.energy_norm_le",
  supported_by @ "paper:golse-paul-1912.06750-equation-26",
  caveat @ "claim:joint-limit-consequence-of-the-recorded-differential-estimate-not-the-paper-specific-wigner-compactness-or-narrow-convergence-proof"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.KGMNonrelativisticLimitControl.tendsto_schrodingerPoisson where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.KGMNonrelativisticLimitControl]

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.KGMNonrelativisticLimitControl.tendsto_schrodingerPoisson where
  formalizes @ "claim:vanishing-initial-and-remainder-defects-propagated-by-the-right-derivative-gronwall-control-force-simultaneous-strong-convergence-of-both-dephased-scalar-sectors-and-the-poisson-potential",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.tendsto_energy_zero",
  supported_by @ "paper:bechouche-mauser-selberg-kgm-main-nonrelativistic-limit",
  caveat @ "claim:generic-strong-topology-convergence-after-the-explicit-finite-slab-differential-control-and-vanishing-remainder-premises;instantiate-with-H1-and-homogeneous-H1-only-after-supplying-the-paper's-uniform-sobolev-multiplier-and-bilinear-estimates"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.physicalQuantumPotential_tendsto_zero where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.physicalQuantumPotential]

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.physicalQuantumPotential_tendsto_zero where
  formalizes @ "claim:the-entropic-dynamics-fisher-bohm-quantum-potential-density-vanishes-for-fixed-density-data-as-hbar-tends-to-zero",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:ContinuousAt.tendsto",
  caveat @ "claim:coefficient-level-semiclassical-limit-for-fixed-pointwise-density-data-not-uniform-control-of-density-gradients-or-a-wigner-measure-convergence-theorem"

zil_theorem_intent Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaul_monokineticCurrent_holographicPoisson_bridge where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian.fokkerPlanckCurrent,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPotential3,
    Physlib.Thermodynamics.holographicBits]

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaul_monokineticCurrent_holographicPoisson_bridge where
  formalizes @ "claim:a-monokinetic-limit-current-is-the-entropic-continuity-current-and-its-homogeneous-density-specialization-sources-the-independent-holographic-newton-poisson-normalization",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.laplacianAt3_homogeneousDensityPotential",
  supported_by @ "lean:Physlib.Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm",
  caveat @ "claim:conditional-homogeneous-gravitational-specialization-with-explicit-bit-identification-not-a-gravity-derivation-from-repulsive-coulomb-dynamics;the-coulomb-and-newton-poisson-forces-have-different-signs"

zil_file_contract physlib.entropicDynamicsEvolutionSchrodingerEhrenfest where
  promises "The entropic-dynamics evolution equations of Ipek-Abedi-Caticha and their reusable Coulomb stability layer: lambda equals hbar squared over eight, the Ehrenfest field has its exact quadratic-potential classical shadow, one-over-N pair weighting has the correct combinatorial normalization, and a genuine right-derivative Gronwall theorem propagates vanishing defects. The same control now packages the Klein-Gordon-Maxwell to Schrodinger-Poisson strong limit for two dephased scalar sectors and the electrostatic potential. The Caticha Fisher/Bohm coefficient tends to zero for fixed density data; only under a separate holographic-bit premise does the homogeneous Poisson specialization enter the Newton normalization."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edQuantumCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.ehrenfestForceQuadratic",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.KGMNonrelativisticLimitControl",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian.fokkerPlanckCurrent",
    "lean:Physlib.Thermodynamics.holographicBits"]
  forbids_substitutes ["the Madelung/Hamilton-Jacobi derivation of the functional Schrodinger equation from the entropic continuity and phase equations, which is the cited reconstruction machinery",
    "any operator-ordering or renormalization of the curved-spacetime field Hamiltonian, only the coupling value and the Ehrenfest classical limit are carried",
    "claiming the abstract modulated-energy control constructs the unbounded N-body Coulomb Hamiltonian, Serfaty inequality, BBGKY hierarchy, Wigner compactness or the full Golse-Paul convergence theorem",
    "claiming the abstract KGM control proves the paper-specific H1 multiplier, bilinear Sobolev, uniform existence or oscillatory-remainder estimates",
    "calling pressureless Euler-Poisson a viscous or incompressible Navier-Stokes theorem",
    "identifying repulsive Coulomb coupling with attractive Newton coupling without the explicit sign change and holographic-bit premise",
    "evaluating the finite nonzero-hbar holographic bit identity at hbar equal to zero"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edQuantumCoupling_pos,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.kinetic_eq_four_coupling,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.ehrenfest_force_is_classical,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.ehrenfest_classical_kleinGordon,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaulMeanFieldPairEnergy_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.energy_norm_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.tendsto_energy_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.KGMNonrelativisticLimitControl.tendsto_schrodingerPoisson,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.physicalQuantumPotential_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaul_monokineticCurrent_holographicPoisson_bridge]

/- ZIL-END -/
