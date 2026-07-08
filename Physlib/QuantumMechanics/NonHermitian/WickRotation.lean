/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.Wick.Consistency
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Non-Hermitian Schrödinger evolution, Wick's theorem, and Wick rotation

This module assembles the **full non-Hermitian Schrödinger bridge** of the
entropic-time framework and connects it, on one side, to Physlib's Wick's-theorem
infrastructure and, on
the other, to Wick rotation (imaginary / Euclidean time). It reuses three
existing layers rather than re-deriving them:

* the **operator-level** Nagao–Nielsen complex Hamiltonian
  `H_C = H_R − i·H_I` and its reduction at `H_I = 0`
  (`QuantumMechanics.FiniteTarget`);
* the **complex action weight** `w = exp(i S_R/ℏ − S_I/ℏ)` and its compatibility
  with Wick contractions (`Physlib.QFT.Wick.Consistency`);
* HepLean's combinatorial `wicks_theorem`.

## The eigen-level Schrödinger solution

On an `H_C`-eigenvector with complex eigenvalue `E_C = E_R − i E_I` the stationary
solution of `iℏ ∂_t ψ = H_C ψ` is the scalar

  `u(t) = exp(−i E_C t/ℏ) = exp(−i E_R t/ℏ) · exp(−E_I t/ℏ)`,

a **unitary phase** times a **real entropic damping**. We prove `u` actually
solves the equation (`nonHermitian_schrodinger_eigen`, a genuine `HasDerivAt`),
that its modulus is the damping `exp(−E_I t/ℏ)` (`norm_evolutionFactor`), and that
`u(t)` *is* the complex action weight `w(−E_R t, E_I t, ℏ)`
(`evolutionFactor_eq_complexActionWeight`) — so the propagator weight is exactly
the scalar that the Wick expansion records.

## Link to Wick's theorem

Because `u(t)` is a `complexActionWeight`, it commutes through `timeOrder` and
distributes over the Wick-contraction sum
(`evolutionFactor_smul_wicks_theorem`): the non-Hermitian propagator weight
factors uniformly across the time-ordered expansion.

## Wick rotation (imaginary time)

Following the two-sector rule, only the **reversible** phase is rotated:
substituting `t = −iτ` sends `exp(−i E_R t/ℏ) ↦ exp(−E_R τ/ℏ)` — a real Euclidean
heat-kernel weight (`reversiblePhase_wickRotation`) — while the **entropy**
damping is transferred unchanged as a real, contractive factor
(`lorentzian_to_euclidean_wickRotation`).

## Reduction to unitary time

At `H_I = 0` (equivalently `E_I = 0`, i.e. `S_I = 0`) the damping is `1`, the
evolution is the pure phase `exp(−i E_R t/ℏ)` of unit modulus, and the operator
generator collapses to the Hermitian `H_R` — standard unitary Schrödinger
dynamics (`reduces_to_unitary_at_H_I_zero`). On the diagonal `ρ = σ` the entropic
proper time vanishes and the same unitary reduction holds
(`entropicEvolutionFactor_self_eq_reversiblePhase`).


## References

- **Sergi & Giaquinta 2016** — *Linear Quantum Entropy and Non-Hermitian Hamiltonians*, Entropy 18(12), 451 (`entropic-physlib-inventory/entropy-v18-i12_20260602.bib`) — direct source for the `H = H_R − i·H_I` convention used here (no factor of 1/2).
- **Nagao & Nielsen 2011** — *Formulation of Complex Action Theory* — related work; uses `E_n − iΓ_n/2` (rescaled by 1/2).
- **Breuer & Petruccione 2002** — *The Theory of Open Quantum Systems (textbook)*
- **Wick 1954** — *Properties of Bethe-Salpeter Wave Functions*
- **Leray 1934** — *Sur le mouvement d'un liquide visqueux emplissant l'espace* (entropic-time/paper/references.bib) — NS Stokes target of Wick-rotated Schrödinger
- **Constantin & Iyer 2008** — *A stochastic Lagrangian representation of the 3D incompressible Navier–Stokes equations* (entropic-time/paper/references.bib)
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.QFT.Wick.Consistency
namespace Physlib.QuantumMechanics.NonHermitian.WickRotation

open QuantumInfo.Finite FieldSpecification QuantumMechanics.FiniteTarget

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §1 — The complex energy and the eigen-evolution factor -/

/-- Complex eigenvalue of the Nagao–Nielsen Hamiltonian `H_C = H_R − i·H_I` on an
eigenvector: `E_C = E_R − i E_I`. -/
def complexEnergy (E_R E_I : ℝ) : ℂ := (E_R : ℂ) - Complex.I * (E_I : ℂ)

/-- At `E_I = 0` the complex energy is the (real) reversible eigenvalue. -/
@[simp] theorem complexEnergy_at_E_I_zero (E_R : ℝ) :
    complexEnergy E_R 0 = (E_R : ℂ) := by
  unfold complexEnergy; simp

/-- **Eigen-level non-Hermitian Schrödinger solution over complex time**
`u(t) = exp(−i E_C t/ℏ)`, the stationary solution of `iℏ ∂_t ψ = H_C ψ` on an
`H_C`-eigenvector with eigenvalue `E_C = E_R − i E_I`. Defined for complex `t` so
that Wick rotation `t ↦ −iτ` is a substitution in the same object. -/
def evolutionFactorC (E_R E_I hbar : ℝ) (t : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (complexEnergy E_R E_I / hbar) * t)

/-- The real-time eigen-evolution factor `u(t) = exp(−i E_C t/ℏ)`. -/
def evolutionFactor (E_R E_I hbar t : ℝ) : ℂ :=
  evolutionFactorC E_R E_I hbar (t : ℂ)

/-- **Reversible (unitary) phase** `exp(−i E_R t/ℏ)`. -/
def reversiblePhase (E_R hbar t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((E_R / hbar : ℝ) : ℂ) * (t : ℂ))

/-! ## §2 — The Schrödinger equation is actually solved -/

/-- The Schrödinger coefficient `−i E_C/ℏ` equals `E_C/(iℏ)`, the right-hand side
of `iℏ ∂_t ψ = H_C ψ` divided through. -/
theorem schrodingerCoeff_eq (E_R E_I hbar : ℝ) :
    -Complex.I * (complexEnergy E_R E_I / hbar)
      = complexEnergy E_R E_I / (Complex.I * hbar) := by
  rw [div_mul_eq_div_div, Complex.div_I]; ring

/-- **The eigen-evolution factor solves the non-Hermitian Schrödinger equation.**
`u'(t) = (E_C/(iℏ)) · u(t)`, i.e. `iℏ ∂_t u = E_C u` — the eigen-form of
`iℏ ∂_t ψ = H_C ψ`. This is a genuine (holomorphic) derivative, not a definitional
restatement. -/
theorem nonHermitian_schrodinger_eigen (E_R E_I hbar : ℝ) (t : ℂ) :
    HasDerivAt (evolutionFactorC E_R E_I hbar)
      (complexEnergy E_R E_I / (Complex.I * hbar) * evolutionFactorC E_R E_I hbar t) t := by
  have h := ((hasDerivAt_id t).const_mul
      (-Complex.I * (complexEnergy E_R E_I / hbar))).cexp
  rw [← schrodingerCoeff_eq, mul_comm]
  simp only [id_eq, mul_one] at h
  exact h

/-! ## §3 — Two-sector decomposition: unitary phase × entropic damping -/

/-- **Phase/damping factorization**: `u(t) = exp(−i E_R t/ℏ) · exp(−E_I t/ℏ)`.
The first factor is the reversible unitary phase; the second is the real entropic
damping with imaginary action `S_I = E_I·t`. -/
theorem evolutionFactor_decomp (E_R E_I hbar t : ℝ) :
    evolutionFactor E_R E_I hbar t
      = reversiblePhase E_R hbar t * ((Real.exp (-(E_I * t / hbar)) : ℝ) : ℂ) := by
  unfold evolutionFactor evolutionFactorC reversiblePhase complexEnergy
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (E_I * t / hbar : ℂ) * Complex.I_mul_I

/-- The reversible phase has **unit modulus** (it is unitary). -/
theorem norm_reversiblePhase (E_R hbar t : ℝ) :
    ‖reversiblePhase E_R hbar t‖ = 1 := by
  unfold reversiblePhase
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- **The modulus of the evolution factor is the entropic damping**:
`‖u(t)‖ = exp(−E_I t/ℏ)`. The imaginary energy `E_I` over time `t` is the entropic
time `S_I/ℏ = E_I t/ℏ`. -/
theorem norm_evolutionFactor (E_R E_I hbar t : ℝ) :
    ‖evolutionFactor E_R E_I hbar t‖ = Real.exp (-(E_I * t / hbar)) := by
  rw [evolutionFactor_decomp, norm_mul, norm_reversiblePhase, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]

/-! ## §4 — Link to the complex action weight and Wick's theorem -/

/-- **The propagator weight is a complex action weight**:
`u(t) = w(−E_R t, E_I t, ℏ)`. This identifies the non-Hermitian Schrödinger
evolution factor with the scalar of `Physlib.QFT.Wick.Consistency`. -/
theorem evolutionFactor_eq_complexActionWeight (E_R E_I hbar t : ℝ) :
    evolutionFactor E_R E_I hbar t = complexActionWeight (-(E_R * t)) (E_I * t) hbar := by
  unfold evolutionFactor evolutionFactorC complexActionWeight complexEnergy
  congr 1
  push_cast
  linear_combination (E_I * t / hbar : ℂ) * Complex.I_mul_I

/-- **The propagator weight commutes through Wick time-ordering** (since
`timeOrder` is `ℂ`-linear): `𝓣(u • A) = u • 𝓣(A)`. -/
theorem timeOrder_evolutionFactor_smul
    {𝓕 : FieldSpecification} (E_R E_I hbar t : ℝ) (A : 𝓕.WickAlgebra) :
    WickAlgebra.timeOrder (evolutionFactor E_R E_I hbar t • A) =
      evolutionFactor E_R E_I hbar t • WickAlgebra.timeOrder A :=
  map_smul WickAlgebra.timeOrder (evolutionFactor E_R E_I hbar t) A

/-- **The propagator weight distributes over the Wick-contraction expansion**:
`u • 𝓣(ofFieldOpList φs) = ∑ φsΛ, u • φsΛ.wickTerm`. The non-Hermitian Schrödinger
weight factors uniformly across every term of the time-ordered Wick expansion
(the contraction enumeration being HepLean's `wicks_theorem`). -/
theorem evolutionFactor_smul_wicks_theorem
    {𝓕 : FieldSpecification} (E_R E_I hbar t : ℝ) (φs : List 𝓕.FieldOp) :
    evolutionFactor E_R E_I hbar t •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length,
        evolutionFactor E_R E_I hbar t • φsΛ.wickTerm := by
  rw [wicks_theorem φs, Finset.smul_sum]

/-! ## §5 — Wick rotation (imaginary / Euclidean time) -/

/-- Complex-time reversible phase, used to perform the Wick rotation `t ↦ −iτ`. -/
def reversiblePhaseC (E_R hbar : ℝ) (t : ℂ) : ℂ :=
  Complex.exp (-Complex.I * ((E_R / hbar : ℝ) : ℂ) * t)

/-- The complex-time phase restricts to the real-time reversible phase. -/
@[simp] theorem reversiblePhaseC_ofReal (E_R hbar t : ℝ) :
    reversiblePhaseC E_R hbar (t : ℂ) = reversiblePhase E_R hbar t := rfl

/-- **Wick rotation of the reversible sector.** Substituting `t = −iτ` turns the
unitary phase `exp(−i E_R t/ℏ)` into the **real Euclidean heat-kernel** weight
`exp(−E_R τ/ℏ)`. -/
theorem reversiblePhase_wickRotation (E_R hbar τ : ℝ) :
    reversiblePhaseC E_R hbar (-Complex.I * (τ : ℂ)) =
      ((Real.exp (-(E_R * τ / hbar)) : ℝ) : ℂ) := by
  unfold reversiblePhaseC
  rw [Complex.ofReal_exp]
  congr 1
  rw [show -Complex.I * ((E_R / hbar : ℝ) : ℂ) * (-Complex.I * (τ : ℂ))
        = (Complex.I * Complex.I) * (((E_R / hbar : ℝ) : ℂ) * (τ : ℂ)) from by ring,
    Complex.I_mul_I]
  push_cast; ring

/-- Entropy damping factor `exp(−S_I/ℏ)`. -/
def entropyDamping (S_I hbar : ℝ) : ℝ := Real.exp (-(S_I / hbar))

/-- Euclidean evolution weight `exp(−S_E/ℏ) · exp(−S_I/ℏ)` — reversible heat
kernel times the preserved entropic damping. -/
def euclideanEvolutionFactor (S_E S_I hbar : ℝ) : ℝ :=
  Real.exp (-(S_E / hbar)) * entropyDamping S_I hbar

/-- **Two-sector Wick rotation.** Rotating only the reversible phase
(`t ↦ −iτ`) while with the entropy damping over unchanged turns the
Lorentzian weight into the Euclidean weight with `S_E = E_R·τ`; the entropic
damping `exp(−S_I/ℏ)` is **preserved** across the rotation. -/
theorem lorentzian_to_euclidean_wickRotation (E_R S_I hbar τ : ℝ) :
    reversiblePhaseC E_R hbar (-Complex.I * (τ : ℂ)) * ((entropyDamping S_I hbar : ℝ) : ℂ)
      = ((euclideanEvolutionFactor (E_R * τ) S_I hbar : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation]
  unfold euclideanEvolutionFactor
  push_cast; ring

/-- The Euclidean damping sector is real and **contractive** (`≤ 1` of the
reversible heat kernel) for non-negative imaginary action — the entropy sector
never amplifies. -/
theorem euclideanEvolutionFactor_le_heatKernel
    (S_E S_I hbar : ℝ) (hS : 0 ≤ S_I) (hh : 0 < hbar) :
    euclideanEvolutionFactor S_E S_I hbar ≤ Real.exp (-(S_E / hbar)) := by
  unfold euclideanEvolutionFactor entropyDamping
  have hle : Real.exp (-(S_I / hbar)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have : 0 ≤ S_I / hbar := div_nonneg hS hh.le; linarith)
  exact mul_le_of_le_one_right (Real.exp_nonneg _) hle

/-! ## §6 — Reduction to unitary time at `H_I = 0` / `S_I = 0` -/

/-- **At `H_I = 0` (`E_I = 0`) the evolution is the pure unitary phase.** -/
theorem evolutionFactor_at_H_I_zero (E_R hbar t : ℝ) :
    evolutionFactor E_R 0 hbar t = reversiblePhase E_R hbar t := by
  rw [evolutionFactor_decomp]; simp

/-- At `H_I = 0` the propagator weight has **unit modulus** — norm-preserving,
unitary evolution. -/
theorem norm_evolutionFactor_at_H_I_zero (E_R hbar t : ℝ) :
    ‖evolutionFactor E_R 0 hbar t‖ = 1 := by
  rw [evolutionFactor_at_H_I_zero, norm_reversiblePhase]

/-- **Full reduction to unitary time at `H_I = 0`.** Combines the eigen-level and
operator-level statements:

* (i) the eigen-evolution factor becomes the pure unitary phase;
* (ii) its modulus is `1` (norm preserved);
* (iii) the operator complex Hamiltonian collapses to the Hermitian `H_R`.

This is the single-equation summary of "entropic time → unitary time at
`S_I = 0`" across both the scalar and operator layers. -/
theorem reduces_to_unitary_at_H_I_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R : H →L[ℂ] H) (E_R hbar t : ℝ) :
    evolutionFactor E_R 0 hbar t = reversiblePhase E_R hbar t
    ∧ ‖evolutionFactor E_R 0 hbar t‖ = 1
    ∧ complexHamiltonian H_R 0 = H_R :=
  ⟨evolutionFactor_at_H_I_zero E_R hbar t,
   norm_evolutionFactor_at_H_I_zero E_R hbar t,
   complexHamiltonian_at_H_I_zero H_R⟩

/-! ## §7 — Entropic proper time as the imaginary-action source -/

/-- **Entropic evolution factor**: the reversible unitary phase damped by the
relative entropy gap, `exp(−D(ρ‖σ))`. Its imaginary action is `S_I = ℏ·D(ρ‖σ)`. -/
def entropicEvolutionFactor (E_R hbar t : ℝ) (ρ σ : MState d) : ℂ :=
  reversiblePhase E_R hbar t *
    ((Real.exp (-(entropicProperTime ρ σ).toReal) : ℝ) : ℂ)

/-- Its modulus is the entropic damping `exp(−D(ρ‖σ))`. -/
theorem norm_entropicEvolutionFactor (E_R hbar t : ℝ) (ρ σ : MState d) :
    ‖entropicEvolutionFactor E_R hbar t ρ σ‖ =
      Real.exp (-(entropicProperTime ρ σ).toReal) := by
  unfold entropicEvolutionFactor
  rw [norm_mul, norm_reversiblePhase, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

/-- **Diagonal reduction**: on `ρ = σ` the entropic proper time vanishes, so the
entropic evolution factor is the pure unitary phase — `S_I = 0` ⇒ unitary time. -/
theorem entropicEvolutionFactor_self_eq_reversiblePhase
    (E_R hbar t : ℝ) (ρ : MState d) :
    entropicEvolutionFactor E_R hbar t ρ ρ = reversiblePhase E_R hbar t := by
  unfold entropicEvolutionFactor
  rw [entropicProperTime_self]; simp

/-- On the diagonal the entropic evolution factor has unit modulus (unitary). -/
theorem norm_entropicEvolutionFactor_self (E_R hbar t : ℝ) (ρ : MState d) :
    ‖entropicEvolutionFactor E_R hbar t ρ ρ‖ = 1 := by
  rw [entropicEvolutionFactor_self_eq_reversiblePhase, norm_reversiblePhase]

/-! ## §7 — Madelung polar decomposition `ψ = R · exp(i S/ℏ)`

The Madelung polar decomposition writes a wave function as `ψ = R · exp(i S/ℏ)`
with non-negative amplitude `R ≥ 0` and real phase `S`.  This connects the
reversible phase `exp(−i E_R t/ℏ)` (the dynamic phase factor `S = −E_R · t`)
to a probability-amplitude reading: `|ψ|² = R²` is the Born density.

In the entropic-time framework, the Madelung amplitude is the **modulus** and
the Madelung phase is the **argument** of the wave function — exactly the
two-sector split between `path_integral_damping` and `reversiblePhase`.  The
Madelung-Nelson **viscosity identification** `ν = ℏ/(2m)` connects this layer
to the NS Stokes diffusion via `Physlib.QFT.PathIntegral.WickClock`.
-/

/-- **Madelung wave function structure** `ψ = R · exp(i S/ℏ)` with non-negative
amplitude, real phase, and positive ℏ.  Phase-1 scalar form (per-mode). -/
structure MadelungWaveFunction where
  /-- Amplitude `R ≥ 0`. -/
  amplitude : ℝ
  /-- Non-negativity of the amplitude. -/
  amp_nonneg : 0 ≤ amplitude
  /-- Phase `S` (the real action in Bohmian / Madelung mechanics). -/
  phase : ℝ
  /-- Reduced Planck constant `ℏ > 0`. -/
  hbar : ℝ
  /-- Strict positivity of `ℏ`. -/
  hbar_pos : 0 < hbar

/-- **Madelung probability density** `ρ_M = R²` (Born rule). -/
noncomputable def madelungDensity (ψ : MadelungWaveFunction) : ℝ :=
  ψ.amplitude ^ 2

/-- The Madelung density is non-negative. -/
theorem madelungDensity_nonneg (ψ : MadelungWaveFunction) :
    0 ≤ madelungDensity ψ := by unfold madelungDensity; positivity

/-- **Born rule**: probability density equals amplitude squared. -/
theorem madelung_born_rule (ψ : MadelungWaveFunction) :
    madelungDensity ψ = ψ.amplitude ^ 2 := rfl

/-- **Madelung phase factor has unit modulus**: `‖exp(i·θ)‖ = 1`. -/
theorem madelung_phase_factor_norm (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- **Wave-function norm = Madelung amplitude.**  The complex wave function
`R · exp(i S/ℏ)` has norm `R`, identifying `‖ψ‖² = R²` as the Born density. -/
theorem madelung_wf_norm (ψ : MadelungWaveFunction) :
    ‖(ψ.amplitude : ℂ) * Complex.exp (Complex.I * (ψ.phase / ψ.hbar))‖ =
      ψ.amplitude := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ψ.amp_nonneg, mul_comm,
    show Complex.I * ((ψ.phase : ℂ) / (ψ.hbar : ℂ)) =
        ((ψ.phase / ψ.hbar : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The Madelung phase factor at `S = −E_R · t` is the reversible phase.**

For a pure energy eigenstate, the Madelung phase is `S(t) = −E_R · t` (Hamilton's
principal function for time-independent energy), and the Madelung phase factor
`exp(i S(t)/ℏ) = exp(−i E_R t/ℏ)` is exactly the `reversiblePhase E_R ℏ t`.
This identifies the Madelung phase-factor sector with the existing
reversible-phase layer. -/
theorem madelung_phase_factor_eq_reversiblePhase (E_R hbar t : ℝ) :
    Complex.exp (((-E_R * t / hbar : ℝ) : ℂ) * Complex.I) =
      reversiblePhase E_R hbar t := by
  unfold reversiblePhase
  congr 1
  push_cast
  ring

/-- **Madelung amplitude structure** as a constant amplitude `R₀ ≥ 0` paired with
a reversible-phase energy eigenstate — the simplest Madelung wave function
(stationary state with constant probability density `R₀²`). -/
def MadelungWaveFunction.ofEnergyEigenstate
    (R₀ : ℝ) (hR : 0 ≤ R₀) (E_R hbar : ℝ) (hℏ : 0 < hbar) (t : ℝ) :
    MadelungWaveFunction where
  amplitude := R₀
  amp_nonneg := hR
  phase := -E_R * t
  hbar := hbar
  hbar_pos := hℏ

/-- The energy-eigenstate Madelung density is the constant `R₀²`. -/
theorem ofEnergyEigenstate_density (R₀ : ℝ) (hR : 0 ≤ R₀) (E_R hbar : ℝ)
    (hℏ : 0 < hbar) (t : ℝ) :
    madelungDensity (MadelungWaveFunction.ofEnergyEigenstate R₀ hR E_R hbar hℏ t)
      = R₀ ^ 2 := rfl

end Physlib.QuantumMechanics.NonHermitian.WickRotation

end
