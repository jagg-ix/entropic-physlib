/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceRealStructure

meta import Zil

/-!
# The spectral asymmetry invariant and the Yang–Mills sector arithmetic

The closing exact content of Aastrup–Grimstrup arXiv:2410.07290 §4 (pages 11–12):
the spectral invariant `Tr_ξ(i∇^A)` of Eq. 8, the `H_YM = H⁺_YM + H⁻_YM` sector
arithmetic, the canonical commutation relations `[Ê_A(m₁), Â(m₂)] = K(m₁,m₂)`, and
the ground-state degeneracy.

## §A — the spectral asymmetry invariant (paper Eq. 8)

`Tr_ξ(i∇^A) = i·Σᵢ Tr(ξᵢ∇^Aξᵢ)` — *"a spectral invariant … related to the
eta-invariant for `∇^A` first introduced by Atiyah, Patodi, and Singer. This
spectral invariant measures the asymmetry of the spectrum of `∇^A`."* On the matrix
carrier (`spectralInvariant ∇ = i·Tr ∇`):

* `spectralInvariant_real` — for a skew-adjoint covariant derivative (`∇ᴴ = −∇`) the
  invariant is **real**: `Tr ∇` is purely imaginary, so `i·Tr ∇ ∈ ℝ` — the invariant
  is an observable, entering the Hamiltonian sectors.
* `spectralInvariant_basis_invariant` — the invariant does not depend on the
  orthonormal basis `{ξᵢ}` used to compute it: conjugation by any unitary preserves
  it (the "invariant" in its name).
* `spectralAsymmetry_vanishes_of_symmetric` — **the invariant measures spectral
  asymmetry**: if the spectrum of `∇` is symmetric — `∇` is conjugate to `−∇` —
  the invariant vanishes.  Contrapositive: a nonzero `spectralInvariant` certifies
  an asymmetric spectrum, the finite-dimensional face of the Atiyah–Patodi–Singer
  `η(∇) = Σ_λ sign λ`.

## §B — the sector arithmetic (paper page 11, the display after Eq. 8)

`(𝒟^U)² = diag(H⁺_YM + Tr_ξ(i∇^A), H⁻_YM − Tr_ξ(i∇^A)) + curvature + Ξ` — the
invariant enters the two dual sectors with **opposite signs** (the `±t` of
`ConfigurationSpaceRealStructure.rotated_sq_sectors`; `t` is the second Chern–Simons
functional derivative whose trace part is Eq. 8 — the paper's §5 emphasizes that
the invariant *"comes from a term that involves two derivations of the Chern–Simons
term"*, the term a Laplace operator would lose).  Exactly:

* `sector_sum` — adding the two rotated blocks, **the cross terms and the spectral
  invariant cancel**: `block₊ + block₋ = (D² + D²) + (s² + s²)` — the paper's
  `H_YM = H⁺_YM + H⁻_YM`, the total Hamiltonian in `E² + B²` form with the `±2EB`
  transport and the `±η` asymmetry dropping out of the sum.
* `sector_difference` — subtracting them isolates the odd content: the transport
  cross term and twice the (curvature + spectral-invariant) term — what
  distinguishes the self-dual from the anti-self-dual sector.

## §C — the canonical commutation relations (paper page 12)

With the field operators `Ê_A(m) = Σᵢ ξᵢ(m)Êᵢ` and `Â(m) = Σᵢ xᵢξᵢ(m)`:
`smeared_CCR_kernel` — from the mode-level CCR `[pᵢ, xⱼ] = δᵢⱼ`, the smeared
commutator is `[Ê(f), Â(g)] = (Σᵢ fᵢgᵢ)·1` — the paper's
`[Ê_A(m₁), Â(m₂)] = K(m₁,m₂)`, the canonical commutation relations of an `SU(2)`
quantum gauge theory with the **same nonlocal kernel** `K(m₁,m₂) = Σᵢξᵢ(m₁)ξᵢ(m₂)`
as the fermionic CAR (`ConfigurationSpaceDiracFluctuation.smearedField_CAR_kernel`)
— bosons and fermions quantized against one kernel, the unification the framework
is built for.

## §D — the ground state is (infinitely) degenerate (paper page 12)

`groundState_degenerate` — for trivial geometry the Dirac operator acts only on the
`(η⁺, η⁻)` factor, so if `D±η± = 0` then `Ψ' = (η⁺, η⁻) ⊗ Ψ_CAR` is annihilated for
*every* Fock element `Ψ_CAR`: the kernel contains a full Fock factor — *"the ground
state will be infinitely degenerate."*

## Honest scope

Finite matrix/ring carriers: the APS `η`-function regularization (`Σ sign λ·|λ|^{−s}`
and its analytic continuation), the local limit `K → δ`, the `4k²` normalizations
and the identification of `t`'s trace part with Eq. 8 inside the operator algebra
are recorded; the sector arithmetic works on the abstract rotated blocks of
`ConfigurationSpaceRealStructure`.

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2410.07290 §4 (Eq. 8, pages 11–12), §5;
  M. F. Atiyah, V. K. Patodi, I. M. Singer, Math. Proc. Camb. Philos. Soc. **77**
  (1975) 43; **78** (1975) 405; **79** (1976) 71.
* Carriers: `ConfigurationSpaceRealStructure` (`rotated_sq_sectors`),
  `ConfigurationSpaceDiracFluctuation` (`smearedField_CAR_kernel` — the shared
  kernel), `ConfigurationSpaceDiracOperator` (trace identities).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry

/-! ## §A — the spectral asymmetry invariant -/

variable {n : ℕ}

/-- **The spectral invariant of paper Eq. 8**: `Tr_ξ(i∇) = i·Σᵢ⟨ξᵢ, ∇ξᵢ⟩ = i·Tr ∇`
— the trace of the covariant derivative against an orthonormal basis, times `i`. -/
def spectralInvariant (Dv : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Complex.I * Dv.trace

/-- **The invariant is real for a skew-adjoint covariant derivative**: `∇ᴴ = −∇`
forces `Tr ∇` purely imaginary, so `i·Tr ∇` is real — the spectral invariant is an
observable entering the Hamiltonian sectors. -/
theorem spectralInvariant_real {Dv : Matrix (Fin n) (Fin n) ℂ}
    (h : Dv.conjTranspose = -Dv) : (spectralInvariant Dv).im = 0 := by
  have htr : star Dv.trace = -Dv.trace := by
    rw [← Matrix.trace_conjTranspose, h, Matrix.trace_neg]
  have hre : Dv.trace.re = 0 := by
    have hreEq := congrArg Complex.re htr
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hreEq
    linarith
  simp [spectralInvariant, Complex.mul_im, hre]

/-- **The invariant is basis-independent**: conjugating `∇` by any unitary (a change
of the orthonormal family `{ξᵢ}`) preserves it — the "invariant" of its name. -/
theorem spectralInvariant_basis_invariant (Dv U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) :
    spectralInvariant (U.conjTranspose * Dv * U) = spectralInvariant Dv := by
  unfold spectralInvariant
  rw [Matrix.trace_mul_cycle, mul_eq_one_comm.mp hU, one_mul]

/-- **The invariant measures spectral asymmetry** (the Atiyah–Patodi–Singer face):
if the spectrum of `∇` is symmetric — `∇` conjugate to `−∇` — the invariant
vanishes.  Contrapositive: a nonzero `spectralInvariant` certifies an asymmetric
spectrum of the covariant derivative. -/
theorem spectralAsymmetry_vanishes_of_symmetric {Dv G G' : Matrix (Fin n) (Fin n) ℂ}
    (hG : G' * G = 1) (hconj : G * Dv * G' = -Dv) :
    spectralInvariant Dv = 0 := by
  have htr : Dv.trace = -Dv.trace := by
    calc Dv.trace = (G * Dv * G').trace := by
          rw [Matrix.trace_mul_cycle, hG, one_mul]
      _ = (-Dv).trace := by rw [hconj]
      _ = -Dv.trace := Matrix.trace_neg Dv
  have hzero : Dv.trace = 0 := by
    have h2 : Dv.trace + Dv.trace = 0 := by
      nth_rewrite 1 [htr]
      exact neg_add_cancel _
    have h3 : (2 : ℂ) * Dv.trace = 0 := by rw [two_mul]; exact h2
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rw [spectralInvariant, hzero, mul_zero]

/-- **Dirac's dead-wood model carries zero spectral asymmetry**: the antisymmetric
mode-mixing matrix of `ConfigurationSpaceDiracFluctuation.seaMode` has vanishing
`spectralInvariant` — its spectrum is `±`-symmetric (the `±i`-pairs of `a² = −1`),
which is exactly why the bare vacuum `|S⟩` and the filled-sea vacuum `|Y⟩` sit on
equal algebraic footing: neither half of the spectrum is preferred, and the choice
between them is the choice Dirac's dead-wood argument turns on. -/
theorem deadwood_spectralInvariant_zero {n : ℕ} (a : Fin n → Fin n → ℝ)
    (hanti : ∀ r s, a r s = -(a s r)) :
    spectralInvariant (Matrix.of fun i j => ((a i j : ℝ) : ℂ)) = 0 := by
  unfold spectralInvariant
  have htr : (Matrix.of fun i j => ((a i j : ℝ) : ℂ)).trace = 0 := by
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h : a i i = 0 := by
      have := hanti i i
      linarith
    simp [Matrix.diag_apply, h]
  rw [htr, mul_zero]

/-! ## §B — the sector arithmetic -/

/-- **The total Yang–Mills Hamiltonian: the cross terms and the spectral invariant
cancel in the sum of the sectors** (paper: `H_YM = H⁺_YM + H⁻_YM`): adding the two
rotated blocks of `rotated_sq_sectors`, the `±2sD` transport and the `±t`
(curvature + spectral invariant) drop out, leaving the `E² + B²` form. -/
theorem sector_sum {R : Type*} [Ring R] (d s t : R) :
    (d * d - (s * d + s * d) - t + s * s) + (d * d + (s * d + s * d) + t + s * s)
      = (d * d + d * d) + (s * s + s * s) := by
  abel

/-- **The sector difference isolates the odd content**: subtracting the two rotated
blocks leaves the transport cross term and twice the (curvature + spectral
invariant) term — exactly what distinguishes the self-dual from the anti-self-dual
sector, the `±Tr_ξ(i∇^A)` of the paper's display. -/
theorem sector_difference {R : Type*} [Ring R] (d s t : R) :
    (d * d - (s * d + s * d) - t + s * s) - (d * d + (s * d + s * d) + t + s * s)
      = -(s * d + s * d + (s * d + s * d)) - (t + t) := by
  abel

/-! ## §C — the canonical commutation relations -/

/-- **The smeared canonical commutation relations** (paper page 12,
`[Ê_A(m₁), Â(m₂)] = K(m₁,m₂)`): from the mode-level CCR `[pᵢ, xⱼ] = δᵢⱼ`, the
fields smeared against real coefficient vectors satisfy
`[E(f), A(g)] = (Σᵢ fᵢgᵢ)·1` — the canonical commutation relations of the `SU(2)`
quantum gauge theory, with the *same* nonlocal kernel as the fermionic CAR
(`smearedField_CAR_kernel`): bosons and fermions quantized against one kernel. -/
theorem smeared_CCR_kernel {R : Type*} [Ring R] [Module ℝ R]
    [SMulCommClass ℝ R R] [IsScalarTower ℝ R R]
    (p x : Fin n → R)
    (hccr : ∀ i j, p i * x j - x j * p i = if i = j then 1 else 0)
    (f g : Fin n → ℝ) :
    (∑ i, f i • p i) * (∑ j, g j • x j) - (∑ j, g j • x j) * (∑ i, f i • p i)
      = (∑ i, f i * g i) • (1 : R) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hswap : (∑ j, ∑ i, (g j • x j) * (f i • p i))
      = ∑ i, ∑ j, (g j • x j) * (f i • p i) := Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  have hterm : ∀ i j : Fin n,
      (f i • p i) * (g j • x j) - (g j • x j) * (f i • p i)
        = (if i = j then f i * g j else 0) • (1 : R) := by
    intro i j
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (g j) (f i), ← smul_sub,
      hccr, smul_ite, smul_zero]
    by_cases h : i = j <;> simp [h]
  calc ∑ i, ((∑ j, (f i • p i) * (g j • x j)) - ∑ j, (g j • x j) * (f i • p i))
      = ∑ i, ∑ j, ((f i • p i) * (g j • x j) - (g j • x j) * (f i • p i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ i, ∑ j, (if i = j then f i * g j else 0) • (1 : R) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = ∑ i, (f i * g i) • (1 : R) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [ite_smul]
    _ = (∑ i, f i * g i) • (1 : R) := by rw [← Finset.sum_smul]

/-! ## §D — the ground state is infinitely degenerate -/

/-- `diag(0,0) = 0`. -/
theorem blockDiag_zero {R : Type*} [Ring R] :
    ConfigurationSpaceDiracFluctuation.blockDiag (0 : R) 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ConfigurationSpaceDiracFluctuation.blockDiag]

/-- **The ground state is infinitely degenerate** (paper page 12): with trivial
geometry the Dirac operator acts only on the `(η⁺, η⁻)` factor, so if `D±η± = 0`
then the dressed state `(η⁺, η⁻)·w` is annihilated for **every** Fock element `w` —
the kernel contains a whole Fock factor `Ψ' = (η⁺, η⁻) ⊗ Ψ_CAR`. -/
theorem groundState_degenerate {R : Type*} [Ring R] {Dp Dm ηp ηm : R}
    (hp : Dp * ηp = 0) (hm : Dm * ηm = 0) (w : R) :
    ConfigurationSpaceDiracFluctuation.blockDiag Dp Dm
        * (ConfigurationSpaceDiracFluctuation.blockDiag ηp ηm
            * ConfigurationSpaceDiracFluctuation.blockDiag w w)
      = 0 := by
  rw [ConfigurationSpaceDiracFluctuation.blockDiag_mul,
    ConfigurationSpaceDiracFluctuation.blockDiag_mul, ← mul_assoc, ← mul_assoc,
    hp, hm, zero_mul, blockDiag_zero]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.spectralAsymmetry_vanishes_of_symmetric where
  formalizes @ "claim:if-the-spectrum-of-the-covariant-derivative-is-symmetric-the-operator-conjugate-to-its-own-negative-the-spectral-asymmetry-invariant-vanishes-the-finite-dimensional-face-of-the-atiyah-patodi-singer-eta-invariant",
  supported_by @ "paper:aastrup-grimstrup-arxiv-2410-07290-dirac-operators-on-configuration-spaces"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.spectralInvariant_real where
  supported_by @ "lean:HermitianMat.trace_neg",
  formalizes @ "claim:for-a-skew-adjoint-covariant-derivative-the-spectral-invariant-i-times-the-trace-is-real-a-genuine-observable-entering-the-two-dual-hamiltonian-sectors"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.smeared_CCR_kernel where
  supported_by @ "lean:KroneckerDelta.sum_smul",
  formalizes @ "claim:the-smeared-electric-and-gauge-fields-satisfy-canonical-commutation-relations-with-the-same-nonlocal-kernel-as-the-fermionic-car-unifying-boson-and-fermion-quantization",
  requires @ "claim:for-a-skew-adjoint-covariant-derivative-the-spectral-invariant-i-times-the-trace-is-real-a-genuine-observable-entering-the-two-dual-hamiltonian-sectors"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.groundState_degenerate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.blockDiag_mul",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.blockDiag_zero",
  formalizes @ "claim:when-the-trivial-geometry-dirac-operator-annihilates-both-chiral-vacua-the-whole-fock-dressed-state-is-annihilated-for-every-fock-element-so-the-ground-state-is-infinitely-degenerate"

zil_file_contract physlib.configurationSpaceSpectralAsymmetry where
  promises "The spectral asymmetry (eta-invariant face) and ground-state structure of the configuration-space Dirac operator (Aastrup-Grimstrup arXiv:2410.07290). For a skew-adjoint covariant derivative the spectral invariant i*Tr is real (spectralInvariant_real), and vanishes when the spectrum is symmetric (spectralAsymmetry_vanishes_of_symmetric) -- the finite-dimensional face of the Atiyah-Patodi-Singer eta-invariant. The smeared electric/gauge fields satisfy CCR with the same nonlocal kernel as the fermionic CAR (smeared_CCR_kernel), and when the trivial-geometry Dirac operator annihilates both chiral vacua the whole Fock-dressed state is annihilated, so the ground state is infinitely degenerate (groundState_degenerate)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.spectralInvariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.blockDiag"]
  forbids_substitutes ["the analytic Atiyah-Patodi-Singer index theorem, the eta-invariant of a genuine unbounded elliptic operator, and the infinite-dimensional Fock-space construction, which are the cited spectral-geometry infrastructure",
    "any claim that the physical spectral flow is computed; only the finite-dimensional skew-adjoint trace invariant, the smeared CCR, and the algebraic ground-state annihilation are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.spectralAsymmetry_vanishes_of_symmetric,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.spectralInvariant_real,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.smeared_CCR_kernel,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceSpectralAsymmetry.groundState_degenerate]

/- ZIL-END -/
