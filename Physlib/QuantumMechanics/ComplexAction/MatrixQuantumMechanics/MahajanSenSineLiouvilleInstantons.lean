/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMInvertedOscillatorPhase
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Chiral MQM and instantons in sine-Liouville theory (Alexandrov–Mahajan–Sen)

The chiral / light-cone representation of Matrix Quantum Mechanics underlies the computation of instanton
(non-perturbative) effects in the sine-Liouville description of 2d string theory in a non-trivial tachyon
background (Alexandrov, Mahajan, Sen, arXiv:2311.04969, §2). The singlet sector reduces to free fermions in
the inverse oscillator `V(x) = −½x²`; in chiral phase-space coordinates `x_± = (x ± p)/√2` the one-fermion
Hamiltonian becomes a first-order operator with power-law eigenfunctions, and the fermion scattering phase off
the potential is a Gamma function whose imaginary part encodes the tunneling that drives the instanton
effects. This continues `[[project_alexandrov_mqm_thesis]]`
(`MatrixQuantumMechanics.MQMInvertedOscillatorPhase`, `MatrixQuantumMechanics.TodaLaxHirotaString`).

* **§A — chiral coordinates diagonalize the inverse oscillator** (Eq. 2.1). `chiralProduct_eq_neg_hamiltonian`:
  `x_+ x_- = −H₀` with `H₀ = ½(p² − x²)` the inverse-oscillator Hamiltonian (`mqmFermiHamiltonian`).
* **§B — the chiral eigenfunction** (Eq. 2.3). `chiral_euler_eigen`: the power `u^s` is an eigenfunction of
  the Euler operator `u d/du`, `u · (u^s)' = s u^s`; with `s = iE − ½` this gives the chiral one-fermion
  eigenfunction `ψ^E ∝ x_+^{iE−½}` with `(x_+ ∂_{x_+} + ½)ψ = iE ψ`.
* **§C — the tunneling scattering phase** (Eqs. 2.5–2.6). `norm_gamma_half_add_I_sq`:
  `‖Γ(½+iE)‖² = π/cosh(πE)`; `scatteringAmplitude_normSq`: the fermion reflection amplitude
  `e^{iφ₀(E)} = e^{iπ/4 − πE/2}Γ(½+iE)/√(2π)` has `‖e^{iφ₀}‖² = 1/(1 + e^{2πE}) < 1` — the non-unitarity
  `Im φ₀(E) = ½log(1 + e^{2πE}) > 0` is the tunneling of fermions through the inverse oscillator that produces
  the instantons.

## References

* S. Alexandrov, R. Mahajan, A. Sen, *Instantons in sine-Liouville theory*, arXiv:2311.04969, §2,
  Eqs. (2.1), (2.3), (2.5), (2.6).


-/

set_option autoImplicit false

open Complex Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMInvertedOscillatorPhase

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MahajanSenSineLiouvilleInstantons


/-- **The chiral phase-space coordinate** `x_+ = (x + p)/√2` (Eq. 2.1). -/
noncomputable def chiralPlus (x p : ℝ) : ℝ := (x + p) / Real.sqrt 2

/-- **The chiral phase-space coordinate** `x_- = (x − p)/√2` (Eq. 2.1). -/
noncomputable def chiralMinus (x p : ℝ) : ℝ := (x - p) / Real.sqrt 2

/-- **[Chiral coordinates diagonalize the inverse oscillator, Eq. 2.1]** `x_+ x_- = −H₀`, where
`H₀ = ½(p² − x²)` is the inverse-oscillator one-fermion Hamiltonian (`mqmFermiHamiltonian`). The product of
the canonically-conjugate chiral coordinates is (minus) the Hamiltonian — this is what makes the chiral
Hamiltonian first-order. -/
lemma chiralProduct_eq_neg_hamiltonian (x p : ℝ) :
    chiralPlus x p * chiralMinus x p = -(mqmFermiHamiltonian x p) := by
  unfold chiralPlus chiralMinus mqmFermiHamiltonian
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring


/-- **[Euler-operator eigenfunction, Eq. 2.3]** `u · (u^s)' = s u^s`: the power `u^s` is an eigenfunction of
the scaling (Euler) operator `u d/du` with eigenvalue `s`. With `s = iE − ½` this is the chiral one-fermion
eigenfunction `ψ^E_+ ∝ x_+^{iE−½}` (Eq. 2.3): `(x_+ ∂_{x_+} + ½) x_+^{iE−½} = iE x_+^{iE−½}`. -/
lemma chiral_euler_eigen (s u : ℂ) (hdom : 0 < u.re ∨ u.im ≠ 0) :
    u * deriv (fun z => z ^ s) u = s * u ^ s := by
  have hu : u ≠ 0 := by
    rcases hdom with h | h
    · exact fun he => by simp [he] at h
    · exact fun he => by simp [he] at h
  have hpow : u ^ (s - 1) * u = u ^ s := by
    have hadd := Complex.cpow_add (s - 1) 1 hu
    rw [Complex.cpow_one] at hadd
    rw [← hadd]
    congr 1
    ring
  rw [Complex.deriv_cpow_const (Complex.mem_slitPlane_iff.mpr hdom), ← hpow]
  ring


/-- **[`‖Γ(½+iE)‖² = π/cosh(πE)`]** the modulus-squared of the scattering-phase Gamma factor, from the
reflection formula `Γ(s)Γ(1−s) = π/sin(πs)` together with `Γ(½−iE) = conj Γ(½+iE)` and
`sin(π(½+iE)) = cosh(πE)`. -/
lemma norm_gamma_half_add_I_sq (E : ℝ) :
    ‖Complex.Gamma (1 / 2 + Complex.I * (E : ℂ))‖ ^ 2 = Real.pi / Real.cosh (Real.pi * E) := by
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 / 2 + Complex.I * (E : ℂ)))
      = (Real.cosh (Real.pi * E) : ℂ) := by
    rw [show (Real.pi : ℂ) * (1 / 2 + Complex.I * (E : ℂ))
          = Complex.I * ((Real.pi * E : ℝ) : ℂ) + (Real.pi : ℂ) / 2 from by push_cast; ring,
      Complex.sin_add_pi_div_two,
      show Complex.I * ((Real.pi * E : ℝ) : ℂ) = ((Real.pi * E : ℝ) : ℂ) * Complex.I from mul_comm _ _,
      Complex.cos_mul_I, Complex.ofReal_cosh]
  have hconj : Complex.Gamma (1 - (1 / 2 + Complex.I * (E : ℂ)))
      = (starRingEnd ℂ) (Complex.Gamma (1 / 2 + Complex.I * (E : ℂ))) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + Complex.I * (E : ℂ))
  rw [hconj, Complex.mul_conj, hsin, Complex.normSq_eq_norm_sq] at hrefl
  exact_mod_cast hrefl

/-- **The fermion reflection amplitude** `e^{iφ₀(E)} = e^{iπ/4 − πE/2} Γ(½+iE)/√(2π)` (Eq. 2.5) — the
scattering off the inverse oscillator. -/
noncomputable def scatteringAmplitude (E : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ) - ((Real.pi * E / 2 : ℝ) : ℂ))
    / (Real.sqrt (2 * Real.pi) : ℂ) * Complex.Gamma (1 / 2 + Complex.I * (E : ℂ))

/-- **[Tunneling / non-unitarity, Eqs. 2.5–2.6]** `‖e^{iφ₀(E)}‖² = 1/(1 + e^{2πE}) < 1`. The reflection
amplitude of the inverse oscillator is **not** a pure phase: its imaginary scattering phase
`Im φ₀(E) = ½log(1 + e^{2πE}) > 0` is the manifestation of fermions tunneling through the potential — the
non-perturbative effect that produces the instantons. (Compare the non-unitary theory-II reflection factor of
Moore–Plesser–Ramgoolam.) -/
lemma scatteringAmplitude_normSq (E : ℝ) :
    ‖scatteringAmplitude E‖ ^ 2 = 1 / (1 + Real.exp (2 * Real.pi * E)) := by
  have hb : Real.exp (Real.pi * E) ≠ 0 := (Real.exp_pos _).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : (1 : ℝ) + Real.exp (Real.pi * E) ^ 2 ≠ 0 := by positivity
  have hre : (Complex.I * ((Real.pi / 4 : ℝ) : ℂ) - ((Real.pi * E / 2 : ℝ) : ℂ)).re
      = -(Real.pi * E / 2) := by
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [scatteringAmplitude, norm_mul, norm_div, mul_pow, div_pow, Complex.norm_exp,
    norm_gamma_half_add_I_sq, hre, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity), ← Real.exp_nat_mul,
    show ((2 : ℕ) : ℝ) * -(Real.pi * E / 2) = -(Real.pi * E) from by push_cast; ring,
    Real.cosh_eq, Real.exp_neg,
    show Real.exp (2 * Real.pi * E) = Real.exp (Real.pi * E) ^ 2 from by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
  field_simp
  ring

/-- **[Tunneling: the amplitude is not unitary]** `‖e^{iφ₀(E)}‖ < 1`. -/
lemma scatteringAmplitude_norm_lt_one (E : ℝ) : ‖scatteringAmplitude E‖ < 1 := by
  have hlt : ‖scatteringAmplitude E‖ ^ 2 < 1 := by
    rw [scatteringAmplitude_normSq, div_lt_one (by positivity)]
    nlinarith [Real.exp_pos (2 * Real.pi * E)]
  nlinarith [norm_nonneg (scatteringAmplitude E), hlt]


/-- **[Fermi-sea boundary = energy shell, Eq. 2.19]** the unperturbed Fermi-sea profile `x_+ x_- = μ` is the
energy shell `H₀ = −μ`: the fermions fill the inverse oscillator up to the Fermi level `E = −μ`. (This is the
`v_± = 0` / zero-perturbation limit of Eq. 2.19; the boundary of the region filled by the fermions.) -/
lemma chiral_fermiSurface_iff (x p μ : ℝ) :
    chiralPlus x p * chiralMinus x p = μ ↔ mqmFermiHamiltonian x p = -μ := by
  rw [chiralProduct_eq_neg_hamiltonian]
  constructor <;> intro h <;> linarith


/-- **The sine-Liouville instanton action** `S_n = 2μ[θ_n + (2 − 1/R)λ e^{−X/2R} sin(θ_n/R)]` (Eq. 2.29). -/
noncomputable def instantonAction (R μ lam X θ : ℝ) : ℝ :=
  2 * μ * (θ + (2 - 1 / R) * lam * Real.exp (-X / (2 * R)) * Real.sin (θ / R))

/-- **The instanton-phase residual** `sin θ − a₁ sin((1−R)/R · θ)` (Eq. 2.31): the phase `θ_n` is a zero of
this, with boundary condition `θ_n(0) = πn`. -/
noncomputable def instantonPhaseResidual (R a θ : ℝ) : ℝ :=
  Real.sin θ - a * Real.sin ((1 - R) / R * θ)

/-- **[Unperturbed instanton phase, Eq. 2.31 at `λ = 0`]** at vanishing coupling (`a₁ = 0`) the phase
`θ_n = πn` solves the phase equation `sin θ_n = a₁ sin((1−R)/R θ_n)`. -/
lemma instantonPhaseResidual_unperturbed (R : ℝ) (n : ℕ) :
    instantonPhaseResidual R 0 (Real.pi * n) = 0 := by
  unfold instantonPhaseResidual
  rw [mul_comm, Real.sin_nat_mul_pi]
  ring

/-- **[Unperturbed D-instanton action, Eqs. 2.27, 2.29]** at vanishing coupling (`λ = 0`) with the
unperturbed phase `θ_n = πn`, the instanton action is `S_n = 2πnμ` — the D-instanton action whose
exponential `e^{−2πnμ}` is the leading non-perturbative correction to the free energy (Eq. 2.27). -/
lemma instantonAction_unperturbed (R μ X : ℝ) (n : ℕ) :
    instantonAction R μ 0 X (Real.pi * n) = 2 * Real.pi * n * μ := by
  unfold instantonAction
  ring

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MahajanSenSineLiouvilleInstantons

end
