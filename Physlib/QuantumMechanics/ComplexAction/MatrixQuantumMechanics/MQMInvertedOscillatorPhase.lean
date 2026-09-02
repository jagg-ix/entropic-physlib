/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# MQM singlet sector: the inverted oscillator and its WKB scattering phase (Alexandrov §III.2)

In the double-scaling limit the singlet sector of Matrix Quantum Mechanics reduces to a system of free
fermions in the **inverted (upside-down) oscillator** potential `V(x) = −½x²`, with single-particle
Hamiltonian `h(x,p) = ½p² − ½x²` (Alexandrov, hep-th/0311273, Eqs. III.37, III.48). This is exactly the
inverted oscillator underlying the Moore–Plesser–Ramgoolam `c=1` `S`-matrix and the Bhaduri/Nagao–Nielsen
complex-action constructions already formalized — the matrix-model core of `c=1` 2d string theory.

* **§A — the Fermi sea of the inverted oscillator.** `mqmFermiHamiltonian x p = ½p² − ½x²` (Eq. III.48); the
  boundary of the Fermi sea `h(x,p) = ε` (Eq. III.25) is the two-valued profile `p = ±√(2ε + x²)`
  (`mqmFermiBoundary`, Eq. III.50, Fig. III.2). The potential is **unbounded below**
  (`mqmFermiHamiltonian_unbounded_below`): there is no true ground state — the instability of the inverted
  oscillator noted in the thesis (p. 70).
* **§B — the WKB scattering phase.** The phase of the Fermi-level wavefunction is `Φ_ε(x) ≈ ½x² + ε log x −
  φ(ε)` with `φ(ε) = π/4 − (i/2) log[Γ(½+iε)/Γ(½−iε)]` (Eqs. III.39–III.40). We show that the Gamma ratio is
  a **pure phase** — `Γ(½+iε)/Γ(½−iε) = e^{−2i·Θ(ε)}` with `Θ = arg Γ(½−iε)` the Moore–Plesser–Ramgoolam
  reflection phase (Eq. 4.5) — so `φ(ε) = π/4 − Θ(ε)` is real (`mqmWkbPhase`) and the inverted-oscillator
  reflection coefficient is unitary (`mqmGammaRatio_norm_one`).

## References

* S. Yu. Alexandrov, *Matrix Quantum Mechanics and Two-dimensional String Theory in Non-trivial
  Backgrounds*, hep-th/0311273, Ch. III §2, Eqs. (III.25), (III.37), (III.39)–(III.40), (III.48), (III.50).


-/

set_option autoImplicit false

open Complex Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMInvertedOscillatorPhase


/-- **The MQM single-particle Hamiltonian** `h(x,p) = ½p² − ½x²` (Eq. III.48): the inverted-oscillator energy
that, after double scaling, governs the free fermions of the singlet sector (Eq. III.37). -/
noncomputable def mqmFermiHamiltonian (x p : ℝ) : ℝ := (1 / 2) * p ^ 2 - (1 / 2) * x ^ 2

/-- `h(x,p) = ½(p² − x²)` — the inverted oscillator. -/
lemma mqmFermiHamiltonian_eq_inverted (x p : ℝ) :
    mqmFermiHamiltonian x p = (1 / 2) * (p ^ 2 - x ^ 2) := by
  unfold mqmFermiHamiltonian; ring

/-- **The upper branch of the Fermi-sea boundary** `p₊(x) = √(2ε + x²)` (Eq. III.50): the locus `h = ε`
(Eq. III.25) that bounds the phase-space droplet (Fig. III.2). -/
noncomputable def mqmFermiBoundary (ε x : ℝ) : ℝ := Real.sqrt (2 * ε + x ^ 2)

/-- **[The Fermi-sea boundary lies on the energy shell]** `h(x, p₊(x)) = ε`: the profile `p = √(2ε + x²)`
saturates `½p² − ½x² = ε` wherever `2ε + x² ≥ 0`. -/
lemma mqmFermiBoundary_mem (ε x : ℝ) (h : 0 ≤ 2 * ε + x ^ 2) :
    mqmFermiHamiltonian x (mqmFermiBoundary ε x) = ε := by
  unfold mqmFermiHamiltonian mqmFermiBoundary
  rw [Real.sq_sqrt h]; ring

/-- **[The inverted oscillator is unbounded below]** for any momentum `p` and any bound `B` there is a
position `x` with `h(x,p) < B` — there is no ground state (the instability noted on p. 70). -/
lemma mqmFermiHamiltonian_unbounded_below (p B : ℝ) :
    ∃ x : ℝ, mqmFermiHamiltonian x p < B := by
  refine ⟨Real.sqrt (p ^ 2 + 2 * |B| + 1), ?_⟩
  unfold mqmFermiHamiltonian
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [neg_abs_le B]


/-- **The MQM WKB scattering phase** `φ(ε) = π/4 − Θ(ε)` (Eq. III.40), with `Θ(ε) = arg Γ(½ − iε)` the
Moore–Plesser–Ramgoolam reflection phase (Eq. 4.5). The manifestly real form of
`π/4 − (i/2) log[Γ(½+iε)/Γ(½−iε)]`. -/
noncomputable def mqmWkbPhase (ε : ℝ) : ℝ := Real.pi / 4 - reflectionPhase ε

/-- **[The WKB Gamma ratio is a pure phase]** `Γ(½+iε)/Γ(½−iε) = e^{−2i·Θ(ε)}`. This is the reciprocal of the
Moore–Plesser–Ramgoolam Gamma factor `gammaRatio_eq_exp_two_reflectionPhase`; its unit modulus is what makes
`φ(ε)` real. -/
lemma mqmGammaRatio_eq_exp (ε : ℝ) :
    Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (ε : ℂ))
        / Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (ε : ℂ))
      = Complex.exp (-(2 * (reflectionPhase ε : ℂ) * Complex.I)) := by
  rw [← inv_div, gammaRatio_eq_exp_two_reflectionPhase, ← Complex.exp_neg]

/-- **[The WKB Gamma ratio in terms of `φ`]** `Γ(½+iε)/Γ(½−iε) = e^{2i(φ(ε) − π/4)}` — the inverted-oscillator
reflection data expressed through the WKB scattering phase `φ` of Eq. III.40. -/
lemma mqmGammaRatio_eq_exp_wkb (ε : ℝ) :
    Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (ε : ℂ))
        / Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (ε : ℂ))
      = Complex.exp (2 * ((mqmWkbPhase ε - Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [mqmGammaRatio_eq_exp]
  congr 1
  unfold mqmWkbPhase
  push_cast; ring

/-- **[The inverted-oscillator reflection coefficient is unitary]** `‖Γ(½+iε)/Γ(½−iε)‖ = 1` — the pure-phase
property of the singlet-sector scattering, matching the theory-I unitarity of the Moore–Plesser–Ramgoolam
`S`-matrix. -/
lemma mqmGammaRatio_norm_one (ε : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * (ε : ℂ))
      / Complex.Gamma (((1 / 2 : ℝ) : ℂ) - Complex.I * (ε : ℂ))‖ = 1 := by
  rw [← inv_div, norm_inv, norm_gamma_half_ratio, inv_one]

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMInvertedOscillatorPhase

end
