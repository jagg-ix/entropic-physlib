/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Bhaduri's inverted-oscillator caricature of the Riemann zeta function

Formalizes the *exact* algebraic core of R. K. Bhaduri, A. Khare, S. M. Reimann, E. L. Tomusiak, *The
Riemann Zeta Function and the Inverted Harmonic Oscillator* (Ann. Phys. **254** (1997) 25). The paper models
the smoothed density of the Riemann zeros by the toy Hamiltonian `H = ½(p_x² + ω₁²x² + p_y² − ω₂²y²)` — a
harmonic oscillator (`ω₁`) perched on an *inverted* oscillator (`ω₂`) — whose single unstable periodic orbit
gives a Gutzwiller/Selberg trace formula. The numerical fits, Strutinsky smoothing and asymptotic
expansions are out of scope; the exact content:

**§A — the monodromy matrix** (Eqs 19–20). The `2×2` reduced monodromy of the unstable orbit is

  `M̃₁ = !![cosh α, sinh α/ω₂; ω₂ sinh α, cosh α]`,   `α = 2πω₂/ω₁`   (`monodromy`),

a symplectic (`det = 1`, `monodromy_det`) hyperbolic/Bogoliubov matrix with eigenvalues `e^{±α}` and
eigenvectors `(1, ±ω₂)` (`monodromy_mulVec_pos/neg`). The Gutzwiller stability denominator is

  `√|det(M̃₁ − I)| = 2|sinh(α/2)| = 2 sinh(πω₂/ω₁)`   (`sqrt_abs_monodromy_sub_one_det`),

via `det(M̃₁ − I) = 2 − 2cosh α = −4 sinh²(α/2)`.

**§B — the inverted-oscillator damping series** (Eq 38). The `sinh` denominator that damps the higher
harmonics is the geometric sum

  `∑_{l≥0} e^{−(l+½)x} = 1/(2 sinh(x/2))`   (`tsum_exp_eq_inv_two_sinh`),   `x > 0`.

**§C — the complex resonance energies** (Eqs 40–41). The Selberg zeta function `ζ_S` of the toy model has
factors `1 + exp[(2πi/a)(E + i(l+½)b)]` (`a = ℏω₁`, `b = ℏω₂`); setting `ζ_S = 0` quantizes the energies to

  `E = (n+½)·ℏω₁ − i(l+½)·ℏω₂`   (`selberg_factor_eq_zero_iff`),

**complex** resonance energies: real part the bound oscillator `(n+½)ℏω₁`, imaginary part the inverted-oscillator
decay width `−(l+½)ℏω₂`. The bound states are "transformed to resonances" by the inverted direction — a
complex-action / complex-energy structure, the `ω₂ ↔ σ` analogue of the Lorentzian width `(σ−½)` smoothing
the Riemann zeros.

## References

* Bhaduri–Khare–Reimann–Tomusiak (1997), Eqs 19–20, 38, 40–41; Gutzwiller; Bogomolny (Selberg zeta).
  structures: `Mathlib` (`Real.cosh/sinh`, `Complex.exp_eq_one_iff`, geometric series). Hyperbolic
  `cosh α = e^α`-structure connects to the repo's Bogoliubov layer (`Bogoliubov.BosonicBogoliubovDiagonalization`,
  `ThermoFieldDynamics.TFDBogoliubovHopf`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ZetaInvertedOscillator

open scoped Real

/-! ## §A — the monodromy matrix -/

/-- **The reduced `2×2` monodromy matrix** of the unstable periodic orbit (Eq 19), `α = 2πω₂/ω₁`. -/
noncomputable def monodromy (ω₂ α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh α, Real.sinh α / ω₂; ω₂ * Real.sinh α, Real.cosh α]

/-- **[Symplectic] `det M̃₁ = 1`.** The monodromy is area-preserving: `cosh²α − sinh²α = 1`. -/
theorem monodromy_det (ω₂ α : ℝ) (hω : ω₂ ≠ 0) : Matrix.det (monodromy ω₂ α) = 1 := by
  rw [monodromy, Matrix.det_fin_two_of]
  have hs : Real.sinh α / ω₂ * (ω₂ * Real.sinh α) = Real.sinh α ^ 2 := by
    field_simp
  rw [hs]; nlinarith [Real.cosh_sq_sub_sinh_sq α]

/-- **[Trace] `tr M̃₁ = 2cosh α`.** -/
theorem monodromy_trace (ω₂ α : ℝ) : Matrix.trace (monodromy ω₂ α) = 2 * Real.cosh α := by
  rw [monodromy, Matrix.trace_fin_two_of]; ring

/-- **[Eigenvalues `e^{±α}`].** The roots of the characteristic polynomial are `e^{±α}`: their product is
`det M̃₁ = 1` and their sum is `tr M̃₁ = 2cosh α` (so `M̃₁` is hyperbolic/unstable, `e^{α} > 1`). -/
theorem monodromy_eigenvalues (ω₂ α : ℝ) (hω : ω₂ ≠ 0) :
    Real.exp α * Real.exp (-α) = Matrix.det (monodromy ω₂ α)
      ∧ Real.exp α + Real.exp (-α) = Matrix.trace (monodromy ω₂ α) := by
  refine ⟨?_, ?_⟩
  · rw [monodromy_det ω₂ α hω, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  · rw [monodromy_trace ω₂ α, Real.cosh_eq]; ring

/-- **[The Gutzwiller stability determinant] `det(M̃₁ − I) = 2 − 2cosh α`.** -/
theorem monodromy_sub_one_det (ω₂ α : ℝ) (hω : ω₂ ≠ 0) :
    Matrix.det (monodromy ω₂ α - 1) = 2 - 2 * Real.cosh α := by
  have hM : monodromy ω₂ α - 1 =
      !![Real.cosh α - 1, Real.sinh α / ω₂; ω₂ * Real.sinh α, Real.cosh α - 1] := by
    rw [monodromy, Matrix.one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hM, Matrix.det_fin_two_of]
  have hs : Real.sinh α / ω₂ * (ω₂ * Real.sinh α) = Real.sinh α ^ 2 := by field_simp
  rw [hs]; nlinarith [Real.cosh_sq_sub_sinh_sq α]

/-- **[Gutzwiller stability denominator] `√|det(M̃₁ − I)| = 2|sinh(α/2)|`.** Equal to `2 sinh(πω₂/ω₁)` for the
orbit, via `det(M̃₁ − I) = −4 sinh²(α/2)`. -/
theorem sqrt_abs_monodromy_sub_one_det (ω₂ α : ℝ) (hω : ω₂ ≠ 0) :
    Real.sqrt |Matrix.det (monodromy ω₂ α - 1)| = 2 * |Real.sinh (α / 2)| := by
  rw [monodromy_sub_one_det ω₂ α hω]
  have hcosh : Real.cosh α = 1 + 2 * Real.sinh (α / 2) ^ 2 := by
    have hcc := Real.cosh_two_mul (α / 2)
    have hcs := Real.cosh_sq_sub_sinh_sq (α / 2)
    rw [show 2 * (α / 2) = α by ring] at hcc
    nlinarith [hcc, hcs]
  have key : (2 : ℝ) - 2 * Real.cosh α = -(4 * Real.sinh (α / 2) ^ 2) := by rw [hcosh]; ring
  rw [key, abs_neg, abs_of_nonneg (by positivity)]
  rw [show (4 : ℝ) * Real.sinh (α / 2) ^ 2 = (2 * |Real.sinh (α / 2)|) ^ 2 by
    rw [mul_pow, sq_abs]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-! ## §B — the inverted-oscillator damping series -/

/-- **[The `sinh` damping series] `∑_{l≥0} e^{−(l+½)x} = 1/(2 sinh(x/2))`** for `x > 0` (Eq 38) — the
geometric sum whose `sinh` denominator damps the higher harmonics of the trace formula. -/
theorem tsum_exp_eq_inv_two_sinh {x : ℝ} (hx : 0 < x) :
    ∑' l : ℕ, Real.exp (-((l : ℝ) + 1 / 2) * x) = 1 / (2 * Real.sinh (x / 2)) := by
  have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hterm : ∀ l : ℕ, Real.exp (-((l : ℝ) + 1 / 2) * x)
      = Real.exp (-(x / 2)) * Real.exp (-x) ^ l := by
    intro l
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, Real.sinh_eq]
  have hv : Real.exp (x / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hsinhne : Real.exp (x / 2) - Real.exp (-(x / 2)) ≠ 0 := by
    have : Real.exp (-(x / 2)) < Real.exp (x / 2) := by
      apply Real.exp_lt_exp.mpr; linarith
    linarith
  have hgne : (1 : ℝ) - Real.exp (-x) ≠ 0 := by linarith
  rw [show Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) by
    rw [← Real.exp_add]; congr 1; ring]
  rw [show Real.exp (-(x / 2)) = (Real.exp (x / 2))⁻¹ from Real.exp_neg _]
  field_simp

/-! ## §C — the complex resonance energies -/

/-- `exp z = −1 ↔ z = (2n+1)πi`. -/
theorem exp_eq_neg_one_iff (z : ℂ) : Complex.exp z = -1 ↔ ∃ n : ℤ, z = (2 * n + 1) * π * Complex.I := by
  have hπ : Complex.exp (π * Complex.I) = -1 := Complex.exp_pi_mul_I
  rw [show (-1 : ℂ) = Complex.exp (π * Complex.I) from hπ.symm, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn]; ring⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn]; ring⟩

/-- **[Selberg-zeta quantization → complex resonance energies] `ζ_S = 0`.** The factor
`1 + exp[(2πi/a)(E + i(l+½)b)]` (with `a = ℏω₁ > 0`, `b = ℏω₂`) vanishes iff the energy is the **complex**
resonance `E = (n+½)a − i(l+½)b` — real part the bound oscillator level `(n+½)ℏω₁`, imaginary part the
inverted-oscillator decay width `−(l+½)ℏω₂`. -/
theorem selberg_factor_eq_zero_iff {a b : ℝ} (ha : a ≠ 0) (l : ℕ) (E : ℂ) :
    1 + Complex.exp ((2 * π * Complex.I / a) * (E + Complex.I * ((l : ℂ) + 1 / 2) * b)) = 0
      ↔ ∃ n : ℤ, E = ((n : ℂ) + 1 / 2) * a - Complex.I * ((l : ℂ) + 1 / 2) * b := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [add_comm, add_eq_zero_iff_eq_neg, exp_eq_neg_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hkey : (2 * π * Complex.I / a) * (E + Complex.I * ((l : ℂ) + 1 / 2) * b)
        = (2 * (n : ℂ) + 1) * π * Complex.I := hn
    field_simp at hkey
    linear_combination hkey / 2
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]; field_simp; ring

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.ZetaInvertedOscillator

end
