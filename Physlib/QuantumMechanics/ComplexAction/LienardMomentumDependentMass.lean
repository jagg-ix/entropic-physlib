/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Real.Sqrt

/-!
# The quantized Liénard oscillator and its momentum-dependent-mass Hamiltonian

The nonlinear Liénard oscillator `ẍ + kxẋ + ω²x + (k²/9)x³ = 0` (Bagchi, Ghose Choudhury & Guha,
arXiv:1305.4566) is a **bi-Hamiltonian** system: the Jacobi-Last-Multiplier (JLM) analysis of the generalized
Liénard equation `ẍ + f(x)ẋ + g(x) = 0` (`f = kx`, `g = ω²x + (k²/9)x³`) forces the multiplier parameter `η`
(with `M = u^η`) to satisfy a **quadratic**, whose two roots give two distinct Hamiltonians. This module
formalizes the exact algebraic backbone of the paper.

* **§A — the JLM quadratic (Eq. 12).** Matching the `x`-coefficient in the JLM constraint (Eq. 10)
 `d/dx(g/f) = −(1/η)(1/η+1)f` forces `2η² + 9η + 9 = 0` (`jlm_quadratic_from_constraint`), which factors as
 `(η+3)(2η+3)` (`jlmEtaQuadratic_factor`) with the two roots `η = −3` and `η = −3/2`
 (`jlmEtaQuadratic_eq_zero_iff`) — the bi-Hamiltonian structure. The integration constant is `ν = ηω²/k`.
* **§B — the `η = −3/2` momentum-dependent-mass Hamiltonian (Eqs. 18–22).** For `η = −3/2` the Hamiltonian
 exponent `(η+2)/(η+1) = −1` (`lienard_exponent_neg32`) turns the kinetic term into `2/p̃`; with `g/f = ax² + b`
 the Hamiltonian is `H = 3ap̃x² + 3bp̃ + 2/p̃` (`lienardHamiltonian_neg32_from_general`), which is exactly the
 **momentum-dependent-mass** form `x²/(2m(p̃)) + U(p̃)` with `m(p̃) = (6ap̃)⁻¹`, `U(p̃) = 3bp̃ + 2/p̃` (an isotonic
 potential) — `lienardHamiltonianNeg32_eq_mdm`. (For `η = −3` the exponent is `1/2`, the harmonic case.)
* **§C — the isotonic spectrum (Eqs. 40–41).** The confluent-hypergeometric series `₁F₁` terminates (Eq. 40)
 `½(ℓ+3/2) − Λ/4 = −n` iff `Λ = 4n + 2ℓ + 3` (`isotonic_termination_iff`), giving the **equispaced** energy
 levels `Ẽₙ = [n + ½(ℓ+3/2)]ω` with spacing `ω` (`lienardEnergy_equispaced`); the angular parameter satisfies
 `ℓ(ℓ+1) = ε − 1/4 + 96/k` (`lienard_ell_relation`).
* **§D — the constants from `g/f` (Eq. 4).** `gOverF_eq` (`g/f = (k/9)x² + ω²/k`) fixes `a = k/9`, `b = ω²/k`.
* **§E — the `η = −3` harmonic branch (Eqs. 18–19).** `lienardHamiltonianNeg3` (`= (3/2)ap̃x² + (3/2)bp̃ − √p̃`,
 exponent `1/2`); `lienardHamiltonian_neg3_from_general`; `lienardHamiltonianNeg3_completedSquare` (`=
 x²/(2(3ap̃)⁻¹) + (3/2)b(√p̃ − 1/(3b))² − 1/(6b)`, the shifted harmonic oscillator — the non-isotonic complement of
 the `η = −3/2` Hamiltonian).
* **§F — the isotonic potential (Eq. 34).** `isotonicU_from_mdmPotential` (`4·U(p̃) = ω²y² + 96/(ky²)` under
 `p̃ = ky²/12`) — the momentum-dependent-mass potential `U` becomes the isotonic `Ũ`, whose `96/k` fixes `ℓ(ℓ+1)`,
 bridging §B to §C.

All results are exact `ring`/`field_simp`/`Real.sqrt` identities — the derived algebra of the
paper (the JLM quadratic, both Legendre-transformed Hamiltonians, the momentum-space isotonic potential, the
series-termination spectrum). The intermediate analysis — the JLM PDE (Eqs. 5–9), the von Roos-ordered
momentum-space Schrödinger equation (Eqs. 25–27) and its reduction to the confluent-hypergeometric ODE
(Eqs. 28–39) — is the paper's calculus, recorded not re-derived; the algebraic endpoints it produces are
formalized here.

## References

* B. Bagchi, A. Ghose Choudhury, P. Guha, arXiv:1305.4566v2, Eqs. 10, 12, 18–22, 40–41.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LienardMomentumDependentMass

/-! ## §A — the Jacobi-Last-Multiplier quadratic and the two Hamiltonians -/

/-- The **JLM quadratic** `2η² + 9η + 9` whose vanishing fixes the multiplier parameter `η = uᶜ` for the Liénard
oscillator (Eq. 12). -/
def jlmEtaQuadratic (η : ℝ) : ℝ := 2 * η ^ 2 + 9 * η + 9

/-- **The JLM quadratic factors** `2η² + 9η + 9 = (η+3)(2η+3)`. -/
theorem jlmEtaQuadratic_factor (η : ℝ) : jlmEtaQuadratic η = (η + 3) * (2 * η + 3) := by
  unfold jlmEtaQuadratic; ring

/-- **The two JLM roots (Eq. 12)** `2η² + 9η + 9 = 0 ↔ η = −3 ∨ η = −3/2` — the bi-Hamiltonian structure of the
Liénard oscillator: `η = −3` (harmonic, studied earlier) and `η = −3/2` (the new momentum-dependent-mass case). -/
theorem jlmEtaQuadratic_eq_zero_iff (η : ℝ) : jlmEtaQuadratic η = 0 ↔ η = -3 ∨ η = -3 / 2 := by
  rw [jlmEtaQuadratic_factor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> subst h
    · exact Or.inl (by norm_num)
    · exact Or.inr (by norm_num)

/-- **The JLM quadratic is derived from the multiplier constraint (Eq. 10)** — matching the coefficient of `x` in
`d/dx(g/f) = −(1/η)(1/η+1)f`, i.e. `2/9 = −(1+η)/η²` (using `g/f = ω²/k + (k/9)x²`, `f = kx`), is equivalent to
`2η² + 9η + 9 = 0`. This is where the bi-Hamiltonian quadratic comes from. -/
theorem jlm_quadratic_from_constraint (η : ℝ) (hη : η ≠ 0) :
    (2 : ℝ) / 9 = -(1 + η) / η ^ 2 ↔ jlmEtaQuadratic η = 0 := by
  rw [jlmEtaQuadratic, div_eq_div_iff (by norm_num) (pow_ne_zero 2 hη)]
  constructor <;> intro h <;> nlinarith [h]

/-- The **JLM integration constant** `ν = ηω²/k` (the constant term of Eq. 11). -/
noncomputable def jlmNu (η ω k : ℝ) : ℝ := η * ω ^ 2 / k

/-- **The integration constant at the two roots (Eq. 12)** `ν = −3ω²/k` (for `η = −3`) and `ν = −3ω²/(2k)` (for
`η = −3/2`). -/
theorem jlmNu_at_roots (ω k : ℝ) :
    jlmNu (-3) ω k = -3 * ω ^ 2 / k ∧ jlmNu (-3 / 2) ω k = -3 * ω ^ 2 / (2 * k) := by
  constructor <;> · unfold jlmNu; ring

/-! ## §B — the `η = −3/2` momentum-dependent-mass Hamiltonian -/

/-- **The Hamiltonian exponent at `η = −3/2`** `(η+2)/(η+1) = −1` — the momentum power in the kinetic term of
Eq. 18 becomes `p̃⁻¹`, producing the isotonic `2/p̃` term. -/
theorem lienard_exponent_neg32 : ((-3 / 2 : ℝ) + 2) / ((-3 / 2) + 1) = -1 := by norm_num

/-- **The Hamiltonian exponent at `η = −3`** `(η+2)/(η+1) = 1/2` — the harmonic (`√p̃`) case for comparison. -/
theorem lienard_exponent_neg3 : ((-3 : ℝ) + 2) / ((-3) + 1) = 1 / 2 := by norm_num

/-- The **Liénard `η = −3/2` Hamiltonian** `H = 3ap̃x² + 3bp̃ + 2/p̃` (Eq. 20), with `g/f = ax² + b`. -/
noncomputable def lienardHamiltonianNeg32 (a b p x : ℝ) : ℝ := 3 * a * p * x ^ 2 + 3 * b * p + 2 / p

/-- The **momentum-dependent mass** `m(p̃) = (6ap̃)⁻¹` (Eq. 22). -/
noncomputable def mdmMass (a p : ℝ) : ℝ := (6 * a * p)⁻¹

/-- The **isotonic momentum-space potential** `U(p̃) = 3bp̃ + 2/p̃` (Eq. 22). -/
noncomputable def mdmPotential (b p : ℝ) : ℝ := 3 * b * p + 2 / p

/-- **The `η = −3/2` Hamiltonian evaluated from the general Eq. 18** — substituting the coefficients
`1/(η+2) = 2`, `η/(η+1) = 3` and exponent `−1` at `η = −3/2` with `g/f = ax² + b` reproduces `lienardHamiltonianNeg32`. -/
theorem lienardHamiltonian_neg32_from_general (a b p x : ℝ) (hp : p ≠ 0) :
    2 * p⁻¹ + 3 * (p * (a * x ^ 2 + b)) = lienardHamiltonianNeg32 a b p x := by
  unfold lienardHamiltonianNeg32
  field_simp
  ring

/-- **The Liénard `η = −3/2` Hamiltonian is of momentum-dependent-mass form** `H = x²/(2m(p̃)) + U(p̃)` (Eq. 21) —
the roles of position and momentum are transposed: the mass `m(p̃) = (6ap̃)⁻¹` depends on the momentum and the
potential `U(p̃) = 3bp̃ + 2/p̃` is isotonic. -/
theorem lienardHamiltonianNeg32_eq_mdm (a b p x : ℝ) (hp : p ≠ 0) :
    lienardHamiltonianNeg32 a b p x = x ^ 2 / (2 * mdmMass a p) + mdmPotential b p := by
  unfold lienardHamiltonianNeg32 mdmMass mdmPotential
  field_simp
  ring

/-! ## §C — the isotonic spectrum from confluent-hypergeometric termination -/

/-- **The confluent-hypergeometric termination (Eq. 40)** `½(ℓ+3/2) − Λ/4 = −n ↔ Λ = 4n + 2ℓ + 3` — the `₁F₁`
series truncates to a polynomial exactly at these eigenvalues. -/
theorem isotonic_termination_iff (n : ℕ) (ℓ lam : ℝ) :
    (1 / 2) * (ℓ + 3 / 2) - lam / 4 = -(n : ℝ) ↔ lam = 4 * n + 2 * ℓ + 3 := by
  constructor <;> intro h <;> linarith

/-- The **Liénard isotonic energy levels** `Ẽₙ = [n + ½(ℓ+3/2)]ω` (Eq. 41). -/
noncomputable def lienardEnergy (n : ℕ) (ℓ ω : ℝ) : ℝ := ((n : ℝ) + (1 / 2) * (ℓ + 3 / 2)) * ω

/-- **The spectrum is equispaced** `Ẽₙ₊₁ − Ẽₙ = ω` — the momentum-dependent-mass isotonic oscillator has a
harmonic-oscillator-like equispaced ladder with spacing `ω`. -/
theorem lienardEnergy_equispaced (n : ℕ) (ℓ ω : ℝ) :
    lienardEnergy (n + 1) ℓ ω - lienardEnergy n ℓ ω = ω := by
  unfold lienardEnergy; push_cast; ring

/-- **The angular parameter relation (Eqs. 35, 41)** `ℓ(ℓ+1) = ε − 1/4 + 96/k` for `ℓ = −1/2 + √(96/k + ε)` — the
isotonic centrifugal coefficient fixing `ℓ` in terms of the ambiguity parameter `ε` and the coupling `k`. -/
theorem lienard_ell_relation (ℓ ε k : ℝ) (hnn : 0 ≤ 96 / k + ε)
    (h : ℓ = -1 / 2 + Real.sqrt (96 / k + ε)) :
    ℓ * (ℓ + 1) = ε - 1 / 4 + 96 / k := by
  subst h
  rw [show (-1 / 2 + Real.sqrt (96 / k + ε)) * ((-1 / 2 + Real.sqrt (96 / k + ε)) + 1)
      = Real.sqrt (96 / k + ε) ^ 2 - 1 / 4 from by ring, Real.sq_sqrt hnn]
  ring

/-! ## §D — the constants `a = k/9`, `b = ω²/k` from `g/f` (Eq. 4) -/

/-- The ratio `g/f = (ω²x + (k²/9)x³)/(kx)` of the Liénard data `f = kx`, `g = ω²x + (k²/9)x³` (Eq. 4). -/
noncomputable def gOverF (ω k x : ℝ) : ℝ := (ω ^ 2 * x + (k ^ 2 / 9) * x ^ 3) / (k * x)

/-- **`g/f = (k/9)x² + ω²/k`** — the quadratic form `ax² + b` fixing the constants `a = k/9`, `b = ω²/k` used in
the Liénard Hamiltonians (Eq. 18). -/
theorem gOverF_eq (ω k x : ℝ) (hk : k ≠ 0) (hx : x ≠ 0) :
    gOverF ω k x = (k / 9) * x ^ 2 + ω ^ 2 / k := by
  unfold gOverF; field_simp; ring

/-! ## §E — the `η = −3` harmonic-oscillator Hamiltonian (Eqs. 18–19) -/

/-- The **Liénard `η = −3` Hamiltonian** `H = (3/2)ap̃x² + (3/2)bp̃ − √p̃` (Eq. 18 at `η = −3`, exponent `1/2`). -/
noncomputable def lienardHamiltonianNeg3 (a b p x : ℝ) : ℝ :=
  (3 / 2) * a * p * x ^ 2 + (3 / 2) * b * p - Real.sqrt p

/-- **The `η = −3` Hamiltonian from the general Eq. 18** — the coefficients `1/(η+2) = −1`, `η/(η+1) = 3/2` and
exponent `1/2` (so `p̃^{(η+2)/(η+1)} = √p̃`) at `η = −3` with `g/f = ax² + b`. -/
theorem lienardHamiltonian_neg3_from_general (a b p x : ℝ) :
    -Real.sqrt p + (3 / 2) * (p * (a * x ^ 2 + b)) = lienardHamiltonianNeg3 a b p x := by
  unfold lienardHamiltonianNeg3; ring

/-- **The `η = −3` Hamiltonian is a shifted harmonic oscillator in `√p̃` (Eq. 19)** `H = x²/(2(3ap̃)⁻¹) +
(3/2)b(√p̃ − 1/(3b))² − 1/(6b)` — completing the square in `√p̃` exhibits the **harmonic** (non-isotonic) branch of
the bi-Hamiltonian pair, the complement of the `η = −3/2` momentum-dependent-mass Hamiltonian. -/
theorem lienardHamiltonianNeg3_completedSquare (a b p x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hp : 0 < p) :
    lienardHamiltonianNeg3 a b p x
      = x ^ 2 / (2 * (3 * a * p)⁻¹) + (3 / 2) * b * (Real.sqrt p - 1 / (3 * b)) ^ 2 - 1 / (6 * b) := by
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  unfold lienardHamiltonianNeg3
  rw [show x ^ 2 / (2 * (3 * a * p)⁻¹) = 3 / 2 * a * p * x ^ 2 from by
    have := hp.ne'; field_simp]
  set s := Real.sqrt p
  rw [← hs]
  field_simp
  ring

/-! ## §F — the isotonic potential `Ũ(y)` (Eq. 34) -/

/-- The **isotonic momentum-space potential** `Ũ(y) = ω²y² + 96/(ky²)` (Eq. 34) — the harmonic `ω²y²` plus the
`1/y²` centrifugal barrier that gives the potential its isotonic character. -/
noncomputable def isotonicU (ω k y : ℝ) : ℝ := ω ^ 2 * y ^ 2 + 96 / (k * y ^ 2)

/-- **The momentum-dependent-mass potential becomes the isotonic potential** `4·U(p̃) = ω²y² + 96/(ky²)` under the
scaling `p̃ = ky²/12` (`= 3ay²/4`, `a = k/9`), with `b = ω²/k` and `Ũ = U/(η+1)² = 4U` at `η = −3/2` — the origin
of the isotonic centrifugal coefficient `96/k` that fixes `ℓ(ℓ+1)` in `lienard_ell_relation`, tying the
momentum-dependent-mass Hamiltonian (§B) to the isotonic spectrum (§C). -/
theorem isotonicU_from_mdmPotential (ω k y : ℝ) (hk : k ≠ 0) (hy : y ≠ 0) :
    4 * mdmPotential (ω ^ 2 / k) (k * y ^ 2 / 12) = isotonicU ω k y := by
  unfold mdmPotential isotonicU; field_simp; ring

end Physlib.QuantumMechanics.ComplexAction.LienardMomentumDependentMass
