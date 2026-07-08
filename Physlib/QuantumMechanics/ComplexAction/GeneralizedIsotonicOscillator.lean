/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LienardMomentumDependentMass
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Purely nonlinear oscillators generalizing an isotonic potential

The exact-algebra backbone of Ghose-Choudhury, Ghosh, Guha & Pandey (arXiv:1906.10387) — a nonlinear
generalization of the isotonic oscillator in the same spirit as the purely nonlinear generalization of the
harmonic oscillator. This **extends** the isotonic potential `isotonicU` of `LienardMomentumDependentMass`
(`ω²y² + 96/(ky²)`, the momentum-space isotonic potential of the Liénard oscillator).

* **§A — the isotonic potential minimum (Eq. 3.1).** `isotonicRational a b ζ = aζ² + b/ζ²`; **`isotonicRational_ge`**
 (`aζ² + b/ζ² ≥ 2√(ab)`, the AM–GM minimum, achieved at `ζ₀ = (b/a)^{1/4}`). Applied to the Liénard `isotonicU`
 via **`isotonicU_eq_isotonicRational`** and **`isotonicU_ge`**.
* **§B — symmetrization to the harmonic oscillator (Eq. 3.4–3.6).** The standard isotonic potential
 `stdIsotonicU k x = (k/2)((x+1) − 1/(x+1))²`; **`stdIsotonicU_eq`** (`= 2k·h²`, `h = ½((x+1) − 1/(x+1))`),
 **`stdIsotonic_force`** (`−U' = −k(x+1) + k/(x+1)³`, the isotonic equation of motion), and
 **`symmIsotonicU_quarter`** (the symmetric potential `2kξ²` reduces to the LHO `ξ²/2` at `k = 1/4`, giving
 **isochronicity**).
* **§C — the period Beta–Gamma identity (Eqs. 2.7–2.8).** `betaFn u v = Γ(u)Γ(v)/Γ(u+v)`; **`betaFn_half`**
 (`B(1/(α+1), 1/2) = √π Γ(1/(α+1))/Γ((α+3)/(2(α+1)))`) and **`periodU_at_one`** (the amplitude-dependent period
 `T` reduces to the harmonic `2π/c` at `α = 1`).
* **§D — the generalized isotonic symmetry (Eqs. 4.1–4.3).** **`sqrt_sq_add_one_mul_sub`**
 (`(√(ξ²+1)+ξ)(√(ξ²+1)−ξ) = 1`, the hyperbolic identity) and **`genIsotonicU_symm`** (the generalized potential
 `Ũ(ξ) = (c/8)((√(ξ²+1)+ξ)^{(α+1)/2} − (…)^{−(α+1)/2})²` is even, `Ũ(−ξ) = Ũ(ξ)`).
* **§E — the reduced equation of motion (Theorem 1.1).** **`genIsotonic_force_identity`**
 (`(q^β − q^{−β})(q^{β−1} + q^{−β−1}) = q^α − q^{−(α+2)}`, `β = (α+1)/2`) and **`genIsotonic_reduced_force`**
 (with `c_α = 8/(α+1)` the potential gradient reduces to `q^α − q^{−(α+2)}`, i.e. `q̈ + q^α = 1/q^{α+2}`).
* **§F — the amplitude-dependent frequency (page 3).** `frequencyCa cα α A = |A|^{(α−1)/2}√(c_α²(α+1)/2)`;
 **`frequencyCa_at_one`** (`= c_α` at `α = 1`, the isochronous harmonic limit).

All results are exact `ring`/`field_simp`/`Real.sqrt`/`Real.Gamma`/`Real.rpow` identities. The
paper's analytic content — the Ateb-function solutions, the Mañosas–Torres period-symmetrization integral
(Eqs. 2.6–2.7), and the hypergeometric period series (Eqs. 4.6–4.7) — is the calculus of special functions,
recorded not re-derived; the closed-form endpoints (potential minima, symmetrized forms, the Beta–Gamma period,
the symmetry of the generalized potential) are formalized here.

## References

* A. Ghose-Choudhury, A. Ghosh, P. Guha, A. Pandey, arXiv:1906.10387v2, Eqs. 2.8, 3.1–3.6, 4.1–4.3. Extends
 `LienardMomentumDependentMass` (the isotonic potential `isotonicU`).

No new axioms.
-/

set_option autoImplicit false

open scoped Real

open Physlib.QuantumMechanics.ComplexAction.LienardMomentumDependentMass

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator

/-! ## §A — the isotonic potential minimum -/

/-- The **isotonic (rational) potential** `V(ζ) = aζ² + b/ζ²` (Eq. 3.1) — two branches with a minimum on each. -/
noncomputable def isotonicRational (a b ζ : ℝ) : ℝ := a * ζ ^ 2 + b / ζ ^ 2

/-- **The isotonic potential is bounded below by `2√(ab)`** `aζ² + b/ζ² ≥ 2√(ab)` — the AM–GM minimum
`V(ζ₀) = 2√(ab)` at `ζ₀ = (b/a)^{1/4}`. -/
theorem isotonicRational_ge (a b ζ : ℝ) (ha : 0 < a) (hb : 0 < b) (hζ : ζ ≠ 0) :
    2 * Real.sqrt (a * b) ≤ isotonicRational a b ζ := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hab : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha.le b
  have hexp : (Real.sqrt a * ζ - Real.sqrt b / ζ) ^ 2 = isotonicRational a b ζ - 2 * Real.sqrt (a * b) := by
    have he : (Real.sqrt a * ζ - Real.sqrt b / ζ) ^ 2
        = Real.sqrt a ^ 2 * ζ ^ 2 + Real.sqrt b ^ 2 / ζ ^ 2 - 2 * (Real.sqrt a * Real.sqrt b) := by
      field_simp; ring
    rw [he, hsa, hsb, ← hab]; unfold isotonicRational; ring
  nlinarith [sq_nonneg (Real.sqrt a * ζ - Real.sqrt b / ζ), hexp]

/-- **The Liénard isotonic potential is the rational isotonic potential** `isotonicU ω k y =
isotonicRational (ω²) (96/k) y` — identifying `a = ω²`, `b = 96/k`. -/
theorem isotonicU_eq_isotonicRational (ω k y : ℝ) :
    isotonicU ω k y = isotonicRational (ω ^ 2) (96 / k) y := by
  unfold isotonicU isotonicRational; ring

/-- **The Liénard isotonic potential is bounded below** `isotonicU ω k y ≥ 2√(96 ω²/k)` — its minimum, connecting
`LienardMomentumDependentMass.isotonicU` to the AM–GM bound. -/
theorem isotonicU_ge (ω k y : ℝ) (hω : ω ≠ 0) (hk : 0 < k) (hy : y ≠ 0) :
    2 * Real.sqrt (ω ^ 2 * (96 / k)) ≤ isotonicU ω k y := by
  rw [isotonicU_eq_isotonicRational]
  exact isotonicRational_ge (ω ^ 2) (96 / k) y (by positivity) (by positivity) hy

/-! ## §B — symmetrization to the harmonic oscillator -/

/-- The **standard isotonic potential** `U(x) = (k/2)((x+1) − 1/(x+1))²` (Eq. 3.4). -/
noncomputable def stdIsotonicU (k x : ℝ) : ℝ := (k / 2) * ((x + 1) - 1 / (x + 1)) ^ 2

/-- The **Mañosas–Torres variable** `h(x) = ½((x+1) − 1/(x+1))` (Eq. 3.4). -/
noncomputable def stdIsotonicH (x : ℝ) : ℝ := (1 / 2) * ((x + 1) - 1 / (x + 1))

/-- **`U = 2k·h²`** — the standard isotonic potential in terms of the symmetrization variable, the form
`Ũ(h) = 2kh²` that the symmetric potential `Ũ(ξ) = 2kξ²` must reproduce. -/
theorem stdIsotonicU_eq (k x : ℝ) : stdIsotonicU k x = 2 * k * (stdIsotonicH x) ^ 2 := by
  unfold stdIsotonicU stdIsotonicH; ring

/-- The **symmetric potential** `Ũ(ξ) = 2kξ²`, and **`symmIsotonicU_quarter`** its reduction to the linear
harmonic oscillator `ξ²/2` at `k = 1/4` (Eq. 3.6) — the reason the isotonic oscillator is **isochronous** (period
`2π`, amplitude-independent, like the LHO). -/
noncomputable def symmIsotonicU (k ξ : ℝ) : ℝ := 2 * k * ξ ^ 2

theorem symmIsotonicU_quarter (ξ : ℝ) : symmIsotonicU (1 / 4) ξ = ξ ^ 2 / 2 := by
  unfold symmIsotonicU; ring

/-- **The isotonic equation of motion** `U'(x) = k(x+1) − k/(x+1)³` (Eq. 3.5) — the gradient of `stdIsotonicU`
(via the chain rule `U' = k(w − 1/w)(1 + 1/w²)`, `w = x+1`) is the isotonic force `−ẍ = k(x+1) − k/(x+1)³`. -/
theorem stdIsotonic_force (k x : ℝ) (hx : x + 1 ≠ 0) :
    k * ((x + 1) - 1 / (x + 1)) * (1 + 1 / (x + 1) ^ 2) = k * (x + 1) - k / (x + 1) ^ 3 := by
  field_simp; ring

/-! ## §C — the period Beta–Gamma identity -/

/-- The **Beta function** `B(u,v) = Γ(u)Γ(v)/Γ(u+v)` (Eq. 2.7 closed form). -/
noncomputable def betaFn (u v : ℝ) : ℝ := Real.Gamma u * Real.Gamma v / Real.Gamma (u + v)

/-- **The period Beta–Gamma identity** `B(1/(α+1), 1/2) = √π Γ(1/(α+1))/Γ((α+3)/(2(α+1)))` (Eq. 2.8) — using
`Γ(1/2) = √π` and `1/(α+1) + 1/2 = (α+3)/(2(α+1))`. -/
theorem betaFn_half (α : ℝ) (hα : α + 1 ≠ 0) :
    betaFn (1 / (α + 1)) (1 / 2)
      = Real.sqrt π * Real.Gamma (1 / (α + 1)) / Real.Gamma ((α + 3) / (2 * (α + 1))) := by
  unfold betaFn
  rw [Real.Gamma_one_half_eq,
    show (1 / (α + 1)) + (1 / 2) = (α + 3) / (2 * (α + 1)) from by field_simp; ring]
  ring

/-- The **generalized-oscillator period** `T(c,α,q₀) = √(8π/(c²(α+1))) · Γ(1/(α+1))/Γ((α+3)/(2(α+1))) ·
|q₀|^{(1−α)/2}` (Eq. 2.8). -/
noncomputable def periodU (c α q₀ : ℝ) : ℝ :=
  Real.sqrt (8 * π / (c ^ 2 * (α + 1))) *
    (Real.Gamma (1 / (α + 1)) / Real.Gamma ((α + 3) / (2 * (α + 1)))) * |q₀| ^ ((1 - α) / 2)

/-- **The period reduces to the harmonic `2π/c` at `α = 1`** — the amplitude dependence `|q₀|^{(1−α)/2}`
disappears and `Γ(1/2)/Γ(1) = √π`, giving the amplitude-independent linear-harmonic period. -/
theorem periodU_at_one (c q₀ : ℝ) (hc : 0 < c) : periodU c 1 q₀ = 2 * π / c := by
  unfold periodU
  rw [show (1 : ℝ) / (1 + 1) = 1 / 2 from by norm_num,
    show ((1 : ℝ) + 3) / (2 * (1 + 1)) = 1 from by norm_num,
    show ((1 : ℝ) - 1) / 2 = 0 from by norm_num,
    Real.Gamma_one_half_eq, Real.Gamma_one, Real.rpow_zero, div_one, mul_one,
    show 8 * π / (c ^ 2 * (1 + 1)) = 4 * π / c ^ 2 from by ring,
    ← Real.sqrt_mul (by positivity),
    show 4 * π / c ^ 2 * π = (2 * π / c) ^ 2 from by field_simp; ring,
    Real.sqrt_sq (by positivity)]

/-! ## §D — the generalized isotonic potential symmetry -/

/-- **The hyperbolic identity** `(√(ξ²+1) + ξ)(√(ξ²+1) − ξ) = 1` — with `ξ = sinh θ`, `√(ξ²+1) = cosh θ`, this is
`(cosh + sinh)(cosh − sinh) = 1`; it makes `√(ξ²+1) − ξ` the reciprocal of `√(ξ²+1) + ξ`. -/
theorem sqrt_sq_add_one_mul_sub (ξ : ℝ) :
    (Real.sqrt (ξ ^ 2 + 1) + ξ) * (Real.sqrt (ξ ^ 2 + 1) - ξ) = 1 := by
  have h : Real.sqrt (ξ ^ 2 + 1) ^ 2 = ξ ^ 2 + 1 := Real.sq_sqrt (by positivity)
  nlinarith [h]

/-- **`√(ξ²+1) + ξ` is positive.** -/
theorem sqrt_sq_add_one_add_pos (ξ : ℝ) : 0 < Real.sqrt (ξ ^ 2 + 1) + ξ := by
  have h1 : |ξ| < Real.sqrt (ξ ^ 2 + 1) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  linarith [h1, neg_abs_le ξ]

/-- The **generalized isotonic potential** `Ũ(ξ) = (c/8)((√(ξ²+1)+ξ)^{(α+1)/2} − (√(ξ²+1)+ξ)^{−(α+1)/2})²`
(Eq. 4.3). -/
noncomputable def genIsotonicU (c α ξ : ℝ) : ℝ :=
  c / 8 * ((Real.sqrt (ξ ^ 2 + 1) + ξ) ^ ((α + 1) / 2)
    - (Real.sqrt (ξ ^ 2 + 1) + ξ) ^ (-((α + 1) / 2))) ^ 2

/-- **The generalized isotonic potential is even** `Ũ(−ξ) = Ũ(ξ)` (Eq. 4.3) — under `ξ → −ξ` the base
`√(ξ²+1) + ξ` inverts (hyperbolic identity), swapping the two rpow terms, and the square is invariant. This is the
symmetry the Mañosas–Torres period argument requires. -/
theorem genIsotonicU_symm (c α ξ : ℝ) : genIsotonicU c α (-ξ) = genIsotonicU c α ξ := by
  have hpos : 0 < Real.sqrt (ξ ^ 2 + 1) + ξ := sqrt_sq_add_one_add_pos ξ
  have hsq : Real.sqrt ((-ξ) ^ 2 + 1) = Real.sqrt (ξ ^ 2 + 1) := by rw [neg_pow]; ring_nf
  have hinv : Real.sqrt (ξ ^ 2 + 1) + (-ξ) = (Real.sqrt (ξ ^ 2 + 1) + ξ)⁻¹ := by
    rw [inv_eq_one_div, eq_div_iff (ne_of_gt hpos)]
    linear_combination sqrt_sq_add_one_mul_sub ξ
  unfold genIsotonicU
  rw [hsq, hinv, Real.inv_rpow hpos.le, Real.inv_rpow hpos.le,
    ← Real.rpow_neg hpos.le, ← Real.rpow_neg hpos.le, neg_neg]
  ring

/-! ## §E — the reduced equation of motion (Theorem 1.1) -/

/-- **The isotonic force identity** `(q^β − q^{−β})(q^{β−1} + q^{−β−1}) = q^α − q^{−(α+2)}` with `β = (α+1)/2` — the
product appearing in the gradient of the generalized isotonic potential `U(q) = (c_α/8)(q^β − q^{−β})²` collapses to
two power terms (`q > 0`), the cross terms `q^{−1}` cancelling. -/
theorem genIsotonic_force_identity (α q : ℝ) (hq : 0 < q) :
    (q ^ ((α + 1) / 2) - q ^ (-((α + 1) / 2))) * (q ^ ((α + 1) / 2 - 1) + q ^ (-((α + 1) / 2) - 1))
      = q ^ α - q ^ (-(α + 2)) := by
  have e1 : (α + 1) / 2 + ((α + 1) / 2 - 1) = α := by ring
  have e2 : (α + 1) / 2 + (-((α + 1) / 2) - 1) = -1 := by ring
  have e3 : -((α + 1) / 2) + ((α + 1) / 2 - 1) = -1 := by ring
  have e4 : -((α + 1) / 2) + (-((α + 1) / 2) - 1) = -(α + 2) := by ring
  rw [mul_add, sub_mul, sub_mul, ← Real.rpow_add hq, ← Real.rpow_add hq, ← Real.rpow_add hq,
    ← Real.rpow_add hq, e1, e2, e3, e4]
  ring

/-- **The reduced coefficient** `c_α·(α+1)/8 = 1` at `c_α = 8/(α+1)` — the normalization making the equation of
motion coefficient-free. -/
theorem genIsotonic_reduced_coefficient (α : ℝ) (hα : α + 1 ≠ 0) :
    8 / (α + 1) * (α + 1) / 8 = 1 := by field_simp

/-- **The reduced equation of motion (Theorem 1.1)** `q̈ + q^α = 1/q^{α+2}` — with `c_α = 8/(α+1)`, the potential
gradient `U'(q) = (c_α(α+1)/8)(q^β − q^{−β})(q^{β−1} + q^{−β−1})` reduces to `q^α − q^{−(α+2)}`, so
`q̈ = −U'(q) = −q^α + q^{−(α+2)}`, i.e. `q̈ + q^α = 1/q^{α+2}` (`q > 0`) — the generalized isotonic system in the
succinct form of Theorem 1.1. -/
theorem genIsotonic_reduced_force (α q : ℝ) (hq : 0 < q) (hα : α + 1 ≠ 0) :
    8 / (α + 1) * (α + 1) / 8 *
        ((q ^ ((α + 1) / 2) - q ^ (-((α + 1) / 2))) *
          (q ^ ((α + 1) / 2 - 1) + q ^ (-((α + 1) / 2) - 1)))
      = q ^ α - q ^ (-(α + 2)) := by
  rw [genIsotonic_reduced_coefficient α hα, one_mul, genIsotonic_force_identity α q hq]

/-! ## §F — the amplitude-dependent frequency -/

/-- The **amplitude-dependent frequency** `ω_ca = |A|^{(α−1)/2} √(c_α²(α+1)/2)` of the purely nonlinear oscillator
`ẍ + c_α² sgn(x)|x|^α = 0` (page 3) — the frequency depends on the amplitude `A` unless `α = 1`. -/
noncomputable def frequencyCa (cα α A : ℝ) : ℝ := |A| ^ ((α - 1) / 2) * Real.sqrt (cα ^ 2 * (α + 1) / 2)

/-- **The frequency is amplitude-independent at `α = 1`** `ω_ca = c_α` — the linear-harmonic limit: the amplitude
factor `|A|^{(α−1)/2}` becomes `|A|^0 = 1` and `√(c_α²) = c_α`, so the oscillator is isochronous exactly at
`α = 1`. -/
theorem frequencyCa_at_one (cα A : ℝ) (hcα : 0 ≤ cα) : frequencyCa cα 1 A = cα := by
  unfold frequencyCa
  rw [show ((1 : ℝ) - 1) / 2 = 0 from by norm_num, Real.rpow_zero, one_mul,
    show cα ^ 2 * (1 + 1) / 2 = cα ^ 2 from by ring, Real.sqrt_sq hcα]

end Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
