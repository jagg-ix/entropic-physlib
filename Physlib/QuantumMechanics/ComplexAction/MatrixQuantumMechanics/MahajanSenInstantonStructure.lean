/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Difference operator, instanton sum, genus-0 string equation, and double sine-Liouville (AMS §2.3–§4)

The exact (Toda) solution and the instanton corrections of sine-Liouville theory (Alexandrov, Mahajan, Sen,
arXiv:2311.04969, §2.3–§4) are organized by a finite-difference operator acting on the free energy and by
algebraic "string equations" determining the genus-0 data. This continues
`[[project_alexandrov_mahajan_sen_instantons]]`.

* **§A — the free-energy difference operator** (Eq. 2.18). `sinDiff R F = (1/i)(F(μ+i/2R) − F(μ−i/2R))` is the
  finite-difference realization of `2 sin(∂_μ/2R)`; on exponentials it acts as multiplication by the symbol:
  `sinDiff R (e^{a·}) = 2 sin(a/2R) e^{aμ}` (`sinDiff_exp`).
* **§B — instanton eigenvalues** (Eqs. 2.27). On the D-instanton tower `e^{−2πnμ}` the operator gives the
  factor `−2 sin(πn/R)` (`sinDiff_dInstanton`) — the `sin(πn/R)` of the non-perturbative free energy.
* **§C — the genus-0 string equation** (Eqs. 3.11, 4.4). `slStringEquation_relation`: the string equation
  `e^X − (k/R)²(1−k/R)λ²e^{(2−k/R)X} = 1` is equivalent to `e^X = 1 + (1−k/R)a_k²` with
  `a_k = (k/R)λ e^{(1−k/2R)X}`.
* **§D — double sine-Liouville** (Eqs. 4.20, 4.21). `dslPhaseEquation_eq_zero_iff`: the dSL phase equation
  factorizes, `sin(kζ)·[…] = 0 ⟺ sin(kζ)=0 ∨ […]=0`, giving **two** sets of double points (two instanton
  types); `dslFirstSet` gives the first set `ζ_m = πm/k`.

## References

* S. Alexandrov, R. Mahajan, A. Sen, *Instantons in sine-Liouville theory*, arXiv:2311.04969, §2.3–§4,
  Eqs. (2.18), (2.27), (3.11), (4.4), (4.13), (4.20), (4.21).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MahajanSenInstantonStructure

/-! ## §A — the free-energy difference operator (Eq. 2.18) -/

/-- **[`(e^{zi} − e^{−zi})/i = 2 sin z`]** the exponential form of the sine, from `Complex.two_sin`. -/
theorem twoSin_diff (z : ℂ) :
    (Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I)) / Complex.I = 2 * Complex.sin z := by
  rw [Complex.two_sin, div_eq_iff Complex.I_ne_zero, mul_assoc, Complex.I_mul_I]
  ring

/-- **The free-energy difference operator** `2 sin(∂_μ/2R)`, realized as the finite difference
`(1/i)(F(μ + i/2R) − F(μ − i/2R))` (Eq. 2.18). -/
noncomputable def sinDiff (R : ℝ) (F : ℂ → ℂ) (μ : ℂ) : ℂ :=
  (F (μ + Complex.I / (2 * (R : ℂ))) - F (μ - Complex.I / (2 * (R : ℂ)))) / Complex.I

/-- **[The difference operator on exponentials, Eq. 2.18]** `2 sin(∂_μ/2R) e^{aμ} = 2 sin(a/2R) e^{aμ}`: the
finite-difference operator acts on an exponential as multiplication by the symbol `2 sin(a/2R)`, justifying its
interpretation as `2 sin(∂_μ/2R)`. -/
theorem sinDiff_exp (R : ℝ) (a μ : ℂ) :
    sinDiff R (fun ν => Complex.exp (a * ν)) μ
      = 2 * Complex.sin (a / (2 * (R : ℂ))) * Complex.exp (a * μ) := by
  show (Complex.exp (a * (μ + Complex.I / (2 * (R : ℂ))))
      - Complex.exp (a * (μ - Complex.I / (2 * (R : ℂ))))) / Complex.I = _
  rw [show a * (μ + Complex.I / (2 * (R : ℂ))) = a * μ + (a / (2 * (R : ℂ))) * Complex.I from by ring,
    show a * (μ - Complex.I / (2 * (R : ℂ))) = a * μ + (-(a / (2 * (R : ℂ)))) * Complex.I from by ring,
    Complex.exp_add, Complex.exp_add, ← mul_sub, mul_div_assoc,
    twoSin_diff (a / (2 * (R : ℂ)))]
  ring

/-! ## §B — instanton eigenvalues (Eq. 2.27) -/

/-- **[D-instanton eigenvalue, Eq. 2.27]** `2 sin(∂_μ/2R) e^{−2πnμ} = −2 sin(πn/R) e^{−2πnμ}` — the
difference operator turns the D-instanton exponential `e^{−2πnμ}` into the `sin(πn/R)` factor appearing in the
non-perturbative free energy. -/
theorem sinDiff_dInstanton (R : ℝ) (n : ℕ) (μ : ℂ) :
    sinDiff R (fun ν => Complex.exp ((-(2 * Real.pi * n) : ℝ) * ν)) μ
      = -2 * Complex.sin ((Real.pi * n / R : ℝ)) * Complex.exp ((-(2 * Real.pi * n) : ℝ) * μ) := by
  rw [sinDiff_exp R ((-(2 * Real.pi * n) : ℝ) : ℂ) μ,
    show ((-(2 * Real.pi * n) : ℝ) : ℂ) / (2 * (R : ℂ)) = -((Real.pi * n / R : ℝ) : ℂ) from by
      push_cast; ring,
    Complex.sin_neg]
  ring

/-! ## §C — the genus-0 string equation (Eqs. 3.11, 4.4) -/

/-- **The genus-0 coefficient** `a_k = (k/R) λ e^{(1−k/2R)X}` (Eq. 3.11). -/
noncomputable def slAk (k R lam X : ℝ) : ℝ := (k / R) * lam * Real.exp ((1 - k / (2 * R)) * X)

/-- **[Genus-0 string equation, Eqs. 3.11 → 4.4]** the string equation
`e^X − (k/R)²(1−k/R)λ²e^{(2−k/R)X} = 1` is the relation `e^X = 1 + (1−k/R)a_k²` — the single-coupling case of
the general string equation `e^X = 1 + Σ_l (1−l/R)a_l²` (Eq. 4.4). -/
theorem slStringEquation_relation (k R lam X : ℝ)
    (hstr : Real.exp X - (k / R) ^ 2 * (1 - k / R) * lam ^ 2 * Real.exp ((2 - k / R) * X) = 1) :
    Real.exp X = 1 + (1 - k / R) * (slAk k R lam X) ^ 2 := by
  have hsq : (slAk k R lam X) ^ 2 = (k / R) ^ 2 * lam ^ 2 * Real.exp ((2 - k / R) * X) := by
    unfold slAk
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * ((1 - k / (2 * R)) * X) = (2 - k / R) * X from by push_cast; ring]
  rw [hsq]
  linear_combination hstr

/-! ## §D — double sine-Liouville (Eqs. 4.20, 4.21) -/

/-- **The double sine-Liouville phase equation** `sin(kζ)·[a_k sin((k−R)/R θ) + 2a_{2k} cos(kζ) sin((2k−R)/R θ)]`
(Eq. 4.21). -/
noncomputable def dslPhaseEquation (k R ak a2k ζ θ : ℝ) : ℝ :=
  Real.sin (k * ζ)
    * (ak * Real.sin ((k - R) / R * θ) + 2 * a2k * Real.cos (k * ζ) * Real.sin ((2 * k - R) / R * θ))

/-- **[Two sets of double points, Eq. 4.21]** the dSL phase equation **factorizes**: it vanishes iff
`sin(kζ) = 0` (the first set, Eq. 4.13) **or** the bracket vanishes (the second set, Eq. 4.29). Hence double
sine-Liouville has two distinct types of instanton effects. -/
theorem dslPhaseEquation_eq_zero_iff (k R ak a2k ζ θ : ℝ) :
    dslPhaseEquation k R ak a2k ζ θ = 0
      ↔ Real.sin (k * ζ) = 0
        ∨ ak * Real.sin ((k - R) / R * θ) + 2 * a2k * Real.cos (k * ζ) * Real.sin ((2 * k - R) / R * θ)
            = 0 :=
  mul_eq_zero

/-- **[First set of double points, Eq. 4.13]** `ζ_m = πm/k` solves `sin(kζ) = 0`. -/
theorem dslFirstSet (k : ℝ) (hk : k ≠ 0) (m : ℕ) : Real.sin (k * (Real.pi * m / k)) = 0 := by
  rw [show k * (Real.pi * (m : ℝ) / k) = (m : ℝ) * Real.pi from by field_simp]
  exact Real.sin_nat_mul_pi m

/-! ## §E — critical behavior and pure 2D gravity (Appendix C) -/

/-- **The left-hand side of the genus-0 string equation** `e^X − (k/R)²(1−k/R)λ²e^{(2−k/R)X}` (Eq. 3.11); the
string equation is `slLHS = 1`. -/
noncomputable def slLHS (k R lam X : ℝ) : ℝ :=
  Real.exp X - (k / R) ^ 2 * (1 - k / R) * lam ^ 2 * Real.exp ((2 - k / R) * X)

/-- **[Critical point of the string equation, Eq. C.1]** the string-equation LHS reaches its extremum where
`e^{−(1−k/R)X} = (k/R)²(1−k/R)(2−k/R)λ²`. Beyond the corresponding critical coupling the string equation has no
solution: this is the point where the `c = 1` sine-Liouville theory flows to the `c = 0` pure-2d-gravity
critical behavior. -/
theorem slLHS_deriv_eq_zero_iff (k R lam X : ℝ) :
    deriv (fun Y => slLHS k R lam Y) X = 0
      ↔ Real.exp (-(1 - k / R) * X) = (k / R) ^ 2 * (1 - k / R) * (2 - k / R) * lam ^ 2 := by
  have h2 : HasDerivAt (fun Y => Real.exp ((2 - k / R) * Y))
      (Real.exp ((2 - k / R) * X) * (2 - k / R)) X := by
    exact ((Real.hasDerivAt_exp ((2 - k / R) * X)).comp X
      ((hasDerivAt_id X).const_mul (2 - k / R))).congr_deriv (by ring)
  have hd : deriv (fun Y => slLHS k R lam Y) X
      = Real.exp X
        - (k / R) ^ 2 * (1 - k / R) * lam ^ 2 * (Real.exp ((2 - k / R) * X) * (2 - k / R)) :=
    ((Real.hasDerivAt_exp X).sub (h2.const_mul ((k / R) ^ 2 * (1 - k / R) * lam ^ 2))).deriv
  have hexp : Real.exp X = Real.exp (-(1 - k / R) * X) * Real.exp ((2 - k / R) * X) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hd, hexp,
    show Real.exp (-(1 - k / R) * X) * Real.exp ((2 - k / R) * X)
        - (k / R) ^ 2 * (1 - k / R) * lam ^ 2 * (Real.exp ((2 - k / R) * X) * (2 - k / R))
      = Real.exp ((2 - k / R) * X)
        * (Real.exp (-(1 - k / R) * X) - (k / R) ^ 2 * (1 - k / R) * (2 - k / R) * lam ^ 2) from by ring,
    mul_eq_zero, or_iff_right (Real.exp_pos _).ne', sub_eq_zero]

/-! ## §F — sine-Liouville parameter normalization dictionary (Appendix E) -/

/-- **[MQM ↔ string SL-parameter dictionary, Eqs. E.7, E.10]** the worldsheet sine-Liouville coupling `λ̃_k`
relates to the MQM coupling `λ_k` by `λ̃_k = λ_k/π²`: substituting the intermediate normalization
`λ̂_k = (k/R)μλ_k` (Eq. E.7) into `λ̃_k = (R/k)λ̂_k/(π²μ)` (Eq. E.10) the radius `R`, the index `k` and the
cosmological constant `μ` all cancel. -/
theorem slParam_dictionary (k R μ lam : ℝ) (hk : k ≠ 0) (hR : R ≠ 0) (hμ : μ ≠ 0) :
    (R / k) * ((k / R) * μ * lam) / (Real.pi ^ 2 * μ) = lam / Real.pi ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MahajanSenInstantonStructure

end
