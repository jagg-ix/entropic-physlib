/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
public import Physlib.Relativity.MinkowskiMatrix
meta import Zil

/-!
# The Einstein equation as an equation of state (Jacobson)

Jacobson's *Thermodynamics of Spacetime* (Phys. Rev. Lett. 75 (1995) 1260) derives the Einstein
field equation from the Clausius relation `δQ = T δS` applied to **every** local Rindler horizon,
with `S = A/4G` (area–entropy) and `T = ℏκ/2π` (Unruh).  Feeding the horizon area variation
(Raychaudhuri) and the matter heat flux into Clausius, and demanding it hold for **all** null
directions `k` through a point, yields the null-contracted "equation of state"

`R_{ab} kᵃkᵇ = κ T_{ab} kᵃkᵇ`   for all null `k`   (`κ = 8πG/c⁴`).

The purely mathematical step that turns this *per-null-direction* relation into the *tensor* Einstein
equation is a **null-cone polarization** fact: a symmetric tensor whose contraction vanishes on every
null vector is a scalar multiple of the metric.  That step is what makes the Einstein equation the
**output** of the thermodynamic equation of state rather than an assumed premise.

* `nullVanishing_eq_smul_metric` — the forward null-cone polarization lemma: a symmetric matrix `A`
  with `k ⬝ (A k) = 0` on every Minkowski-null `k` equals `A₀₀ • η`.
* `equationOfState_ricci_decomposition` — the null-contracted equation of state forces
  `Ric = κ • T + f • η` for a scalar `f = (Ric − κT)₀₀`.
* `einstein_equation_of_state` — **the Einstein field equation with cosmological term
  `G_{ab} + Λ g_{ab} = κ T_{ab}` is the output** of the equation of state, with
  `Λ = (κ·tr_η T + f·(d−1))/2`.

Reuses the existing Minkowski metric `minkowskiMatrix` (`Physlib.Relativity.MinkowskiMatrix`) and
Einstein tensor `einsteinTensor` (`EinsteinFieldEquationsPhysLean`).

Honest scope: this formalizes the **algebraic heart** of Jacobson's argument — the polarization step
and the trace-reversal assembly — taking the null-contracted equation of state as the labeled
thermodynamic input (the Clausius/Unruh/area–entropy/Raychaudhuri heat-flux computation that
produces it is standard GR, carried elsewhere in the repo as `FutureRegularNullRaychaudhuri`,
`ScreenThermodynamics.screen_first_law`, `unruhTemperature`, and is not re-derived here).  The value
of `Λ` is fixed pointwise; its **constancy** across spacetime is the content of the contracted
Bianchi identity together with local conservation `∇ᵃT_{ab}=0` (the converse direction is
`bianchi_implies_conservation`), which is not re-derived pointwise here.  The polarization lemma is a
Matrix-world, forward-only companion to the `Vector 3` continuous-bilinear `same_null_cone_proportional`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState

open Matrix minkowskiMatrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

variable {d : ℕ}

/-- The `A`-bilinear pairing `⟨x, y⟩_A = x ⬝ (A *ᵥ y)`. -/
private def pr (A : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x y : (Fin 1 ⊕ Fin d) → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ y)

private lemma pr_single (A : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (μ ν : Fin 1 ⊕ Fin d) : pr A (Pi.single μ 1) (Pi.single ν 1) = A μ ν := by
  unfold pr
  rw [single_dotProduct, one_mul]
  change (A μ) ⬝ᵥ (Pi.single ν (1 : ℝ)) = A μ ν
  rw [dotProduct_single, mul_one]

private lemma pr_add_left (A : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x x' y : (Fin 1 ⊕ Fin d) → ℝ) : pr A (x + x') y = pr A x y + pr A x' y := by
  unfold pr; rw [add_dotProduct]

private lemma pr_add_right (A : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (x y y' : (Fin 1 ⊕ Fin d) → ℝ) : pr A x (y + y') = pr A x y + pr A x y' := by
  unfold pr; rw [mulVec_add, dotProduct_add]

private lemma pr_smul_left (A : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (a : ℝ) (x y : (Fin 1 ⊕ Fin d) → ℝ) : pr A (a • x) y = a * pr A x y := by
  unfold pr; rw [smul_dotProduct, smul_eq_mul]

private lemma pr_smul_right (A : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (a : ℝ) (x y : (Fin 1 ⊕ Fin d) → ℝ) : pr A x (a • y) = a * pr A x y := by
  unfold pr; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- **The forward null-cone polarization lemma.**  A symmetric real matrix on `(1+d)`-dimensional
Minkowski space whose quadratic form `k ⬝ (A *ᵥ k)` vanishes on **every** null vector `k`
(`k ⬝ (η *ᵥ k) = 0`) is a scalar multiple of the Minkowski metric: `A = A₀₀ • η`.  (Only the
forward implication "null ⟹ vanishes" is used — this is the physically needed direction, the
equation of state holding *on* the null cone.) -/
@[zil_level structural]
theorem nullVanishing_eq_smul_metric (A : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (hA : A.IsSymm)
    (h : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 → k ⬝ᵥ (A *ᵥ k) = 0) :
    A = A (Sum.inl 0) (Sum.inl 0) • η := by
  have symmA : ∀ p q, A p q = A q p := fun p q => by
    conv_lhs => rw [← hA.eq]
    rfl
  -- Time–space and space diagonal: A₀ⱼ = 0 and Aⱼⱼ = −A₀₀.
  have hL12 : ∀ j : Fin d, A (Sum.inl 0) (Sum.inr j) = 0
      ∧ A (Sum.inr j) (Sum.inr j) = -A (Sum.inl 0) (Sum.inl 0) := by
    intro j
    have hn1 : (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr j) 1) ⬝ᵥ
        (η *ᵥ (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr j) 1)) = 0 := by
      change pr η (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr j) 1)
        (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr j) 1) = 0
      simp only [pr_add_left, pr_add_right, pr_single]
      simp
    have hn2 : (Pi.single (Sum.inl 0) 1 + (-1 : ℝ) • Pi.single (Sum.inr j) 1) ⬝ᵥ
        (η *ᵥ (Pi.single (Sum.inl 0) 1 + (-1 : ℝ) • Pi.single (Sum.inr j) 1)) = 0 := by
      change pr η (Pi.single (Sum.inl 0) 1 + (-1 : ℝ) • Pi.single (Sum.inr j) 1)
        (Pi.single (Sum.inl 0) 1 + (-1 : ℝ) • Pi.single (Sum.inr j) 1) = 0
      simp only [pr_add_left, pr_add_right, pr_smul_left, pr_smul_right, pr_single]
      simp
    have e1 : pr A (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr j) 1)
        (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr j) 1) = 0 := h _ hn1
    have e2 : pr A (Pi.single (Sum.inl 0) 1 + (-1 : ℝ) • Pi.single (Sum.inr j) 1)
        (Pi.single (Sum.inl 0) 1 + (-1 : ℝ) • Pi.single (Sum.inr j) 1) = 0 := h _ hn2
    simp only [pr_add_left, pr_add_right, pr_smul_left, pr_smul_right, pr_single] at e1 e2
    rw [symmA (Sum.inr j) (Sum.inl 0)] at e1 e2
    constructor
    · linarith
    · linarith
  -- Space off-diagonal: Aᵢⱼ = 0 for i ≠ j.
  have hL3 : ∀ i j : Fin d, i ≠ j → A (Sum.inr i) (Sum.inr j) = 0 := by
    intro i j hij
    have hn3 : (Real.sqrt 2 • Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr i) 1
          + Pi.single (Sum.inr j) 1) ⬝ᵥ (η *ᵥ (Real.sqrt 2 • Pi.single (Sum.inl 0) 1
          + Pi.single (Sum.inr i) 1 + Pi.single (Sum.inr j) 1)) = 0 := by
      change pr η (Real.sqrt 2 • Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr i) 1
          + Pi.single (Sum.inr j) 1) (Real.sqrt 2 • Pi.single (Sum.inl 0) 1
          + Pi.single (Sum.inr i) 1 + Pi.single (Sum.inr j) 1) = 0
      simp only [pr_add_left, pr_add_right, pr_smul_left, pr_smul_right, pr_single]
      have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      simp [hij, hij.symm, hsq]
      norm_num
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have e3 : pr A (Real.sqrt 2 • Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr i) 1
        + Pi.single (Sum.inr j) 1) (Real.sqrt 2 • Pi.single (Sum.inl 0) 1
        + Pi.single (Sum.inr i) 1 + Pi.single (Sum.inr j) 1) = 0 := h _ hn3
    simp only [pr_add_left, pr_add_right, pr_smul_left, pr_smul_right, pr_single] at e3
    rw [(hL12 i).1, (hL12 j).1, (hL12 i).2, (hL12 j).2] at e3
    rw [symmA (Sum.inr i) (Sum.inl 0), symmA (Sum.inr j) (Sum.inl 0),
      symmA (Sum.inr j) (Sum.inr i)] at e3
    rw [(hL12 i).1, (hL12 j).1] at e3
    simp only [mul_zero, add_zero, zero_add] at e3
    rw [← mul_assoc, h2] at e3
    linarith
  -- Assemble.
  ext p q
  rw [Matrix.smul_apply, smul_eq_mul]
  rcases p with p0 | i <;> rcases q with q0 | j
  · obtain rfl : p0 = 0 := Subsingleton.elim p0 0
    obtain rfl : q0 = 0 := Subsingleton.elim q0 0
    simp
  · obtain rfl : p0 = 0 := Subsingleton.elim p0 0
    rw [(hL12 j).1, minkowskiMatrix.off_diag_zero (by simp), mul_zero]
  · obtain rfl : q0 = 0 := Subsingleton.elim q0 0
    rw [symmA (Sum.inr i) (Sum.inl 0), (hL12 i).1,
      minkowskiMatrix.off_diag_zero (by simp), mul_zero]
  · by_cases hij : i = j
    · subst hij
      rw [(hL12 i).2, minkowskiMatrix.inr_i_inr_i]; ring
    · rw [hL3 i j hij, minkowskiMatrix.off_diag_zero (by simp [hij]), mul_zero]

/-- **The null-contracted equation of state forces `Ric = κ • T + f • η`.**  If the Ricci and
stress tensors are symmetric and their contractions agree on every null vector,
`R_{ab} kᵃkᵇ = κ T_{ab} kᵃkᵇ`, then `Ric` and `κ T` differ by a multiple of the metric — the scalar
`f = (Ric − κ • T)₀₀`. -/
@[zil_level bridge_theorem]
theorem equationOfState_ricci_decomposition
    (Ric T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (κ : ℝ)
    (hRic : Ric.IsSymm) (hT : T.IsSymm)
    (hEoS : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 →
      k ⬝ᵥ (Ric *ᵥ k) = κ * (k ⬝ᵥ (T *ᵥ k))) :
    Ric = κ • T + ((Ric - κ • T) (Sum.inl 0) (Sum.inl 0)) • η := by
  have hB : (Ric - κ • T).IsSymm := hRic.sub (hT.smul κ)
  have hvan : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 →
      k ⬝ᵥ ((Ric - κ • T) *ᵥ k) = 0 := by
    intro k hk
    rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hEoS k hk,
      sub_self]
  have hpol := nullVanishing_eq_smul_metric (Ric - κ • T) hB hvan
  rw [← hpol]; abel

/-- **The Einstein field equation is the output of the equation of state.**  Given the null-contracted
Clausius equation of state `R_{ab} kᵃkᵇ = κ T_{ab} kᵃkᵇ` for all null `k`, the Einstein field
equation with cosmological term holds,

`G_{ab} + Λ g_{ab} = κ T_{ab}`,   `g = η`,   `Λ = (κ·tr_η T + f·(d−1))/2`,   `f = (Ric − κT)₀₀`.

This is Jacobson's *Einstein equation of state*: the field equation is **derived**, not assumed.  The
value of `Λ` is fixed pointwise by the trace part; its spacetime constancy is the contracted-Bianchi
content (see the module header). -/
@[zil_level bridge_theorem]
theorem einstein_equation_of_state
    (Ric T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (κ : ℝ)
    (hRic : Ric.IsSymm) (hT : T.IsSymm)
    (hEoS : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 →
      k ⬝ᵥ (Ric *ᵥ k) = κ * (k ⬝ᵥ (T *ᵥ k))) :
    einsteinFieldEquationCosmological Ric (Matrix.trace (η * Ric)) η T
      ((κ * Matrix.trace (η * T)
        + ((Ric - κ • T) (Sum.inl 0) (Sum.inl 0)) * ((d : ℝ) - 1)) / 2) κ := by
  set f : ℝ := (Ric - κ • T) (Sum.inl 0) (Sum.inl 0) with hf
  have hdec : Ric = κ • T + f • η := equationOfState_ricci_decomposition Ric T κ hRic hT hEoS
  have htr : Matrix.trace (η * Ric) = κ * Matrix.trace (η * T) + f * (1 + (d : ℝ)) := by
    rw [hdec, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_smul, minkowskiMatrix.sq, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    push_cast [Fintype.card_sum, Fintype.card_fin]
    ring
  unfold einsteinFieldEquationCosmological einsteinTensor
  rw [htr, hdec]
  module

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState

zil attach nullVanishing_eq_smul_metric where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:a-symmetric-tensor-whose-quadratic-form-vanishes-on-every-minkowski-null-vector-is-a-scalar-multiple-of-the-metric-the-forward-null-cone-polarization-lemma"

zil attach equationOfState_ricci_decomposition where
  formalizes @ "claim:the-null-contracted-clausius-equation-of-state-ricci-contraction-equals-kappa-times-stress-contraction-on-all-null-vectors-forces-the-ricci-tensor-to-equal-kappa-times-the-stress-tensor-plus-a-scalar-multiple-of-the-metric",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.nullVanishing_eq_smul_metric"

zil attach einstein_equation_of_state where
  formalizes @ "claim:jacobsons-einstein-equation-of-state-the-einstein-field-equation-with-cosmological-term-is-the-derived-output-of-the-thermodynamic-null-contracted-clausius-equation-of-state-not-an-assumed-premise",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.equationOfState_ricci_decomposition",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinTensor"

zil_file_contract physlib.einsteinEquationOfState where
  promises "Jacobson's derivation of the Einstein field equation as an equation of state. The mathematical heart is the forward null-cone polarization lemma: a symmetric tensor whose quadratic form vanishes on every Minkowski null vector is a scalar multiple of the metric. The null-contracted Clausius equation of state, Ricci contraction equals kappa times stress contraction on all null vectors, therefore forces the Ricci tensor to equal kappa times the stress tensor plus a scalar multiple of the metric, and the trace-reversal assembles this into the Einstein field equation with cosmological term G plus Lambda g equals kappa T. The Einstein equation is thus the derived output of the thermodynamic equation of state, not an assumed premise. Honest scope: this formalizes the algebraic heart, taking the null-contracted equation of state as the labeled thermodynamic input produced by the standard Clausius, Unruh temperature, area-entropy, and Raychaudhuri heat-flux computation carried elsewhere in the repo; and the cosmological constant is fixed pointwise, its spacetime constancy being the separate contracted-Bianchi content."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:minkowskiMatrix",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinTensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquationCosmological"
  ]
  forbids_substitutes [
    "reading the equation-of-state derivation as also deriving the Clausius/Raychaudhuri heat-flux input or the spacetime constancy of the cosmological constant, both of which are labeled inputs here"
  ]
  witnessed_by [
    nullVanishing_eq_smul_metric,
    equationOfState_ricci_decomposition,
    einstein_equation_of_state
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.einsteinEquationOfState
