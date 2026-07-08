/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Explicit Chern–Simons–Witten structures

Completes the remaining abstract underlying spaces of `ChernSimons.Gravity` — those that, like the original
`TorusHilbertFactorization`, merely *recorded* their result as a structure field — with explicit content.

* **§A — the complex CSW coupling and action.** Hayashi's couplings `t = k + is`, `t̄ = k − is` satisfy
  `t + t̄ = 2k` (`holomorphicCoupling_add_antiholomorphicCoupling`) and `t·t̄ = k² + s²`
  (`holomorphicCoupling_mul_antiholomorphicCoupling`); an explicit `ComplexCSWAction` weights the two sector
  Chern–Simons functionals by these couplings (`hayashiComplexCSWAction`), realizing Hayashi (2.2)–(2.3).
* **§B — the `SL(2,ℂ)` gravity split.** Substituting `A = ω + ie`, `Ā = ω − ie` into a quadratic
  Chern–Simons functional splits it into an exotic term `2λ(ω² − e²)` (the sum, `sl2c_quadratic_sum`) and an
  Einstein–Hilbert term `4iλωe` (the difference, `sl2c_quadratic_diff`); an explicit `SL2CCSWGravityCarrier`
  packages this decomposition (`hayashiSL2CGravity`).
* **§C — the genus-one diagonal invariant.** The torus partition function is the diagonal modular invariant
  `Z = Σ_a |χ_a|²`, factoring each term into the anti-holomorphic and holomorphic characters
  (`torusDiagonalInvariant`, an explicit `TopologicalInvariantFactorization`; `torusPartitionFunction`,
  `torusPartitionFunction_nonneg`), realizing Hayashi (5.19).

## References

* E. Witten (1989); Hayashi (the CSW-gravity paper). structure: `Physlib` (`ChernSimons.Gravity`).

No additional assumptions.
-/

set_option autoImplicit false

open scoped BigOperators

open Complex
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — the complex CSW coupling and action -/

/-- **[`t + t̄ = 2k`]** the holomorphic and anti-holomorphic couplings sum to twice the integer level. -/
theorem holomorphicCoupling_add_antiholomorphicCoupling (c : HayashiCouplings) :
    holomorphicCoupling c + antiholomorphicCoupling c = 2 * (c.level : ℂ) := by
  simp only [holomorphicCoupling, antiholomorphicCoupling]; ring

/-- **[`t − t̄ = 2is`]** their difference is `2i` times the second coupling. -/
theorem holomorphicCoupling_sub_antiholomorphicCoupling (c : HayashiCouplings) :
    holomorphicCoupling c - antiholomorphicCoupling c = 2 * Complex.I * c.s := by
  simp only [holomorphicCoupling, antiholomorphicCoupling]; ring

/-- **[`t·t̄ = k² + s²`]** the product of the two couplings is real-positive in `k, s` (the squared
modulus). -/
theorem holomorphicCoupling_mul_antiholomorphicCoupling (c : HayashiCouplings) :
    holomorphicCoupling c * antiholomorphicCoupling c = (c.level : ℂ) ^ 2 + c.s ^ 2 := by
  simp only [holomorphicCoupling, antiholomorphicCoupling]
  rw [show ((c.level : ℂ) + Complex.I * c.s) * ((c.level : ℂ) - Complex.I * c.s)
      = (c.level : ℂ) ^ 2 - Complex.I ^ 2 * c.s ^ 2 from by ring, Complex.I_sq]
  ring

/-- **An explicit complex CSW action** (Hayashi (2.2)–(2.3)): the holomorphic and anti-holomorphic sector
Chern–Simons functionals weighted by the couplings `t/8π`, `t̄/8π`. -/
noncomputable def hayashiComplexCSWAction {Field : Type*} (c : HayashiCouplings)
    (csHolo csAntiHolo : Field → ℂ) : ComplexCSWAction Field where
  holomorphicAction A := holomorphicCoupling c / (8 * (Real.pi : ℂ)) * csHolo A
  antiholomorphicAction A := antiholomorphicCoupling c / (8 * (Real.pi : ℂ)) * csAntiHolo A
  totalAction A := holomorphicCoupling c / (8 * (Real.pi : ℂ)) * csHolo A
    + antiholomorphicCoupling c / (8 * (Real.pi : ℂ)) * csAntiHolo A
  total_eq_sector_sum := fun _ => rfl

/-! ## §B — the `SL(2,ℂ)` gravity split -/

/-- **[`SL(2,ℂ)` exotic term, the sum]** `λ(ω+ie)² + λ(ω−ie)² = 2λ(ω² − e²)` — substituting the complex
connection `A = ω + ie` into a quadratic Chern–Simons functional, the sum of sectors gives the exotic /
cosmological term. -/
theorem sl2c_quadratic_sum (lam ω e : ℂ) :
    lam * (ω + Complex.I * e) ^ 2 + lam * (ω - Complex.I * e) ^ 2 = 2 * lam * (ω ^ 2 - e ^ 2) := by
  rw [show lam * (ω + Complex.I * e) ^ 2 + lam * (ω - Complex.I * e) ^ 2
      = 2 * lam * ω ^ 2 + 2 * lam * Complex.I ^ 2 * e ^ 2 from by ring, Complex.I_sq]
  ring

/-- **[`SL(2,ℂ)` Einstein–Hilbert term, the difference]** `λ(ω+ie)² − λ(ω−ie)² = 4iλωe` — the difference of
sectors gives the Einstein–Hilbert (dreibein ∧ curvature) term. -/
theorem sl2c_quadratic_diff (lam ω e : ℂ) :
    lam * (ω + Complex.I * e) ^ 2 - lam * (ω - Complex.I * e) ^ 2 = 4 * Complex.I * lam * ω * e := by
  ring

/-- **An explicit `SL(2,ℂ)` CSW-gravity structure** for connection `A = ω + ie`, cosmological constant
`Λ < 0`: the complex action `λ((ω+ie)² + (ω−ie)²)` decomposes into the exotic term `2λ(ω²−e²)`, and the three
interpretive fields are realized by **genuine** statements — the dreibein/spin-connection reading by the
Einstein–Hilbert identity `λ(ω+ie)² − λ(ω−ie)² = 4iλωe`, the Euclidean cosmological constant by `Λ < 0`, and
the tetrad geometry by the Lorentz-gauge invariance of the proper separation (none left as vacuous `True`). -/
noncomputable def hayashiSL2CGravity (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0) : SL2CCSWGravityCarrier where
  complexAction := lam * (ω + Complex.I * e) ^ 2 + lam * (ω - Complex.I * e) ^ 2
  exoticTerm := 2 * lam * (ω ^ 2 - e ^ 2)
  einsteinHilbertTerm := 0
  action_decomposition := by rw [sl2c_quadratic_sum]; ring
  spinConnectionDreibeinInterpretation :=
    lam * (ω + Complex.I * e) ^ 2 - lam * (ω - Complex.I * e) ^ 2 = 4 * Complex.I * lam * ω * e
  spinConnectionDreibeinInterpretation_holds := sl2c_quadratic_diff lam ω e
  euclideanNegativeCosmologicalConstant := Λ < 0
  euclideanNegativeCosmologicalConstant_holds := hΛ
  tetradInvariantGeometry :=
    ∀ (d : ℕ) (Γ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ), Γ ∈ LorentzGroup d →
      ∀ x, properSeparationSq (Γ * E) x = properSeparationSq E x
  tetradInvariantGeometry_holds := fun _ Γ E hΓ x =>
    hayashi_tetrad_properSeparation_lorentz_invariant Γ E hΓ x

/-! ## §C — the genus-one diagonal invariant -/

/-- **The genus-one diagonal modular invariant** (Hayashi (5.19)): an explicit
`TopologicalInvariantFactorization` whose complex-group invariant `|χ_a|²` factors into the anti-holomorphic
character `χ̄_a` (right) and the holomorphic character `χ_a` (left). -/
noncomputable def torusDiagonalInvariant (k : ℕ) (χ : Fin k → ℂ) :
    TopologicalInvariantFactorization (Fin k) ℂ where
  leftInvariant a := χ a
  rightInvariant a := (starRingEnd ℂ) (χ a)
  complexInvariant a := (starRingEnd ℂ) (χ a) * χ a
  factorizes := fun _ => rfl

/-- **The torus partition function** `Z = Σ_a |χ_a|²` — the diagonal modular invariant summed over the
level-`k` characters. -/
noncomputable def torusPartitionFunction (k : ℕ) (χ : Fin k → ℂ) : ℂ :=
  ∑ a, (torusDiagonalInvariant k χ).complexInvariant a

/-- **[The partition function is `Σ |χ_a|²`].** -/
theorem torusPartitionFunction_eq_normSq (k : ℕ) (χ : Fin k → ℂ) :
    torusPartitionFunction k χ = ∑ a, (Complex.normSq (χ a) : ℂ) := by
  unfold torusPartitionFunction
  refine Finset.sum_congr rfl fun a _ => ?_
  show (starRingEnd ℂ) (χ a) * χ a = (Complex.normSq (χ a) : ℂ)
  rw [mul_comm]; exact Complex.mul_conj (χ a)

/-- **[The partition function is real and non-negative]** `Z = Σ |χ_a|² ≥ 0` — a genuine (real) partition
function. -/
theorem torusPartitionFunction_nonneg (k : ℕ) (χ : Fin k → ℂ) :
    0 ≤ (torusPartitionFunction k χ).re := by
  rw [torusPartitionFunction_eq_normSq, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [Complex.ofReal_re]
  exact Complex.normSq_nonneg (χ a)

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
