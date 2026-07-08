/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Data.Complex.Basic

/-!
# Stochel's generalised creation/annihilation operators: the Bargmann–Fock CCR

Formalizes the algebraic core of J. B. Stochel, *Representation of generalised creation and annihilation
operators in Fock space* (Univ. Iagel. Acta Math. **XXXIV**, 1997). On the Bargmann space `B_∞` of
holomorphic functions on `l²`, the **generalised creation and annihilation operators in direction**
`a ∈ l²` are (Eqs. 2.7–2.8)

  `(A_a⁺ f)(z) = ⟨z, a⟩ · f(z)`        (multiplication by the linear field `⟨·, a⟩`),
  `(A_a⁻ f)(z) = d/dλ f(z + λa)|_{λ=0}`  (the directional derivative `∑ᵢ aᵢ ∂ᵢ`).

Their defining commutation relation — the **canonical commutation relation (CCR) of the Fock representation
over a Hilbert space** — is `[A_a⁻, A_b⁺] = ⟨a, b⟩·I`: the commutator of an annihilation and a creation
operator is the *Hilbert inner product of the directions*, a `c`-number. This is the bosonic CCR generalised
from one mode to a whole Hilbert space of directions.

**§A — the abstract CCR.** The relation is a two-line consequence of the Leibniz rule. For any derivation
`D` (an `A_a⁻`) and any element `g` (a creation field `A_b⁺ = g·`) with `D g = c·1` (the directional
derivative of the *linear* field is the constant inner product),

  `D (g · f) − g · D f = c · f`   for all `f`   (`generalised_ccr`),

i.e. `[D, g·] = c·I`.

**§B — the concrete Bargmann–Fock realization.** On `BargmannPoly n = MvPolynomial (Fin n) ℂ` (the
polynomial core of `B_∞`), the creation field `crePoly b = ⟨z, b⟩ = ∑ᵢ b̄ᵢ Xᵢ` and the directional
derivative `ann a = ∑ᵢ aᵢ ∂ᵢ` (built as `mkDerivation`, `Xᵢ ↦ aᵢ`) satisfy

  `ann a (crePoly b) = ⟨a, b⟩·1`   (`ann_crePoly`,  `⟨a,b⟩ = ∑ᵢ b̄ᵢ aᵢ`, the standard ℂⁿ inner product),

so the generalised CCR holds exactly (`generalised_ccr_bargmann`):

  `ann a (crePoly b · f) − crePoly b · ann a f = ⟨a, b⟩ · f`.

This makes the abstract CCR non-vacuous and realizes Stochel's operators concretely. Taking `a = b = eₖ`
recovers the single-mode canonical pair `[∂ₖ, Xₖ·] = 1` (`canonical_ccr`) — the `ν = 0`, single-variable case
already in `Dunkl.Oscillator`/`CollisionOperatorSl2.CollisionModular` ([∂, X·] = 1), here generalised to a Hilbert
space of directions with the inner product as the commutator.

* **§A — the abstract CCR** (`generalised_ccr`).
* **§B — the Bargmann–Fock realization** (`bargmannInner`, `crePoly`, `ann`, `ann_crePoly`,
  `generalised_ccr_bargmann`, `canonical_ccr`).

## References

* J. B. Stochel, *Representation of generalised creation and annihilation operators in Fock space* (1997),
  Eqs. 2.5–2.8; V. Bargmann; K. Friedrichs. structures: `Mathlib.Algebra.MvPolynomial.Derivation`
  (`mkDerivation`); cf. `Dunkl.Oscillator` (single-mode `[∂, X·] = 1`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.BargmannFockCCR

open MvPolynomial Finset

/-! ## §A — the abstract CCR -/

/-- **[The generalised CCR, abstractly] `[D, g·] = c·I`.** For any derivation `D` of a commutative
`ℂ`-algebra and any element `g` with `D g = c·1`, the commutator of `D` with multiplication by `g` is the
scalar `c`: `D (g·f) − g·(D f) = c·f`. With `D = A_a⁻` (a directional derivative) and `g = ⟨·,b⟩` the linear
creation field, `c = ⟨a,b⟩` is the Hilbert inner product — the canonical commutation relation. -/
theorem generalised_ccr {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (g : R) (c : ℂ) (hg : D g = c • (1 : R)) (f : R) :
    D (g * f) - g * D f = c • f := by
  rw [Derivation.leibniz, hg, smul_eq_mul, add_sub_cancel_left, smul_eq_mul, mul_smul_comm,
    mul_one]

/-! ## §B — the Bargmann–Fock realization -/

/-- The polynomial core of the Bargmann space `B_∞`: complex polynomials in `n` holomorphic variables. -/
abbrev BargmannPoly (n : ℕ) : Type := MvPolynomial (Fin n) ℂ

/-- **The Hilbert inner product of two directions** `⟨a, b⟩ = ∑ᵢ b̄ᵢ aᵢ` on `ℂⁿ` (conjugate-linear in `b`,
linear in `a`) — the value the CCR returns. -/
def bargmannInner {n : ℕ} (a b : Fin n → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (b i) * a i

/-- **The creation field** `A_b⁺ = ⟨z, b⟩· = (∑ᵢ b̄ᵢ Xᵢ)·` — multiplication by the linear functional in
direction `b` (Eq. 2.7). -/
noncomputable def crePoly {n : ℕ} (b : Fin n → ℂ) : BargmannPoly n :=
  ∑ i, (starRingEnd ℂ) (b i) • X i

/-- **The annihilation operator** `A_a⁻ = ∑ᵢ aᵢ ∂ᵢ` — the directional derivative in direction `a`
(Eq. 2.8), built as the derivation sending `Xᵢ ↦ aᵢ`. -/
noncomputable def ann {n : ℕ} (a : Fin n → ℂ) : Derivation ℂ (BargmannPoly n) (BargmannPoly n) :=
  mkDerivation ℂ (fun i => C (a i))

/-- **[The directional derivative of the creation field is the inner product] `A_a⁻ ⟨z,b⟩ = ⟨a,b⟩·1`.** The
derivative of the *linear* field `⟨z, b⟩` in direction `a` is the constant `∑ᵢ b̄ᵢ aᵢ = ⟨a, b⟩` — the single
input that turns the Leibniz rule into the CCR. -/
theorem ann_crePoly {n : ℕ} (a b : Fin n → ℂ) :
    ann a (crePoly b) = bargmannInner a b • (1 : BargmannPoly n) := by
  have hsum : ann a (∑ i, (starRingEnd ℂ) (b i) • X i)
      = ∑ i, ann a ((starRingEnd ℂ) (b i) • X i) := map_sum (ann a).toLinearMap _ _
  rw [crePoly, hsum, bargmannInner, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hC : (C (a i) : BargmannPoly n) = a i • 1 := by
    rw [← MvPolynomial.algebraMap_eq]; exact Algebra.algebraMap_eq_smul_one (a i)
  simp only [Derivation.map_smul, ann, mkDerivation_X]
  rw [hC, smul_smul]

/-- **[Stochel's generalised CCR, realized] `[A_a⁻, A_b⁺] = ⟨a,b⟩·I`.** On the Bargmann polynomials, the
generalised annihilation and creation operators satisfy the canonical commutation relation: their commutator
is multiplication by the Hilbert inner product `⟨a, b⟩` of the two directions. -/
theorem generalised_ccr_bargmann {n : ℕ} (a b : Fin n → ℂ) (f : BargmannPoly n) :
    ann a (crePoly b * f) - crePoly b * ann a f = bargmannInner a b • f :=
  generalised_ccr (ann a) (crePoly b) (bargmannInner a b) (ann_crePoly a b) f

/-- **[The single-mode canonical pair] `[∂ₖ, Xₖ·] = 1`.** Taking both directions to be the `k`-th unit
vector `eₖ`, the inner product is `⟨eₖ, eₖ⟩ = 1`, so the generalised CCR reduces to the ordinary canonical
commutation relation `[A_{eₖ}⁻, A_{eₖ}⁺] = I` — the single-variable `[∂, X·] = 1` of the Bargmann–Fock
representation, here recovered as the diagonal of the Hilbert-space CCR. -/
theorem canonical_ccr {n : ℕ} (k : Fin n) (f : BargmannPoly n) :
    ann (Pi.single k 1) (crePoly (Pi.single k 1) * f)
      - crePoly (Pi.single k 1) * ann (Pi.single k 1) f = f := by
  have h : bargmannInner (Pi.single k (1 : ℂ)) (Pi.single k 1) = 1 := by
    rw [bargmannInner, Finset.sum_eq_single k]
    · simp
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp
  rw [generalised_ccr_bargmann, h, one_smul]

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.BargmannFockCCR

end
