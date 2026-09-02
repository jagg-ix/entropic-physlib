/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

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
  Eqs. 2.5–2.8; V. Bargmann; K. Friedrichs. Carriers: `Mathlib.Algebra.MvPolynomial.Derivation`
  (`mkDerivation`); cf. `Dunkl.Oscillator` (single-mode `[∂, X·] = 1`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.BargmannFockCCR

open MvPolynomial Finset


/-- **[The generalised CCR, abstractly] `[D, g·] = c·I`.** For any derivation `D` of a commutative
`ℂ`-algebra and any element `g` with `D g = c·1`, the commutator of `D` with multiplication by `g` is the
scalar `c`: `D (g·f) − g·(D f) = c·f`. With `D = A_a⁻` (a directional derivative) and `g = ⟨·,b⟩` the linear
creation field, `c = ⟨a,b⟩` is the Hilbert inner product — the canonical commutation relation. -/
lemma generalised_ccr {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (g : R) (c : ℂ) (hg : D g = c • (1 : R)) (f : R) :
    D (g * f) - g * D f = c • f := by
  rw [Derivation.leibniz, hg, smul_eq_mul, add_sub_cancel_left, smul_eq_mul, mul_smul_comm,
    mul_one]


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
lemma ann_crePoly {n : ℕ} (a b : Fin n → ℂ) :
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
lemma generalised_ccr_bargmann {n : ℕ} (a b : Fin n → ℂ) (f : BargmannPoly n) :
    ann a (crePoly b * f) - crePoly b * ann a f = bargmannInner a b • f :=
  generalised_ccr (ann a) (crePoly b) (bargmannInner a b) (ann_crePoly a b) f

/-- **[The single-mode canonical pair] `[∂ₖ, Xₖ·] = 1`.** Taking both directions to be the `k`-th unit
vector `eₖ`, the inner product is `⟨eₖ, eₖ⟩ = 1`, so the generalised CCR reduces to the ordinary canonical
commutation relation `[A_{eₖ}⁻, A_{eₖ}⁺] = I` — the single-variable `[∂, X·] = 1` of the Bargmann–Fock
representation, here recovered as the diagonal of the Hilbert-space CCR. -/
lemma canonical_ccr {n : ℕ} (k : Fin n) (f : BargmannPoly n) :
    ann (Pi.single k 1) (crePoly (Pi.single k 1) * f)
      - crePoly (Pi.single k 1) * ann (Pi.single k 1) f = f := by
  have h : bargmannInner (Pi.single k (1 : ℂ)) (Pi.single k 1) = 1 := by
    rw [bargmannInner, Finset.sum_eq_single k]
    · simp
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp
  rw [generalised_ccr_bargmann, h, one_smul]


/-! ## The SU(2) prepotential layer (Mathur, hep-lat/0405008)

Mathur solves SU(2) lattice gauge theory by attaching a harmonic-oscillator *doublet* to each end
of every link (his Eq. 6) and building the electric fields from the Jordan–Schwinger bilinears
`Eᵃ = a†(σᵃ/2)a` (Eq. 7), so that the su(2) quantization rules (Eq. 2) become *theorems* of the
oscillator CCR. On the Bargmann carrier the doublet is two polynomial variables, creation is
multiplication and annihilation is `pderiv`, and the Schwinger bilinears are the operators
`X i · ∂ⱼ`. Below: the su(2) relations in Cartan–Weyl form (`J⁺ = X₀∂₁`, `J⁻ = X₁∂₀`,
`T = 2J³ = X₀∂₀ − X₁∂₁`), the commuting `U(1)` number operator of his Eq. 12, and — on the
four-variable carrier of a full link (doublets `a = (X₀,X₁)`, `b = (X₂,X₃)`) — the gauge-invariant
singlet creation operator `a†·b̃† = X₀X₃ − X₁X₂` (Eq. 9), which is `U(1)`-neutral, and the
`U(1)` charge `N_a − N_b` of the link basis monomials (Eq. 11), whose vanishing is the abelian
Gauss law (Eq. 10). The powers of the singlet are the `d = 1` physical basis (Eq. 24); the
`SL(2)` invariance of the singlet is the `ε`-determinant mechanism
(`SuNTensorDecomposition.su2_singlet_bilinear_invariant`); the dilation-group reading of the
`U(1)` Gauss law is `ScaleDilationLogMetric` §G. -/

/-- **Partial derivatives commute** on the Bargmann polynomials — the equal-mixed-partials fact
`∂ᵢ∂ⱼ = ∂ⱼ∂ᵢ` (not in Mathlib for `pderiv`; proved by polynomial induction). -/
lemma pderiv_pderiv_comm {n : ℕ} (i j : Fin n) (f : BargmannPoly n) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    rcases eq_or_ne k i with hki | hki <;> rcases eq_or_ne k j with hkj | hkj
    · subst hki; subst hkj; rfl
    · subst hki
      simp only [pderiv_mul, map_add, hp, pderiv_X_self, pderiv_X_of_ne hkj,
        mul_zero, add_zero, mul_one]
    · subst hkj
      simp only [pderiv_mul, map_add, hp, pderiv_X_self, pderiv_X_of_ne hki,
        mul_zero, add_zero, mul_one]
    · simp only [pderiv_mul, hp, pderiv_X_of_ne hki, pderiv_X_of_ne hkj,
        mul_zero, add_zero]

/-- **The Schwinger raising operator** `J⁺ = a†₁a₂ = X₀·∂₁` (Mathur Eq. 7 in Cartan–Weyl form). -/
noncomputable def schwingerRaise (f : BargmannPoly 2) : BargmannPoly 2 := X 0 * pderiv 1 f

/-- **The Schwinger lowering operator** `J⁻ = a†₂a₁ = X₁·∂₀`. -/
noncomputable def schwingerLower (f : BargmannPoly 2) : BargmannPoly 2 := X 1 * pderiv 0 f

/-- **The Cartan generator** `T = 2J³ = a†₁a₁ − a†₂a₂ = X₀∂₀ − X₁∂₁` (`σ³ = diag(1,−1)` with the
half absorbed). -/
noncomputable def schwingerCartan (f : BargmannPoly 2) : BargmannPoly 2 :=
  X 0 * pderiv 0 f - X 1 * pderiv 1 f

/-- **The `U(1)` number operator** `N = a†₁a₁ + a†₂a₂ = X₀∂₀ + X₁∂₁` — the generator of Mathur's
novel abelian gauge invariance (his Eq. 12), *not* a subgroup of the SU(2). -/
noncomputable def schwingerNumber (f : BargmannPoly 2) : BargmannPoly 2 :=
  X 0 * pderiv 0 f + X 1 * pderiv 1 f

/-- **[su(2), Cartan–raising]** `[T, J⁺] = 2J⁺`: the quantization rule of Mathur's Eq. 2, *derived*
from the oscillator CCR of the Bargmann carrier. -/
theorem schwinger_cartan_raise (f : BargmannPoly 2) :
    schwingerCartan (schwingerRaise f) - schwingerRaise (schwingerCartan f)
      = 2 * schwingerRaise f := by
  simp only [schwingerCartan, schwingerRaise, map_sub, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  linear_combination (X 0 * X 0) * pderiv_pderiv_comm 0 1 f

/-- **[su(2), Cartan–lowering]** `[T, J⁻] = −2J⁻`. -/
theorem schwinger_cartan_lower (f : BargmannPoly 2) :
    schwingerCartan (schwingerLower f) - schwingerLower (schwingerCartan f)
      = -(2 * schwingerLower f) := by
  simp only [schwingerCartan, schwingerLower, map_sub, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  linear_combination (X 1 * X 1) * pderiv_pderiv_comm 0 1 f

/-- **[su(2), raising–lowering]** `[J⁺, J⁻] = T`: the third quantization rule, closing the su(2)
algebra of the electric fields on the link end. -/
theorem schwinger_raise_lower (f : BargmannPoly 2) :
    schwingerRaise (schwingerLower f) - schwingerLower (schwingerRaise f)
      = schwingerCartan f := by
  simp only [schwingerCartan, schwingerRaise, schwingerLower, pderiv_mul, pderiv_X_self]
  linear_combination (X 0 * X 1) * pderiv_pderiv_comm 1 0 f

/-- **[The `U(1)` commutes with the raising operator]** `[N, J⁺] = 0` — Mathur's `SU(2) ⊗ U(1)`:
the abelian number symmetry and the su(2) act independently on the link end. -/
theorem schwinger_number_raise (f : BargmannPoly 2) :
    schwingerNumber (schwingerRaise f) - schwingerRaise (schwingerNumber f) = 0 := by
  simp only [schwingerNumber, schwingerRaise, map_add, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  linear_combination (X 0 * X 0) * pderiv_pderiv_comm 0 1 f

/-- **[The `U(1)` commutes with the lowering operator]** `[N, J⁻] = 0`. -/
theorem schwinger_number_lower (f : BargmannPoly 2) :
    schwingerNumber (schwingerLower f) - schwingerLower (schwingerNumber f) = 0 := by
  simp only [schwingerNumber, schwingerLower, map_add, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  linear_combination (X 1 * X 1) * pderiv_pderiv_comm 1 0 f

/-- **The singlet creation operator of a link** `a†·b̃† = a†₁b†₂ − a†₂b†₁ = X₀X₃ − X₁X₂`
(Mathur Eq. 9): with the two prepotential doublets `a = (X₀, X₁)`, `b = (X₂, X₃)` at the two link
ends, this is the manifestly SU(2)-invariant pair creation whose powers generate the `d = 1`
physical Hilbert space (his Eq. 24). -/
noncomputable def singletCre : BargmannPoly 4 := X 0 * X 3 - X 1 * X 2

/-- **The link `U(1)` charge operator** `Q = N_a − N_b = X₀∂₀ + X₁∂₁ − X₂∂₂ − X₃∂₃` — the
generator of Mathur's Eq. 12 phase `a† ↦ e^{iθ}a†`, `b† ↦ e^{−iθ}b†`; its kernel is the abelian
Gauss law `N_a = N_b` (Eq. 10). -/
noncomputable def linkCharge (f : BargmannPoly 4) : BargmannPoly 4 :=
  X 0 * pderiv 0 f + X 1 * pderiv 1 f - X 2 * pderiv 2 f - X 3 * pderiv 3 f

/-- **[The singlet is `U(1)`-neutral]** `Q(S·f) = S·(Qf)`: creating a gauge-invariant pair does not
change the link `U(1)` charge — the singlet of Eq. 9 respects the Gauss law of Eq. 10, which is why
its powers solve both constraints at once (Eq. 24). -/
theorem linkCharge_singletCre_mul (f : BargmannPoly 4) :
    linkCharge (singletCre * f) = singletCre * linkCharge f := by
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  simp only [linkCharge, singletCre, pderiv_mul, map_sub, pderiv_X_self]
  simp only [pderiv_X_of_ne (show (0 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 2 by decide),
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 2 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 2 by decide)]
  ring

/-- **[The link basis monomials are `U(1)` eigenstates with charge `N_a − N_b`]** the Eq. 11 basis
state `(a†₁)^p(a†₂)^q(b†₁)^r(b†₂)^s|0⟩` carries link charge `(p + q) − (r + s)`; the abelian Gauss
law (Eq. 10) is exactly charge zero, `p + q = r + s` — i.e. `N_a = N_b`. -/
theorem linkCharge_basisMonomial (p q r s : ℕ) :
    linkCharge (X 0 ^ p * X 1 ^ q * X 2 ^ r * X 3 ^ s)
      = C (((p : ℂ) + q) - ((r : ℂ) + s)) * (X 0 ^ p * X 1 ^ q * X 2 ^ r * X 3 ^ s) := by
  have hpow : ∀ (i : Fin 4) (k : ℕ), pderiv i ((X i : BargmannPoly 4) ^ k)
      = k • ((X i : BargmannPoly 4) ^ (k - 1)) := by
    intro i k
    rw [Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, mul_one]
  have hne : ∀ (i j : Fin 4), j ≠ i → ∀ (k : ℕ),
      pderiv i ((X j : BargmannPoly 4) ^ k) = 0 := by
    intro i j hij k
    rw [Derivation.leibniz_pow, pderiv_X_of_ne hij, smul_zero, smul_zero]
  rcases p with _ | p <;> rcases q with _ | q <;> rcases r with _ | r <;> rcases s with _ | s <;>
    · simp only [linkCharge, pderiv_mul, hpow, nsmul_eq_mul,
        hne 0 1 (by decide), hne 0 2 (by decide), hne 0 3 (by decide),
        hne 1 0 (by decide), hne 1 2 (by decide), hne 1 3 (by decide),
        hne 2 0 (by decide), hne 2 1 (by decide), hne 2 3 (by decide),
        hne 3 0 (by decide), hne 3 1 (by decide), hne 3 2 (by decide),
        Nat.succ_sub_one, map_sub, map_add, map_natCast]
      push_cast
      ring


/-! ### The generating function, the vertex factors, and the `(2j)!(2j+1)!` normalization
(Mathur, hep-lat/0405008 Eqs. 20–28)

Mathur builds the orthonormal physical basis from SU(2) coherent-state generating functions:
`exp(δ₃·a†·b̃†)|0⟩ = Σ_c (δ₃^c/c!)·S^c|0⟩` graded by the pair number, with vertex factors
`Φ_{j₁j₂j}(δ)` (Eq. 23) carrying the angular-momentum bookkeeping in Schwinger's exponent
dictionary `a = j₁−j₂+j, b = −j₁+j₂+j, c = j₁+j₂−j`. Below, all of it at exact-arithmetic level
on the Bargmann carrier: the pair annihilation `singletAnn` adjoint to `singletCre` obeys
`A(S·f) = 2f + Ef + S·Af` with `E` the Euler operator, whence `A(Sⁿ) = n(n+1)Sⁿ⁻¹` and the
**Eq. 24 normalization** `Aⁿ(Sⁿ) = n!(n+1)!·1` — i.e. `‖(a†·b̃†)^{2j}|0⟩‖² = (2j)!(2j+1)!` with
`n = 2j`, since iterating the adjoint pair against the pair power returns the Fock norm² on the
vacuum. The vertex-factor arithmetic: `Φ²(0,0,c) = c+1` (`vertexFactorSq_dOne`), consistent with
the generating-function coefficient — `Φ²·(c!)² = c!(c+1)!` (`generating_coefficient_consistency`)
— and the per-rung product with the Eq. 28 normalization constant collapses to `(a+b)!/c!`
(`vertex_normalization_product`). The `d = 1` projection `δ = (0, 0, δ₃)` kills every channel with
`a ≠ 0` or `b ≠ 0` (`dOne_selection`), forcing `j₁ = j₂, j = 0` exactly as in the paper; the
Schwinger exponents solve the triangle constraints identically (`triangle_from_exponents`). -/

/-- **The Euler (total-number) operator** `E = Σᵢ Xᵢ∂ᵢ` on the link carrier — total occupation,
the generator of the overall scale grading. -/
noncomputable def eulerOp (f : BargmannPoly 4) : BargmannPoly 4 :=
  X 0 * pderiv 0 f + X 1 * pderiv 1 f + X 2 * pderiv 2 f + X 3 * pderiv 3 f

/-- **The singlet pair annihilation** `A = ∂₀∂₃ − ∂₁∂₂` — the Fock adjoint of multiplication by
`singletCre = X₀X₃ − X₁X₂`. -/
noncomputable def singletAnn (f : BargmannPoly 4) : BargmannPoly 4 :=
  pderiv 0 (pderiv 3 f) - pderiv 1 (pderiv 2 f)

/-- **[The Leibniz identity of the pair]** `A(S·f) = 2f + Ef + S·Af`: annihilating across one
created pair yields the constant `2`, the total number, and the pass-through — the su(1,1)
structure behind the normalization. -/
lemma singletAnn_singletCre_mul (f : BargmannPoly 4) :
    singletAnn (singletCre * f) = f + f + eulerOp f + singletCre * singletAnn f := by
  simp only [singletAnn, singletCre, eulerOp, sub_mul, map_sub, map_add, pderiv_mul,
    pderiv_X_self,
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 2 by decide),
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 2 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 2 by decide),
    map_zero, mul_zero, zero_mul, add_zero, mul_one, one_mul]
  ring

/-- The Euler operator is a derivation on products. -/
lemma eulerOp_mul (f g : BargmannPoly 4) :
    eulerOp (f * g) = eulerOp f * g + f * eulerOp g := by
  simp only [eulerOp, pderiv_mul]
  ring

/-- The singlet pair carries total number `2`: `E(S) = S + S`. -/
lemma eulerOp_singletCre : eulerOp singletCre = singletCre + singletCre := by
  simp only [eulerOp, singletCre, map_sub, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 2 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (0 : Fin 4) ≠ 2 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (1 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 4) ≠ 3 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 1 by decide),
    pderiv_X_of_ne (show (3 : Fin 4) ≠ 2 by decide)]
  ring

/-- **[The pair power is a number eigenstate]** `E(Sⁿ⁺¹) = 2(n+1)·Sⁿ⁺¹` — `n+1` pairs carry total
occupation `2(n+1)`. -/
lemma eulerOp_singletCre_pow (n : ℕ) :
    eulerOp (singletCre ^ (n + 1)) = (2 * (n + 1)) • singletCre ^ (n + 1) := by
  induction n with
  | zero =>
    have hb : (2 * (0 + 1) : ℕ) • singletCre ^ 1 = singletCre + singletCre := by
      rw [pow_one]
      exact two_nsmul singletCre
    rw [pow_one, eulerOp_singletCre, ← hb, pow_one]
  | succ n ih =>
    rw [pow_succ', eulerOp_mul, eulerOp_singletCre, ih, mul_smul_comm, ← pow_succ',
      add_mul, ← pow_succ']
    have hco : 2 * (n + 1 + 1) = 2 * (n + 1) + 2 := by ring
    rw [hco, add_smul, two_smul]
    abel

/-- Pair annihilation is additive over `ℕ`-scaling. -/
lemma singletAnn_nsmul (k : ℕ) (f : BargmannPoly 4) :
    singletAnn (k • f) = k • singletAnn f := by
  simp [singletAnn, smul_sub]

/-- **[The pair-annihilation recursion]** `A(Sⁿ⁺¹) = (n+1)(n+2)·Sⁿ` — Mathur's exact grading:
each annihilation strips one pair and returns the su(1,1) eigenvalue. -/
theorem singletAnn_singletCre_pow (n : ℕ) :
    singletAnn (singletCre ^ (n + 1)) = ((n + 1) * (n + 2)) • singletCre ^ n := by
  induction n with
  | zero =>
    rw [pow_one, show singletCre = singletCre * 1 by rw [mul_one],
      singletAnn_singletCre_mul]
    simp [eulerOp, singletAnn, one_add_one_eq_two]
  | succ n ih =>
    rw [pow_succ', singletAnn_singletCre_mul, ih, eulerOp_singletCre_pow, mul_smul_comm,
      ← pow_succ']
    have hpack : singletCre ^ (n + 1) + singletCre ^ (n + 1)
          + (2 * (n + 1)) • singletCre ^ (n + 1)
          + ((n + 1) * (n + 2)) • singletCre ^ (n + 1)
        = (1 + 1 + 2 * (n + 1) + (n + 1) * (n + 2)) • singletCre ^ (n + 1) := by
      rw [add_smul, add_smul, add_smul, one_smul]
    rw [hpack]
    congr 1
    ring

/-- **[Mathur's Eq. 24 normalization]** `Aⁿ(Sⁿ) = n!·(n+1)!·1`: iterating the pair annihilation
against the pair-creation power returns the vacuum with coefficient `n!(n+1)!` — on the Fock
pairing (where `A` is the adjoint of `S·`) this *is* `‖(a†·b̃†)^{2j}|0⟩‖² = (2j)!(2j+1)!` with
`n = 2j`, the closed-form orthonormalization of the `d = 1` physical basis. -/
theorem singlet_normalization (n : ℕ) :
    singletAnn^[n] (singletCre ^ n)
      = (n.factorial * (n + 1).factorial) • (1 : BargmannPoly 4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hiter : ∀ (m k : ℕ) (g : BargmannPoly 4),
        singletAnn^[m] (k • g) = k • singletAnn^[m] g := by
      intro m
      induction m with
      | zero => intro k g; simp
      | succ m ihm =>
        intro k g
        rw [Function.iterate_succ_apply, singletAnn_nsmul, ihm,
          ← Function.iterate_succ_apply]
    rw [Function.iterate_succ_apply, singletAnn_singletCre_pow, hiter, ih, smul_smul]
    congr 1
    rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    ring

/-- **The vertex factor squared** `Φ²_{j₁j₂j}` of Mathur's Eq. 23 at unit phases, in Schwinger's
exponent dictionary `a = j₁−j₂+j`, `b = −j₁+j₂+j`, `c = j₁+j₂−j`:
`Φ² = (a+b+c+1)!/((a+b+1)·a!·b!·c!)`. -/
def vertexFactorSq (a b c : ℕ) : ℚ :=
  (a + b + c + 1).factorial / ((a + b + 1) * a.factorial * b.factorial * c.factorial)

/-- **[The `d = 1` vertex]** `Φ²(0,0,c) = c+1` — the single-rung vertex factor of the trivial
ladder. -/
lemma vertexFactorSq_dOne (c : ℕ) : vertexFactorSq 0 0 c = c + 1 := by
  unfold vertexFactorSq
  simp only [Nat.zero_add, Nat.factorial_zero]
  rw [Nat.factorial_succ]
  have hc : ((c.factorial : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **[Generating function ↔ normalization consistency]** `Φ²·(c!)² = c!(c+1)!`: the `c`-th
coefficient of `exp(δ₃S)|0⟩` is `S^c/c!`, whose squared Fock norm `c!(c+1)!/(c!)² = c+1` is
exactly the `d = 1` vertex factor — Eqs. 22, 23 and 24 close on each other. -/
theorem generating_coefficient_consistency (c : ℕ) :
    vertexFactorSq 0 0 c * (c.factorial * c.factorial)
      = c.factorial * (c + 1).factorial := by
  rw [vertexFactorSq_dOne, Nat.factorial_succ]
  push_cast
  ring

/-- **[Vertex × Eq. 28 normalization]** the per-rung product of the squared vertex factor with
Mathur's normalization constant `N_r = (2J+1)!·a!·b!/(a+b+c+1)!` collapses to `(a+b)!/c!` — the
factorial bookkeeping of the ladder telescopes rung by rung. -/
theorem vertex_normalization_product (a b c : ℕ) :
    ((a + b + 1).factorial * a.factorial * b.factorial : ℚ) / (a + b + c + 1).factorial
        * vertexFactorSq a b c
      = (a + b).factorial / c.factorial := by
  unfold vertexFactorSq
  rw [Nat.factorial_succ (a + b)]
  have h1 : ((a + b + c + 1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (a.factorial : ℚ) ≠ 0 := by positivity
  have h3 : (b.factorial : ℚ) ≠ 0 := by positivity
  have h4 : (c.factorial : ℚ) ≠ 0 := by positivity
  have h5 : ((a : ℚ) + b + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **[Schwinger's dictionary solves the triangle]** with `2j₁ = a+c`, `2j₂ = b+c`, `2j = a+b`,
the angular-momentum triangle inequalities hold identically in the exponents. -/
theorem triangle_from_exponents (a b c : ℕ) :
    a + b ≤ (a + c) + (b + c) ∧ a + c ≤ (a + b) + (b + c) ∧ b + c ≤ (a + b) + (a + c) := by
  omega

/-- **[The `d = 1` projection selects the singlet channel]** at `δ = (0, 0, δ₃)` the vertex
monomial `δ₁^a δ₂^b δ₃^c` survives only for `a = b = 0` — i.e. `j₁ = j₂` and `j = 0`, Mathur's
selection after Eq. 23: only pure singlet powers remain, the Eq. 24 basis. -/
theorem dOne_selection (a b c : ℕ) (d3 : ℂ)
    (h : (0 : ℂ) ^ a * (0 : ℂ) ^ b * d3 ^ c ≠ 0) : a = 0 ∧ b = 0 := by
  constructor
  · by_contra ha
    rw [zero_pow ha] at h
    simp at h
  · by_contra hb
    rw [zero_pow hb] at h
    simp at h


/-! ### The non-Hermitian oscillator virial ladder (Hajong–Modak–Mandal §V, Eqs. 33–40)

For the complex-frequency oscillator `H = p²/2 + Ω²x²/2` (`Ω = ω₁ + iω₂`, not PT-invariant), the
generalized virial theorem gives trapping energy `Ẽ_tr = ½⟨Ω²x²⟩_G = (Ω/4)⟨2N+1⟩ = ½E_n` — the
*same* half-energy relation as the Hermitian oscillator, because the ladder algebra is
frequency-independent. The carrier fact, on the Bargmann representation (`a† = X·`, `a = ∂`):
`(a a† + a† a)|n⟩ = (2n+1)|n⟩` — exactly the paper's Eq. 40 middle step, with the complex `Ω`
entering only the scalar prefactor `Ω/4`. -/

/-- **[The virial ladder]** `(a a† + a† a) Xⁿ = (2n+1)·Xⁿ` on the single-mode Bargmann carrier:
the symmetric ladder combination behind `⟨x²⟩` is diagonal with eigenvalue `2n+1`, independent
of any (possibly complex) frequency. -/
theorem oscillator_virial_ladder (n : ℕ) :
    pderiv 0 ((X 0 : BargmannPoly 1) * (X 0 : BargmannPoly 1) ^ n)
        + (X 0 : BargmannPoly 1) * pderiv 0 ((X 0 : BargmannPoly 1) ^ n)
      = (2 * n + 1) • ((X 0 : BargmannPoly 1) ^ n) := by
  have hpow : ∀ k : ℕ, pderiv 0 ((X 0 : BargmannPoly 1) ^ k)
      = k • ((X 0 : BargmannPoly 1) ^ (k - 1)) := by
    intro k
    rw [Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, mul_one]
  rcases n with _ | m
  · simp
  · have hXpow : (X 0 : BargmannPoly 1) * (X 0 : BargmannPoly 1) ^ (m + 1)
        = (X 0 : BargmannPoly 1) ^ (m + 2) := (pow_succ' _ _).symm
    rw [hXpow, hpow (m + 2), hpow (m + 1), Nat.succ_sub_one, Nat.succ_sub_one,
      mul_smul_comm, ← pow_succ']
    have hpack : (m + 2) • ((X 0 : BargmannPoly 1) ^ (m + 1))
          + (m + 1) • ((X 0 : BargmannPoly 1) ^ (m + 1))
        = (2 * (m + 1) + 1) • ((X 0 : BargmannPoly 1) ^ (m + 1)) := by
      rw [← add_smul]
      congr 1
      ring
    exact hpack

/-- **[The trapping energy is half the energy]** `(Ω/4)·(2n+1) = ½·(n+½)·Ω` for *any* complex
frequency: combined with `oscillator_virial_ladder`, the non-Hermitian oscillator's trapping
energy equals half its eigenenergy — the paper's Eq. 40, indistinguishable from the Hermitian
case because the imaginary part of `Ω` never touches the ladder count. -/
theorem oscillator_virial_half_energy (n : ℕ) (Om : ℂ) :
    Om / 4 * (2 * n + 1) = 1 / 2 * ((n + 1 / 2) * Om) := by
  ring

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.BargmannFockCCR

end
