/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Hankel bilinear forms and the Mittag–Leffler Fock kernel (Cascante–Fàbrega–Pascuas)

Formalizes the two *exact* algebraic cores of C. Cascante, J. Fàbrega, D. Pascuas, *Hankel bilinear forms
on generalized Fock–Sobolev spaces on `ℂⁿ`* (arXiv:1912.09241). The paper's main results (Thms 1.1, 1.3,
1.5) are analytic boundedness/compactness/Schatten characterizations with `≲`-estimates, Bergman-kernel
asymptotics and weak factorization — out of scope here. What *is* exact and formalizable:

**§A — the two-parametric Mittag–Leffler function** (§2.1), the entire function

  `E_{a,b}(λ) = ∑_{k≥0} λᵏ / Γ(ak + b)`   (`mittagLeffler`),

which generates the Bergman kernel of the Fock–Sobolev space (Lemma 2.5:
`K_α = (ℓα^{n/ℓ}/n!)·E_{1/ℓ,1/ℓ}^{(n-1)}(α^{1/ℓ}·)`). Its defining special value — used throughout for the
classical `ℓ = 1` Fock kernel `K(w,z) = (γⁿ/n!)e^{γ z·w̄}` (Eq. 1.3) — is

  `E_{1,1} = exp`   (`mittagLeffler_one_one`),

since `Γ(k+1) = k!`. This is the analytic seed of the reproducing kernel
(`OperatorAlgebra.BargmannFockCCR`, `K(w,z) = exp⟨w,z⟩`).

**§B — the Hankel bilinear form** (§1, the title). A bilinear form `Λ` on a product of function spaces is
**Hankel** iff `Λ(f, g) = Λ(fg, 1)` — it depends only on the *product* `fg`. On any commutative `ℂ`-algebra
this is exactly captured by a **linear symbol** `φ = Λ(·, 1)`:

* a Hankel form factors through multiplication, `Λ(f, g) = φ(fg)` (`hankel_apply_eq_symbol`);
* it is symmetric, `Λ(f, g) = Λ(g, f)` (`hankel_symm`), and shift-invariant, `Λ(fg, h) = Λ(f, gh)`
  (`hankel_shift`);
* conversely every linear `φ` gives a Hankel form `Λ_φ(f, g) = φ(fg)` (`isHankel_mulHankelForm`), and the two
  constructions are mutually inverse (`hankelSymbol_mulHankelForm`, `mulHankelForm_hankelSymbol`).

So **Hankel forms correspond bijectively to linear functionals on the product** — precisely the structure of
Theorem 1.1, where the symbol is the `α`-pairing `Λ(f, g) = ⟨fg, b⟩_α` (the analytic content being *which*
`b` make `Λ` bounded). The `α`-pairing symbol is the Fock inner product of `OperatorAlgebra.BargmannFockCCR`
(`bargmannInner`).

* **§A — Mittag–Leffler** (`mittagLeffler`, `mittagLeffler_one_one`).
* **§B — Hankel forms** (`IsHankel`, `hankelSymbol`, `hankel_apply_eq_symbol`, `hankel_symm`,
  `hankel_shift`, `mulHankelForm`, `isHankel_mulHankelForm`, `hankelSymbol_mulHankelForm`,
  `mulHankelForm_hankelSymbol`).

## References

* C. Cascante, J. Fàbrega, D. Pascuas, *Hankel bilinear forms on generalized Fock–Sobolev spaces on `ℂⁿ`*
  (2019), §1, §2.1, Thm 1.1. structures: `Mathlib` (`Complex.Gamma`, `NormedSpace.exp`, `LinearMap.mk₂`);
  cf. `OperatorAlgebra.BargmannFockCCR` (Fock kernel / inner product).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HankelFockSobolev

/-! ## §A — the Mittag–Leffler function -/

/-- **The two-parametric Mittag–Leffler function** `E_{a,b}(λ) = ∑_{k≥0} λᵏ / Γ(ak + b)` — the entire
function generating the Fock–Sobolev Bergman kernel (Lemma 2.5). -/
noncomputable def mittagLeffler (a b : ℂ) (z : ℂ) : ℂ :=
  ∑' (k : ℕ), z ^ k / Complex.Gamma (a * k + b)

/-- **[The defining special value] `E_{1,1} = exp`.** With `a = b = 1` the denominators are `Γ(k + 1) = k!`,
so the Mittag–Leffler series is the exponential — the `ℓ = 1` Fock/Bergman reproducing kernel. -/
theorem mittagLeffler_one_one (z : ℂ) : mittagLeffler 1 1 z = Complex.exp z := by
  rw [mittagLeffler]
  simp only [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  refine tsum_congr (fun k => ?_)
  rw [one_mul, Complex.Gamma_nat_eq_factorial]

/-! ## §B — the Hankel bilinear form -/

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- **A Hankel bilinear form**: `Λ(f, g) = Λ(fg, 1)` for all `f, g` — the form depends only on the product
`fg`. -/
def IsHankel (Λ : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop := ∀ f g : A, Λ f g = Λ (f * g) 1

/-- **The symbol** of a bilinear form: the linear functional `φ = Λ(·, 1)`. For a Hankel form it determines
`Λ` completely. -/
noncomputable def hankelSymbol (Λ : A →ₗ[ℂ] A →ₗ[ℂ] ℂ) : A →ₗ[ℂ] ℂ := Λ.flip 1

/-- **[A Hankel form factors through multiplication] `Λ(f, g) = φ(fg)`.** -/
theorem hankel_apply_eq_symbol {Λ : A →ₗ[ℂ] A →ₗ[ℂ] ℂ} (h : IsHankel Λ) (f g : A) :
    Λ f g = hankelSymbol Λ (f * g) := by
  rw [hankelSymbol, LinearMap.flip_apply]; exact h f g

/-- **[A Hankel form is symmetric] `Λ(f, g) = Λ(g, f)`** — because `fg = gf`. -/
theorem hankel_symm {Λ : A →ₗ[ℂ] A →ₗ[ℂ] ℂ} (h : IsHankel Λ) (f g : A) : Λ f g = Λ g f := by
  rw [h f g, h g f, mul_comm]

/-- **[A Hankel form is shift-invariant] `Λ(fg, h) = Λ(f, gh)`** — the displacement property characteristic of
Hankel (vs. Toeplitz) forms. -/
theorem hankel_shift {Λ : A →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hΛ : IsHankel Λ) (f g k : A) :
    Λ (f * g) k = Λ f (g * k) := by
  rw [hΛ (f * g) k, hΛ f (g * k), mul_assoc]

/-- **The Hankel form built from a linear symbol** `φ`: `Λ_φ(f, g) = φ(fg)` (Theorem 1.1's representation,
with `φ = ⟨·, b⟩`). -/
noncomputable def mulHankelForm (φ : A →ₗ[ℂ] ℂ) : A →ₗ[ℂ] A →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f g => φ (f * g))
    (fun f₁ f₂ g => by simp only [add_mul, map_add])
    (fun c f g => by simp only [smul_mul_assoc, map_smul])
    (fun f g₁ g₂ => by simp only [mul_add, map_add])
    (fun f c g => by simp only [mul_smul_comm, map_smul])

/-- **[Every linear symbol yields a Hankel form] `Λ_φ` is Hankel.** -/
theorem isHankel_mulHankelForm (φ : A →ₗ[ℂ] ℂ) : IsHankel (mulHankelForm φ) := by
  intro f g
  simp only [mulHankelForm, LinearMap.mk₂_apply, mul_one]

/-- **[Symbol of the form built from `φ` is `φ`].** -/
theorem hankelSymbol_mulHankelForm (φ : A →ₗ[ℂ] ℂ) : hankelSymbol (mulHankelForm φ) = φ := by
  ext h
  simp only [hankelSymbol, LinearMap.flip_apply, mulHankelForm, LinearMap.mk₂_apply, mul_one]

/-- **[A Hankel form is recovered from its symbol] `Λ_{φ_Λ} = Λ`.** Together with
`hankelSymbol_mulHankelForm`, this gives the bijection **Hankel forms ↔ linear functionals on the product**:
the algebraic core of Theorem 1.1. -/
theorem mulHankelForm_hankelSymbol {Λ : A →ₗ[ℂ] A →ₗ[ℂ] ℂ} (h : IsHankel Λ) :
    mulHankelForm (hankelSymbol Λ) = Λ := by
  ext f g
  simp only [mulHankelForm, LinearMap.mk₂_apply, hankelSymbol, LinearMap.flip_apply]
  exact (h f g).symm

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HankelFockSobolev

end
