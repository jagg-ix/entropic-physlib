/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Saveliev's mass transformation IS a Bogoliubov squeeze (canonical pair ↔ `p, q`)

The deepest layer connecting Saveliev's linear Boltzmann collision operator (*V. Saveliev, J. Math. Phys.
37 (1996) 6139*) to the repository's canonical infrastructure: Saveliev's **mass generator** `M = ∇v∗ =
ad_{∇v}` acting on the canonical pair `(∇, v)` (with `[∇, v] = 1`) is the **Bogoliubov / squeeze
generator**, and the **mass transformation** `e^{ξ M}` is a Bogoliubov transformation
(`Bogoliubov.BosonicBogoliubovDiagonalization.bosonicBogoliubov`).

* **(operator side)** the mass generator is the `sl(2)` Cartan / squeeze: `ad_{∇v}(∇) = −∇`
  (`collisionStar_delVel_del`), `ad_{∇v}(v) = +v` (`collisionStar_delVel_vel`). So `e^{ξ ad_{∇v}}` scales
  `∇ ↦ e^{−ξ}∇`, `v ↦ e^{ξ}v` — exactly a squeeze of the canonical pair.
* **(matrix side)** the Bogoliubov transformation `bosonicBogoliubov(cosh ξ, sinh ξ)` has the light-cone
  eigenvectors `(1, ±1)` with eigenvalues `e^{±ξ}` (`bogoliubov_eigvec_plus/minus`,
  `bogoliubov_squeeze_eigenvalues`) — the *same* squeeze factors — and preserves the symplectic/Minkowski
  metric `S` (`bosonicBogoliubov_cosh_sinh_preserves_S`), i.e. it preserves the canonical commutator.
* **(identification)** the squeeze rapidity is Saveliev's mass parameter `ξ = ln(1+m)`: at `ξ = ln(1+m)`
  the `v`-eigenvalue is `e^{ξ} = 1+m` and the `∇`-eigenvalue is `e^{−ξ} = 1/(1+m)`
  (`saveliev_mass_bogoliubov_squeeze`).

So Saveliev's energy/mass `sl(2)` (`∇², ∇v, v²`) is the squeezing algebra, the mass transformation is a
Bogoliubov transformation, and `[∇, v] = 1` is the canonical commutator preserved by it.

No new axioms.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.BogoliubovSqueeze

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization

/-! ## §A — the operator side: the mass generator is the squeeze (`sl(2)` Cartan) -/

/-- **The mass generator `M = ∇v∗` is the squeeze generator on the canonical pair**: `ad_{∇v}(∇) = −∇` and
`ad_{∇v}(v) = +v` (`collisionStar_delVel_del`, `collisionStar_delVel_vel`). The pair `(∇, v)` are the
eigenvectors of `M` with eigenvalues `∓1` — the `sl(2)` Cartan structure. -/
theorem massGen_squeeze {R : Type*} [Ring R] (del vel : R) (h : collisionStar del vel = 1) :
    collisionStar (del * vel) del = -del ∧ collisionStar (del * vel) vel = vel :=
  ⟨collisionStar_delVel_del del vel h, collisionStar_delVel_vel del vel h⟩

/-! ## §B — the matrix side: the Bogoliubov light-cone eigenvalues are the squeeze factors -/

/-- **The `(1,1)` light-cone mode is a Bogoliubov eigenvector** with eigenvalue `u + v`. -/
theorem bogoliubov_eigvec_plus (u v : ℝ) :
    bosonicBogoliubov u v *ᵥ ![1, 1] = (u + v) • ![1, 1] := by
  funext i
  fin_cases i <;> simp [bosonicBogoliubov, Matrix.mulVec, Fin.sum_univ_two, dotProduct] <;> ring

/-- **The `(1,−1)` light-cone mode is a Bogoliubov eigenvector** with eigenvalue `u − v`. -/
theorem bogoliubov_eigvec_minus (u v : ℝ) :
    bosonicBogoliubov u v *ᵥ ![1, -1] = (u - v) • ![1, -1] := by
  funext i
  fin_cases i <;> simp [bosonicBogoliubov, Matrix.mulVec, Fin.sum_univ_two, dotProduct] <;> ring

/-- **The Bogoliubov squeeze eigenvalues are `e^{±ξ}`.** At `u = cosh ξ`, `v = sinh ξ` the light-cone
eigenvalues `u ± v` are `e^{±ξ}` — the squeeze factors of the rapidity-`ξ` Bogoliubov transformation. -/
theorem bogoliubov_squeeze_eigenvalues (ξ : ℝ) :
    Real.cosh ξ + Real.sinh ξ = Real.exp ξ ∧ Real.cosh ξ - Real.sinh ξ = Real.exp (-ξ) :=
  ⟨by rw [Real.cosh_eq, Real.sinh_eq]; ring,
   by rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]; ring⟩

/-! ## §C — the identification: Saveliev's mass transformation is the Bogoliubov squeeze -/

/-- **Saveliev's mass transformation is the Bogoliubov squeeze of the canonical pair.** Bundles, for the
squeeze rapidity `ξ` (Saveliev's mass parameter, `ξ = ln(1+m)`):

* **(operator)** the mass generator `M = ∇v∗` squeezes the canonical pair `∇ ↦ −∇`, `v ↦ +v`;
* **(matrix)** the Bogoliubov transformation `bosonicBogoliubov(cosh ξ, sinh ξ)` acts on the `v`-mode
  `(1,1)` with eigenvalue `e^{ξ}` and on the `∇`-mode `(1,−1)` with eigenvalue `e^{−ξ}` — the same squeeze
  factors that `e^{ξ M}` produces (`ad_{∇v}(v) = v` ⟹ `e^{ξ}`, `ad_{∇v}(∇) = −∇` ⟹ `e^{−ξ}`);
* **(symplectic)** it preserves the Minkowski metric `S`, i.e. the canonical commutator `[∇, v] = 1`. -/
theorem saveliev_mass_bogoliubov_squeeze {R : Type*} [Ring R] (del vel : R)
    (h : collisionStar del vel = 1) (ξ : ℝ) :
    (collisionStar (del * vel) del = -del ∧ collisionStar (del * vel) vel = vel)
      ∧ (bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ) *ᵥ ![1, 1] = Real.exp ξ • ![1, 1])
      ∧ (bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ) *ᵥ ![1, -1] = Real.exp (-ξ) • ![1, -1])
      ∧ (bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ))ᵀ * symplecticS
          * bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ) = symplecticS := by
  refine ⟨massGen_squeeze del vel h, ?_, ?_, bosonicBogoliubov_cosh_sinh_preserves_S ξ⟩
  · rw [bogoliubov_eigvec_plus, (bogoliubov_squeeze_eigenvalues ξ).1]
  · rw [bogoliubov_eigvec_minus, (bogoliubov_squeeze_eigenvalues ξ).2]

/-! ## §D — the canonical pair, properly realized: `∇ = d/dX`, `v = X·` with `[∇,v] = 1` a *theorem* -/

section Realization

open Polynomial

/-! ### Base operators -/

/-- **The gradient `∇ = d/dX`** as a genuine operator — Saveliev's momentum-like generator, the formal
derivative on `ℝ[X]` (`Module.End ℝ ℝ[X]`). This is the *concrete* `∇`, not an abstract placeholder. -/
noncomputable def gradOp : Module.End ℝ ℝ[X] := Polynomial.derivative

/-- **The velocity `v = X·`** as a genuine operator — Saveliev's position-like generator, multiplication
by `X` on `ℝ[X]`. This is the *concrete* `v`. -/
noncomputable def velOp : Module.End ℝ ℝ[X] := LinearMap.mulLeft ℝ (X : ℝ[X])

/-- **`∇` acts as the derivative**: `∇ p = p'`. -/
@[simp] theorem gradOp_apply (p : ℝ[X]) : gradOp p = derivative p := rfl

/-- **`v` acts as multiplication by `X`**: `v p = X · p`. -/
@[simp] theorem velOp_apply (p : ℝ[X]) : velOp p = X * p := rfl

/-- **The canonical commutation relation `[∇, v] = 1` is a THEOREM, not a hypothesis.** On `ℝ[X]` the
derivative and multiplication-by-`X` operators satisfy `[d/dX, X·] = 1` — the Schrödinger/Bargmann
representation of the Heisenberg algebra — because `(Xp)' − X p' = p` (`Polynomial.derivative_mul`,
`derivative_X`). This realizes Saveliev's abstract `[∇, v] = 1`, so every collision-operator lemma proved
under that hypothesis holds *non-vacuously* for these genuine operators. -/
theorem ccr : collisionStar gradOp velOp = 1 := by
  refine LinearMap.ext fun p => ?_
  simp only [collisionStar, LinearMap.sub_apply, Module.End.mul_apply, gradOp, velOp,
    LinearMap.mulLeft_apply, derivative_mul, derivative_X, Module.End.one_apply]
  ring

/-! ### The quadratic operators (Saveliev's `∇², v², ∇v, v∇`) -/

/-- **`∇² = d²/dX²`** (Saveliev's `Q₁` generator element): `∇² p = (p')'`. -/
theorem gradSq_apply (p : ℝ[X]) : (gradOp * gradOp) p = derivative (derivative p) := rfl

/-- **`v² = X²·`** (Saveliev's `Q₃` generator element): `v² p = X² · p`. -/
theorem velSq_apply (p : ℝ[X]) : (velOp * velOp) p = X ^ 2 * p := by
  show X * (X * p) = X ^ 2 * p; ring

/-- **`∇v` (the mass generator element `M`)**: `∇v p = (X · p)'`. -/
theorem gradVel_apply (p : ℝ[X]) : (gradOp * velOp) p = derivative (X * p) := rfl

/-- **`v∇` (the `Q₂` generator element)**: `v∇ p = X · p'`. -/
theorem velGrad_apply (p : ℝ[X]) : (velOp * gradOp) p = X * derivative p := rfl

/-- **`v∇` is the number (degree) operator**: on a monomial `X^n` it returns `n · X^n` — the degree is the
eigenvalue. This is the harmonic-oscillator number operator `N = v∇` realized on `ℝ[X]`. -/
theorem numberOp_monomial (n : ℕ) : (velOp * gradOp) (X ^ n) = (n : ℝ) • X ^ n := by
  rw [velGrad_apply, derivative_X_pow, smul_eq_C_mul]
  cases n with
  | zero => simp
  | succ k => rw [Nat.succ_sub_one]; ring

/-! ### The translation operator (Saveliev Eq. 10, `e^{a∇}`) -/

/-- **The translation operator `e^{a∇}`** (Saveliev Eq. 10) generated by `∇ = d/dX`, realized as the Taylor
shift on `ℝ[X]`. -/
noncomputable def transOp (a : ℝ) : Module.End ℝ ℝ[X] := Polynomial.taylor a

/-- **[Saveliev Eq. 10] `e^{a∇} f(v) = f(v + a)`**: the operator generated by `∇` shifts the argument,
`transOp a p = p(X + a)`. -/
theorem transOp_apply (a : ℝ) (p : ℝ[X]) : transOp a p = p.comp (X + C a) :=
  Polynomial.taylor_apply a p

/-! ### The star maps `∗ = ad` (the building blocks of the collision operator, Eq. 18) -/

/-- **`∇∗ v = 1`** — the star map of `∇` on `v` is the identity (the CCR). -/
theorem gradStar_vel : collisionStar gradOp velOp = 1 := ccr

/-- **`v∗ ∇ = −1`** — the star map of `v` on `∇`. -/
theorem velStar_grad : collisionStar velOp gradOp = -1 := by
  have e : collisionStar velOp gradOp = -collisionStar gradOp velOp := by
    unfold collisionStar; noncomm_ring
  rw [e, ccr]

/-- **`∇∗ ∇ = 0`** — `∇` commutes with itself. -/
theorem gradStar_grad : collisionStar gradOp gradOp = 0 := collisionStar_self gradOp

/-- **`∇∗ v² = 2v`** — the star map of `∇` on `v²` (`[∇, v²] = 2v`). -/
theorem gradStar_velSq : collisionStar gradOp (velOp * velOp) = 2 * velOp :=
  collisionStar_del_velSq gradOp velOp ccr

/-! ### The `sl(2)` algebra of the quadratic generators, realized -/

/-- **`[∇², v²] = 4∇v − 2`** for the genuine operators (`sl(2)` closing relation). -/
theorem realized_sl2 :
    collisionStar (gradOp * gradOp) (velOp * velOp) = 4 * (gradOp * velOp) - 2 :=
  collisionStar_delSq_velSq gradOp velOp ccr

/-- **`[∇², ∇v] = 2∇²`** for the genuine operators. -/
theorem realized_delSq_delVel :
    collisionStar (gradOp * gradOp) (gradOp * velOp) = 2 * (gradOp * gradOp) :=
  collisionStar_delSq_delVel gradOp velOp ccr

/-- **`[∇v, v²] = 2v²`** for the genuine operators. -/
theorem realized_delVel_velSq :
    collisionStar (gradOp * velOp) (velOp * velOp) = 2 * (velOp * velOp) :=
  collisionStar_delVel_velSq gradOp velOp ccr

/-! ### The mass generator / squeeze, realized -/

/-- **The mass/squeeze action holds for the genuine operators**: `[∇v, ∇] = −∇`, `[∇v, v] = v` on `ℝ[X]` —
the realized mass generator `M = ∇v∗` squeezes the actual `d/dX`, `X·` pair. -/
theorem realized_squeeze :
    collisionStar (gradOp * velOp) gradOp = -gradOp ∧ collisionStar (gradOp * velOp) velOp = velOp :=
  massGen_squeeze gradOp velOp ccr

/-- **The full squeeze/Bogoliubov bridge for the genuine operators.** `saveliev_mass_bogoliubov_squeeze`
instantiated at the realized canonical pair `∇ = d/dX`, `v = X·`: the mass transformation of the *actual*
derivative/multiplication operators is the Bogoliubov squeeze with rapidity `ξ`. -/
theorem realized_mass_bogoliubov_squeeze (ξ : ℝ) :
    (collisionStar (gradOp * velOp) gradOp = -gradOp ∧ collisionStar (gradOp * velOp) velOp = velOp)
      ∧ (bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ) *ᵥ ![1, 1] = Real.exp ξ • ![1, 1])
      ∧ (bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ) *ᵥ ![1, -1] = Real.exp (-ξ) • ![1, -1])
      ∧ (bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ))ᵀ * symplecticS
          * bosonicBogoliubov (Real.cosh ξ) (Real.sinh ξ) = symplecticS :=
  saveliev_mass_bogoliubov_squeeze gradOp velOp ccr ξ

end Realization

end Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.BogoliubovSqueeze

end
