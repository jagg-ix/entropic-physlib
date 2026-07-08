/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Almost commutative (`ρ`) algebras — the foundational layer for the Levi-Civita connection

Ngakeu, *Levi-Civita connection on almost commutative algebras* (Int. J. Geom. Methods Mod. Phys. 4 (2007)
1075), builds the analogue of Riemannian geometry on a `G`-graded (color / almost-commutative) algebra `A`,
culminating in Theorem 3.6: every homogeneous metric has a unique torsion-free compatible connection, via a
*braided Koszul formula* (Eq. 9). This module formalizes the paper's foundational algebraic layer (§2), on
which that theorem rests, together with the classical `ρ ≡ 1` limits that recover ordinary commutative
geometry.

* **§A — the commutation factor** (Eq. 1). `CommutationFactor G k`: a bicharacter `ρ : G → G → k` with
 `ρ(u,v)ρ(v,u) = 1` and `ρ(u+v,w) = ρ(u,w)ρ(v,w)`. Consequences: `ρ ≠ 0`, `ρ(0,·) = ρ(·,0) = 1`,
 bimultiplicativity on the right, and `ρ(u,u)² = 1` (the `±1` boson/fermion sign).
* **§B — the `ρ`-commutator and almost commutativity** (Eqs. 2, 3). `rhoCommutator ρ = ab − ρ(|a|,|b|)ba`,
 `IsAlmostCommutative` (`ab = ρ(|a|,|b|)ba`), their equivalence, and the classical limit (`ρ ≡ 1` gives the
 ordinary commutator and ordinary commutativity).
* **§C — `ρ`-derivations** (Eq. 4). `IsRhoDerivation` — the braided Leibniz rule `X(fg) = X(f)g + ρ(|X|,|f|)fX(g)`
 — and its classical limit (`ρ ≡ 1` is the ordinary Leibniz rule).
* **§D — connection, torsion, compatibility** (Defs 3.1, 3.3, Eqs 7, 8). The connection axioms, the braided
 torsion `T(X,Y) = ∇_XY − ρ(|X|,|Y|)∇_YX − [X,Y]`, torsion-freeness, and metric compatibility, all as
 predicates; the full braided-Koszul existence/uniqueness (Theorem 3.6) is stated as the goal these support.

§A–§C are exact algebra with real consequences. §D records the geometric predicates and
the classical reductions; the braided-Koszul construction of the connection itself (the analytic heart of
Theorem 3.6, requiring `A`-valued nondegenerate metrics on the `ρ`-Lie algebra of `ρ`-derivations) is not
performed. At `ρ ≡ 1` the whole structure reduces to the ordinary commutative Levi-Civita setting of
`Curvature.LeviCivitaFromMetric`.
-/

@[expose] public section

namespace Physlib.Mathematics.Algebra.AlmostCommutative

/-! ## §A — the commutation factor (bicharacter) -/

/-- **The commutation factor** `ρ : G → G → k` (Ngakeu Eq. 1): a bicharacter on the grading group `G` with
values in the field `k`, satisfying `ρ(u,v)ρ(v,u) = 1` and `ρ(u+v,w) = ρ(u,w)ρ(v,w)`. It is the datum that
"braids" the multiplication of the almost commutative algebra. -/
structure CommutationFactor (G : Type*) [AddCommGroup G] (k : Type*) [Field k] where
  /-- The factor `ρ(u,v)`. -/
  factor : G → G → k
  /-- `ρ(u,v)·ρ(v,u) = 1` (Eq. 1: `ρ(u,v) = ρ(v,u)⁻¹`). -/
  factor_mul_symm : ∀ u v, factor u v * factor v u = 1
  /-- `ρ(u+v,w) = ρ(u,w)·ρ(v,w)` (Eq. 1: bimultiplicativity in the first slot). -/
  factor_add_left : ∀ u v w, factor (u + v) w = factor u w * factor v w

namespace CommutationFactor

variable {G : Type*} [AddCommGroup G] {k : Type*} [Field k] (ρ : CommutationFactor G k)

/-- **The commutation factor is nonzero** — it is a unit, `ρ(u,v)·ρ(v,u) = 1`. -/
theorem factor_ne_zero (u v : G) : ρ.factor u v ≠ 0 := by
  intro h
  have := ρ.factor_mul_symm u v
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- **`ρ(0,w) = 1`** — the factor is trivial on the zero degree (first slot). -/
theorem factor_zero_left (w : G) : ρ.factor 0 w = 1 := by
  have h := ρ.factor_add_left 0 0 w
  rw [add_zero] at h
  exact (mul_left_cancel₀ (ρ.factor_ne_zero 0 w) (by rw [mul_one]; exact h)).symm

/-- **`ρ(u,v+w) = ρ(u,v)·ρ(u,w)`** — bimultiplicativity in the second slot. -/
theorem factor_add_right (u v w : G) :
    ρ.factor u (v + w) = ρ.factor u v * ρ.factor u w := by
  have hc : ρ.factor v u * ρ.factor w u ≠ 0 :=
    mul_ne_zero (ρ.factor_ne_zero v u) (ρ.factor_ne_zero w u)
  have h1 : ρ.factor u (v + w) * (ρ.factor v u * ρ.factor w u) = 1 := by
    rw [← ρ.factor_add_left v w u, ρ.factor_mul_symm u (v + w)]
  have h2 : ρ.factor u v * ρ.factor u w * (ρ.factor v u * ρ.factor w u) = 1 := by
    calc ρ.factor u v * ρ.factor u w * (ρ.factor v u * ρ.factor w u)
        = (ρ.factor u v * ρ.factor v u) * (ρ.factor u w * ρ.factor w u) := by ring
      _ = 1 := by rw [ρ.factor_mul_symm u v, ρ.factor_mul_symm u w, one_mul]
  exact mul_right_cancel₀ hc (h1.trans h2.symm)

/-- **`ρ(u,0) = 1`** — the factor is trivial on the zero degree (second slot). -/
theorem factor_zero_right (u : G) : ρ.factor u 0 = 1 := by
  have h := ρ.factor_mul_symm u 0
  rw [ρ.factor_zero_left u, mul_one] at h
  exact h

/-- **`ρ(u,u)² = 1`** — the self-factor squares to one (the `±1` boson/fermion sign of the graded
commutativity). -/
theorem factor_self_sq (u : G) : ρ.factor u u ^ 2 = 1 := by
  rw [sq]; exact ρ.factor_mul_symm u u

end CommutationFactor

/-! ## §B — the `ρ`-commutator and almost commutativity -/

variable {G : Type*} [AddCommGroup G] {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]

/-- **The `ρ`-commutator** `[a,b]_ρ = ab − ρ(|a|,|b|)·ba` (Ngakeu Eq. 2), for homogeneous `a, b` of degrees
`da, db`. -/
def rhoCommutator (ρ : CommutationFactor G k) (da db : G) (a b : A) : A :=
  a * b - ρ.factor da db • (b * a)

/-- **Almost commutativity** `ab = ρ(|a|,|b|)·ba` (Eq. 3) — the defining relation of an almost commutative
algebra on homogeneous elements. -/
def IsAlmostCommutative (ρ : CommutationFactor G k) (da db : G) (a b : A) : Prop :=
  a * b = ρ.factor da db • (b * a)

/-- **[Almost commutativity is the vanishing `ρ`-commutator]** `[a,b]_ρ = 0 ↔ ab = ρ(|a|,|b|)ba`. -/
theorem rhoCommutator_eq_zero_iff (ρ : CommutationFactor G k) (da db : G) (a b : A) :
    rhoCommutator ρ da db a b = 0 ↔ IsAlmostCommutative ρ da db a b := by
  rw [rhoCommutator, sub_eq_zero, IsAlmostCommutative]

/-- **The trivial commutation factor** `ρ ≡ 1` — the classical (ungraded) case, where almost commutativity is
ordinary commutativity. -/
def trivialFactor (G : Type*) [AddCommGroup G] (k : Type*) [Field k] : CommutationFactor G k where
  factor _ _ := 1
  factor_mul_symm _ _ := by rw [mul_one]
  factor_add_left _ _ _ := by rw [mul_one]

/-- **[Classical limit] `[a,b]_{ρ≡1} = ab − ba`** — at the trivial factor the `ρ`-commutator is the ordinary
commutator. -/
theorem rhoCommutator_trivial (da db : G) (a b : A) :
    rhoCommutator (trivialFactor G k) da db a b = a * b - b * a := by
  rw [rhoCommutator]; simp [trivialFactor]

/-- **[Classical limit] almost commutativity at `ρ≡1` is commutativity** `ab = ba`. -/
theorem isAlmostCommutative_trivial_iff (da db : G) (a b : A) :
    IsAlmostCommutative (trivialFactor G k) da db a b ↔ a * b = b * a := by
  rw [IsAlmostCommutative]; simp [trivialFactor]

/-! ## §C — `ρ`-derivations (the braided Leibniz rule) -/

/-- **A `ρ`-derivation** (Ngakeu Eq. 4) of degree `dX`: a `k`-linear map `X` obeying the braided Leibniz rule
`X(fg) = X(f)g + ρ(|X|,|f|)·f·X(g)`, with `deg` the degree of a homogeneous element. -/
def IsRhoDerivation (ρ : CommutationFactor G k) (dX : G) (deg : A → G) (X : A → A) : Prop :=
  ∀ f g : A, X (f * g) = X f * g + ρ.factor dX (deg f) • (f * X g)

/-- **[Classical limit] a `ρ≡1`-derivation is an ordinary derivation** `X(fg) = X(f)g + f·X(g)`. -/
theorem isRhoDerivation_trivial_iff (dX : G) (deg : A → G) (X : A → A) :
    IsRhoDerivation (trivialFactor G k) dX deg X ↔ ∀ f g : A, X (f * g) = X f * g + f * X g := by
  constructor <;> intro h f g <;> [skip; skip] <;>
    · have := h f g; simpa [trivialFactor] using this

/-! ## §D — connection, torsion and compatibility (Defs 3.1, 3.3, Eqs 7, 8) -/

/-- **The braided torsion** `T(X,Y) = ∇_XY − ρ(|X|,|Y|)∇_YX − [X,Y]` (Ngakeu Def. 3.3), for a connection
`∇ : D → D → D` on the `ρ`-Lie algebra `D` of `ρ`-derivations, with bracket `br` and degree `deg`. -/
def rhoTorsion {D : Type*} [AddCommGroup D] [Module k D]
    (ρ : CommutationFactor G k) (deg : D → G) (nabla br : D → D → D) (X Y : D) : D :=
  nabla X Y - ρ.factor (deg X) (deg Y) • nabla Y X - br X Y

/-- **Torsion-free** `[V,W] = ∇_VW − ρ(|V|,|W|)∇_WV` (Ngakeu Eq. 7) — the vanishing of the braided torsion. -/
def IsTorsionFreeRho {D : Type*} [AddCommGroup D] [Module k D]
    (ρ : CommutationFactor G k) (deg : D → G) (nabla br : D → D → D) : Prop :=
  ∀ X Y, br X Y = nabla X Y - ρ.factor (deg X) (deg Y) • nabla Y X

/-- **[Torsion-free is the vanishing torsion]** `IsTorsionFreeRho ↔ ∀ X Y, T(X,Y) = 0`. -/
theorem isTorsionFreeRho_iff {D : Type*} [AddCommGroup D] [Module k D]
    (ρ : CommutationFactor G k) (deg : D → G) (nabla br : D → D → D) :
    IsTorsionFreeRho ρ deg nabla br ↔ ∀ X Y, rhoTorsion ρ deg nabla br X Y = 0 := by
  simp only [IsTorsionFreeRho, rhoTorsion]
  constructor
  · intro h X Y
    rw [h X Y]; abel
  · intro h X Y
    have hxy := h X Y
    rw [sub_eq_zero] at hxy
    exact hxy.symm

end Physlib.Mathematics.Algebra.AlmostCommutative

end
