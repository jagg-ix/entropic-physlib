/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Algebra.AlmostCommutative
public import Mathlib.Data.ZMod.Basic

/-!
# The super-algebra instance of an almost commutative (`ρ`) algebra

Ngakeu's almost commutative algebras (`Physlib.Mathematics.Algebra.AlmostCommutative`) specialize, at the
grading group `G = ℤ₂` and the sign commutation factor `ρ(a,b) = (−1)^{ab}`, to the **super-algebras**: the
`ρ`-commutator of two *odd* (degree-`1`) elements is the **anticommutator** `ab + ba`, the fermionic relation,
while for even elements it is the ordinary commutator. This is the `G = ℤ₂` face of the `±1` sign
`ρ(u,u)² = 1` (`CommutationFactor.factor_self_sq`) — the boson/fermion dichotomy the rest of the library
carries through `QFT…FieldStatistic`, the CAR algebra, and the Sorkin–Johnston exchange spectrum
(`ribbonTwist`, boson `+1` / fermion `−1`). The other extreme `ρ ≡ 1` (`trivialFactor`) recovers ordinary
commutative geometry and the Levi-Civita connection of `Curvature.LeviCivitaFromMetric`.

* `superSign` — the sign character `(−1)^{x}` on `ℤ₂`, with `superSign_add` (a group homomorphism to `k`).
* `superCommutationFactor` — the ℤ₂ sign factor `ρ(a,b) = (−1)^{ab}`.
* `rhoCommutator_super_odd` — odd × odd: the anticommutator `ab + ba` (fermions).
* `rhoCommutator_super_even_left` — even × anything: the ordinary commutator `ab − ba` (bosons).
* `isAlmostCommutative_super_odd_iff` — odd elements *anticommute*: `ab = −ba`.
-/

@[expose] public section

namespace Physlib.Mathematics.Algebra.AlmostCommutative

variable {A : Type*} [Ring A] {k : Type*} [Field k] [Algebra k A]

/-- **The `ℤ₂` sign character** `superSign x = (−1)^{x.val}` — the values `+1` (even/boson) and `−1`
(odd/fermion). -/
def superSign (k : Type*) [Field k] (x : ZMod 2) : k := (-1 : k) ^ x.val

lemma superSign_one (k : Type*) [Field k] : superSign k 1 = -1 := by
  unfold superSign; rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

lemma superSign_zero (k : Type*) [Field k] : superSign k 0 = 1 := by
  unfold superSign; rw [show (0 : ZMod 2).val = 0 from rfl, pow_zero]

/-- **The sign character squares to one** `superSign x · superSign x = 1` — the `±1` boson/fermion sign. -/
lemma superSign_mul_self (k : Type*) [Field k] (x : ZMod 2) : superSign k x * superSign k x = 1 := by
  unfold superSign
  rw [← pow_add, ← two_mul]
  exact Even.neg_one_pow (even_two_mul x.val)

/-- **The sign character is additive** `superSign (x+y) = superSign x · superSign y` — the `ℤ₂ → k` sign
homomorphism, from the 2-periodicity of `(−1)^n`. -/
lemma superSign_add (k : Type*) [Field k] (x y : ZMod 2) :
    superSign k (x + y) = superSign k x * superSign k y := by
  unfold superSign
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) 2, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **The super (ℤ₂) commutation factor** `ρ(a,b) = (−1)^{ab}`: `ρ(1,1) = −1` and `ρ = 1` otherwise — the sign
rule of a super-algebra, an instance of `CommutationFactor` on `G = ℤ₂`. -/
def superCommutationFactor (k : Type*) [Field k] : CommutationFactor (ZMod 2) k where
  factor a b := superSign k (a * b)
  factor_mul_symm a b := by
    show superSign k (a * b) * superSign k (b * a) = 1
    rw [mul_comm b a]; exact superSign_mul_self k (a * b)
  factor_add_left a b c := by
    show superSign k ((a + b) * c) = superSign k (a * c) * superSign k (b * c)
    rw [add_mul, superSign_add]

@[simp] lemma superCommutationFactor_odd (k : Type*) [Field k] :
    (superCommutationFactor k).factor 1 1 = (-1 : k) := by
  show superSign k (1 * 1) = -1
  rw [mul_one, superSign_one]

@[simp] lemma superCommutationFactor_even_left (k : Type*) [Field k] (b : ZMod 2) :
    (superCommutationFactor k).factor 0 b = (1 : k) := by
  show superSign k (0 * b) = 1
  rw [zero_mul, superSign_zero]

/-- **[Odd × odd is the anticommutator] `[a,b]_ρ = ab + ba`** — two fermionic (degree-`1`) elements: the super
`ρ`-commutator is the CAR-algebra anticommutator, since `ρ(1,1) = −1`. -/
lemma rhoCommutator_super_odd (a b : A) :
    rhoCommutator (superCommutationFactor k) 1 1 a b = a * b + b * a := by
  rw [rhoCommutator, superCommutationFactor_odd, neg_one_smul, sub_neg_eq_add]

/-- **[Even × anything is the ordinary commutator] `[a,b]_ρ = ab − ba`** — a bosonic (degree-`0`) element. -/
lemma rhoCommutator_super_even_left (db : ZMod 2) (a b : A) :
    rhoCommutator (superCommutationFactor k) 0 db a b = a * b - b * a := by
  rw [rhoCommutator, superCommutationFactor_even_left, one_smul]

/-- **[Odd elements anticommute] `ab = −ba`** — super almost-commutativity of two fermions. -/
lemma isAlmostCommutative_super_odd_iff (a b : A) :
    IsAlmostCommutative (superCommutationFactor k) 1 1 a b ↔ a * b = -(b * a) := by
  rw [IsAlmostCommutative, superCommutationFactor_odd, neg_one_smul]

end Physlib.Mathematics.Algebra.AlmostCommutative

end
