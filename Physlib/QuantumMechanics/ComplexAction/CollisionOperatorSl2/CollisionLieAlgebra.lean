/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

/-!
# The seven-dimensional Lie algebra of the linear Boltzmann collision operator (Saveliev 1996, §V)

The Lie algebra of transformations of the collision operator (*V. Saveliev, J. Math. Phys. 37 (1996)
6139*, §V, Eqs. 32–35, Table I). The seven generators

  `P₁ = ∇∗∇∗/√8, P₂ = ∇∗v∗/2, P₃ = v∗v∗/√8,  Q₁ = ∇²∗/√8, Q₂ = (v∇)∗/2, Q₃ = v²∗/√8,  S`

(built from the `*`-calculus of `CollisionOperatorSl2.LinearBoltzmannOperator`) close into a 7-dimensional Lie algebra
with the structure constants of Table I. We encode the bracket on the basis `Fin 7`
(`0,1,2 = P₁,P₂,P₃`, `3,4,5 = Q₁,Q₂,Q₃`, `6 = S`) over `ℤ` and verify, by decision procedure:

* **antisymmetry** `[A_i, A_j] = −[A_j, A_i]` (`lieBracket_antisymm`);
* **the Jacobi identity** `[A_i,[A_j,A_k]] + [A_j,[A_k,A_i]] + [A_k,[A_i,A_j]] = 0` (`lieBracket_jacobi`)
  — so the structure constants of Table I genuinely define a Lie algebra;
* the explicit **commutation relations** of Eqs. 33 and 35: the `P`'s commute (abelian ideal `AP`), `S` is
  the grading element `[S, P_k] = P_k`, `[S, Q_k] = 0`.

The metric `b` of Eq. 34 (antidiagonal, `b² = 1`) underlies the `so(2,1)` structure of the `Q`-subalgebra.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionLieAlgebra

/-! ## §A — the metric `b` of Eq. 34 (antidiagonal, `b² = 1`) -/

/-- **[Saveliev Eq. 34] The antidiagonal metric** `b = [[0,0,1],[0,−1,0],[1,0,0]]` underlying the
`so(2,1)` structure of the `Q`-subalgebra. -/
def bMetric : Fin 3 → Fin 3 → ℤ
  | 0, 2 => 1
  | 1, 1 => -1
  | 2, 0 => 1
  | _, _ => 0

/-- **`b` is symmetric** (`b̃ = b`, Eq. 34). -/
theorem bMetric_symm (l m : Fin 3) : bMetric l m = bMetric m l := by
  fin_cases l <;> fin_cases m <;> rfl

/-- **`b² = 1`** (Eq. 34): `∑_l b_{il} b_{lj} = δ_{ij}`. -/
theorem bMetric_mul_self (i j : Fin 3) :
    ∑ l, bMetric i l * bMetric l j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide

/-! ## §B — the structure constants of Table I (the seven-dimensional Lie algebra) -/

/-- **[Saveliev Table I] The Lie bracket on the basis** `A₀..A₆ = P₁,P₂,P₃,Q₁,Q₂,Q₃,S`, returning the
coefficient vector of `[A_i, A_j]`. Each bracket is a single basis element (with coefficient `±1`) or `0`,
exactly as tabulated in Table I. -/
def lieBracket : Fin 7 → Fin 7 → (Fin 7 → ℤ)
  -- [P₁, ·]
  | 0, 4 => Pi.single 0 1      -- [P₁,Q₂] = P₁
  | 0, 5 => Pi.single 1 1      -- [P₁,Q₃] = P₂
  | 0, 6 => Pi.single 0 (-1)   -- [P₁,S]  = −P₁
  -- [P₂, ·]
  | 1, 3 => Pi.single 0 (-1)   -- [P₂,Q₁] = −P₁
  | 1, 5 => Pi.single 2 1      -- [P₂,Q₃] = P₃
  | 1, 6 => Pi.single 1 (-1)   -- [P₂,S]  = −P₂
  -- [P₃, ·]
  | 2, 3 => Pi.single 1 (-1)   -- [P₃,Q₁] = −P₂
  | 2, 4 => Pi.single 2 (-1)   -- [P₃,Q₂] = −P₃
  | 2, 6 => Pi.single 2 (-1)   -- [P₃,S]  = −P₃
  -- [Q₁, ·]
  | 3, 1 => Pi.single 0 1      -- [Q₁,P₂] = P₁
  | 3, 2 => Pi.single 1 1      -- [Q₁,P₃] = P₂
  | 3, 4 => Pi.single 3 1      -- [Q₁,Q₂] = Q₁
  | 3, 5 => Pi.single 4 1      -- [Q₁,Q₃] = Q₂
  -- [Q₂, ·]
  | 4, 0 => Pi.single 0 (-1)   -- [Q₂,P₁] = −P₁
  | 4, 2 => Pi.single 2 1      -- [Q₂,P₃] = P₃
  | 4, 3 => Pi.single 3 (-1)   -- [Q₂,Q₁] = −Q₁
  | 4, 5 => Pi.single 5 1      -- [Q₂,Q₃] = Q₃
  -- [Q₃, ·]
  | 5, 0 => Pi.single 1 (-1)   -- [Q₃,P₁] = −P₂
  | 5, 1 => Pi.single 2 (-1)   -- [Q₃,P₂] = −P₃
  | 5, 3 => Pi.single 4 (-1)   -- [Q₃,Q₁] = −Q₂
  | 5, 4 => Pi.single 5 (-1)   -- [Q₃,Q₂] = −Q₃
  -- [S, ·]
  | 6, 0 => Pi.single 0 1      -- [S,P₁]  = P₁
  | 6, 1 => Pi.single 1 1      -- [S,P₂]  = P₂
  | 6, 2 => Pi.single 2 1      -- [S,P₃]  = P₃
  | _, _ => 0

/-- **Antisymmetry** `[A_i, A_j] = −[A_j, A_i]` — Table I is antisymmetric. -/
theorem lieBracket_antisymm (i j : Fin 7) : lieBracket i j = -lieBracket j i := by
  fin_cases i <;> fin_cases j <;> decide

/-- **Self-bracket vanishes** `[A_i, A_i] = 0`. -/
theorem lieBracket_self (i : Fin 7) : lieBracket i i = 0 := by
  fin_cases i <;> decide

set_option maxHeartbeats 4000000 in
/-- **[Saveliev Eq. 32–35] The Jacobi identity** for the Table I structure constants:
`[A_i,[A_j,A_k]] + [A_j,[A_k,A_i]] + [A_k,[A_i,A_j]] = 0`, where `[A_i, v] := ∑_l v_l [A_i, A_l]` extends
the bracket linearly. The bracket of Table I therefore genuinely defines a 7-dimensional Lie algebra. -/
theorem lieBracket_jacobi (i j k : Fin 7) :
    (∑ l, lieBracket j k l • lieBracket i l)
      + (∑ l, lieBracket k i l • lieBracket j l)
      + (∑ l, lieBracket i j l • lieBracket k l) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-! ## §C — the explicit commutation relations of Eqs. 33, 35 -/

/-- **[Eq. 33] The `P`'s form an abelian ideal `AP`**: `[P_i, P_k] = 0`. -/
theorem lieBracket_P_P (i k : Fin 3) :
    lieBracket (i.castLE (by omega)) (k.castLE (by omega)) = 0 := by
  fin_cases i <;> fin_cases k <;> decide

/-- **[Eq. 33] `S` is the grading element on `P`**: `[S, P_k] = P_k`. -/
theorem lieBracket_S_P1 : lieBracket 6 0 = Pi.single 0 1 := by decide
theorem lieBracket_S_P2 : lieBracket 6 1 = Pi.single 1 1 := by decide
theorem lieBracket_S_P3 : lieBracket 6 2 = Pi.single 2 1 := by decide

/-- **[Eq. 33] `S` annihilates `Q`**: `[S, Q_k] = 0`. -/
theorem lieBracket_S_Q (k : Fin 3) :
    lieBracket 6 (⟨k + 3, by omega⟩) = 0 := by
  fin_cases k <;> decide

/-! ## §D — dimensional grading and Eq. 27 (the temperature/mass generators commute)

**Dimensional analysis.** With `∇ ~ velocity⁻¹` and `v ~ velocity`, the star map `∗ = ad` preserves the
velocity dimension of its subscript, so the generators include the velocity *degrees*

  `P₁ = ∇∗∇∗, Q₁ = ∇²∗ ↦ −2`,  `P₃ = v∗v∗, Q₃ = v²∗ ↦ +2`,  `P₂ = ∇∗v∗, Q₂ = (v∇)∗, S ↦ 0`.

The collision-operator Lie algebra is **graded** by this degree: `[A_i, A_j]` has degree `deg i + deg j`
(`lieBracket_graded`) — the dimensional consistency of Table I. The mass generator
`M = ∇v∗ = S + Q₂ + P₂` (Eq. 32, since `S = M − Q₂ − P₂`) has degree `0`, so `[M, ∇∗∇∗]` has degree `−2`:
**dimensional analysis forces `[∇∗∇∗, ∇v∗] = c·∇∗∇∗`** (the only degree `−2` generators are `P₁, Q₁`), and
Table I pins `c = 0` (`temperature_mass_commute`). -/

/-- **The velocity-dimension grading** (degree): `P₁,Q₁ ↦ −2`, `P₃,Q₃ ↦ +2`, `P₂,Q₂,S ↦ 0`. -/
def degree : Fin 7 → ℤ
  | 0 => -2  -- P₁ = ∇∗∇∗
  | 1 => 0   -- P₂ = ∇∗v∗
  | 2 => 2   -- P₃ = v∗v∗
  | 3 => -2  -- Q₁ = ∇²∗
  | 4 => 0   -- Q₂ = (v∇)∗
  | 5 => 2   -- Q₃ = v²∗
  | 6 => 0   -- S

/-- **The Lie bracket is dimensionally graded**: every nonzero structure constant `[A_i,A_j]_k` satisfies
`deg k = deg i + deg j`. This is the dimensional consistency of Saveliev's collision-operator algebra —
the velocity-degree grading underlying the dimensional analysis of the generators. -/
theorem lieBracket_graded (i j k : Fin 7) (h : lieBracket i j k ≠ 0) :
    degree k = degree i + degree j := by
  revert h; fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The **mass generator** `M = ∇v∗ = S + Q₂ + P₂` (Saveliev Eq. 32, `S = M − Q₂ − P₂`), as a coefficient
vector in the basis `A₀..A₆`. -/
def massGen : Fin 7 → ℤ := Pi.single 6 1 + Pi.single 4 1 + Pi.single 1 1

/-- **[Saveliev Eq. 27] The temperature and mass generators commute** `[∇∗∇∗, ∇v∗] = 0`. Constructed from
Table I: writing the mass generator `M = ∇v∗ = S + Q₂ + P₂`, its bracket with the temperature generator
`P₁ = ∇∗∇∗` is `[M, P₁] = [S, P₁] + [Q₂, P₁] + [P₂, P₁] = P₁ + (−P₁) + 0 = 0` — the `S`-grading
(`[S,P₁] = P₁`) and the `Q₂`-action (`[Q₂,P₁] = −P₁`) cancel. (The naive `ad_{∇·v}` gives the coefficient
`2`; the *correct* mass generator is the combination `S + Q₂ + P₂`, for which dimensional analysis allows
any `c·∇∗∇∗` and Table I selects `c = 0`.) -/
theorem temperature_mass_commute :
    lieBracket 6 0 + lieBracket 4 0 + lieBracket 1 0 = 0 := by decide

/-- **[Saveliev Eq. 27, vector form]** The same commutator written via the mass-generator vector
`M = S + Q₂ + P₂`: `[M, P₁] = ∑_i M_i [A_i, P₁] = 0`. -/
theorem massGen_temperature_commute :
    (∑ i, massGen i • lieBracket i 0) = 0 := by decide

/-! ## §E — the full `M`-relations (Eq. 35) and the affine subalgebra (Eq. 46) -/

/-- **[Saveliev Eq. 35] `[M, P₂] = P₂`** — the mass generator scales `P₂` by its degree. -/
theorem massGen_P2 : (∑ i, massGen i • lieBracket i 1) = Pi.single 1 1 := by decide

/-- **[Saveliev Eq. 35] `[M, P₃] = 2P₃`** — degree `+2`. -/
theorem massGen_P3 : (∑ i, massGen i • lieBracket i 2) = Pi.single 2 2 := by decide

/-- **[Saveliev Eq. 35] `[M, Q₁] = −Q₁ − P₁`**. -/
theorem massGen_Q1 :
    (∑ i, massGen i • lieBracket i 3) = Pi.single 3 (-1) + Pi.single 0 (-1) := by decide

/-- **[Saveliev Eq. 35] `[M, Q₂] = 0`**. -/
theorem massGen_Q2 : (∑ i, massGen i • lieBracket i 4) = 0 := by decide

/-- **[Saveliev Eq. 35] `[M, Q₃] = Q₃ + P₃`**. -/
theorem massGen_Q3 :
    (∑ i, massGen i • lieBracket i 5) = Pi.single 5 1 + Pi.single 2 1 := by decide

/-- **[Saveliev Eq. 46] The affine `ax+b` subalgebra `{M, P₂}`**: `[Q₂, M] = 0`, `[Q₂, P₂] = 0`, and
`[M, P₂] = P₂` (`massGen_P2`) — `Q₂` commutes with both `M` and `P₂`, while `M` scales `P₂`, the
generators of the affine subgroup (Eqs. 47–48). -/
theorem Q2_massGen_commute : (∑ j, massGen j • lieBracket 4 j) = 0 := by decide

theorem Q2_P2_commute : lieBracket 4 1 = 0 := by decide

/-! ## §F — the `so(2,1)` structure of the `Q`-subalgebra (Eq. 33 via Levi-Civita and `b`) -/

/-- The Levi-Civita symbol on `Fin 3` (`ε₀₁₂ = 1`). -/
def leviCivita3 : Fin 3 → Fin 3 → Fin 3 → ℤ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | 1, 0, 2 => -1
  | _, _, _ => 0

/-- **[Saveliev Eq. 33] The `so(2,1)` structure constant** `c_{ikm} = ∑_l ε_{ikl} b_{lm}` (Levi-Civita
twisted by the antidiagonal metric `b`). -/
def qStruct (i k m : Fin 3) : ℤ := ∑ l, leviCivita3 i k l * bMetric l m

/-- Index of `Q_i` in `Fin 7` (`Q₁,Q₂,Q₃ = A₃,A₄,A₅`). -/
def qIdx (i : Fin 3) : Fin 7 := ⟨i.val + 3, by omega⟩

/-- Index of `P_i` in `Fin 7` (`P₁,P₂,P₃ = A₀,A₁,A₂`). -/
def pIdx (i : Fin 3) : Fin 7 := i.castLE (by omega)

/-- **[Saveliev Eq. 33] `[Q_i, Q_k] = ε_{ikl} b_{lm} Q_m`** — the `Q`-subalgebra is `so(2,1)`: its
`Q_m`-coefficient is the structure constant `qStruct i k m`. -/
theorem QQ_isStructConst (i k m : Fin 3) :
    lieBracket (qIdx i) (qIdx k) (qIdx m) = qStruct i k m := by
  fin_cases i <;> fin_cases k <;> fin_cases m <;> decide

/-- **[Saveliev Eq. 33] `[Q_i, P_k] = ε_{ikl} b_{lm} P_m`** — the `P`'s form the same `so(2,1)`-module as
the `Q`'s, with the identical structure constant `qStruct i k m`. -/
theorem QP_isStructConst (i k m : Fin 3) :
    lieBracket (qIdx i) (pIdx k) (pIdx m) = qStruct i k m := by
  fin_cases i <;> fin_cases k <;> fin_cases m <;> decide

end Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionLieAlgebra

end
