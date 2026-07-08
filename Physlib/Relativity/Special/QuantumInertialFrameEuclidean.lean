/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import Physlib.Relativity.Special.QuantumInertialFrameLorentzian
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Euclidean Quantum Inertial Frame (Wick-rotated companion)

Concrete instantiation of the operator-level
`QuantumMechanics.FiniteTarget.QuantumInertialFrame` structure on a
**Euclidean** (Wick-rotated, positive-signature) background.  The
Lorentzian sister file (`QuantumInertialFrameLorentzian.lean`) lives
on Minkowski `SpaceTime sd` with timelike / lightlike / spacelike
distinctions; here all directions are positive-definite and the
"proper distance" is the Euclidean norm `‖p − q‖` on
`EuclideanSpace ℝ (Fin (sd+1))`.

## Wick-rotation correspondence

The Lorentzian path weight `exp(i·S/ℏ) = exp(i·S_R/ℏ)·exp(−S_I/ℏ)`
becomes, after Wick rotation `t ↦ −iτ_E`,

  `exp(−S_E/ℏ)`  with  `S_E ≥ 0`,

so the **Euclidean Cameron weight** is just the imaginary-action
factor `exp(−τ_ent)` of the Lorentzian theory promoted to the *only*
suppression mechanism (no oscillatory phase).  This realises the
Wick row of the paper's Cameron table:

  | Theory | Re(A)        | Cameron condition | Measure       |
  |--------|--------------|-------------------|----------------|
  | Feynman| 0            | NO                | distributional |
  | Wick   | −S_E/ℏ < 0   | YES               | valid          |
  | complex-action/entropic-time| −S_I/ℏ < 0   | YES               | valid          |

The Euclidean QIF lives in the Wick row: the entire `S_E` is the
suppression exponent, and equilibrium QIF (zero entropic rate)
collapses the weight to `1` along that state.

## Main theorem

`euclideanCameronWeight_eq_one_at_equilibrium` — at an equilibrium
QIF state (where the QIF entropic rate `λ(ψ) = 0`), the Euclidean
Cameron weight along that state's worldline is identically `1` (no
suppression).  This is the QIF realisation of the Wick-vacuum
condition.

## Riemannian distance bridge

`euclideanDistance` — the bare Euclidean distance `‖p − q‖` on
`EuclideanSpace ℝ (Fin sd)`, used as the geometric clock for an
Euclidean QIF (Riemannian arc-length companion of Minkowski's
proper-time interval).

## References

  table.
* Cameron 1960, "The translation pathology of Wiener space",
  Duke Math. J. 27, 1.
* Constantin & Iyer 2008 — Wick-rotation / stochastic Lagrangian
  representation.
* Connes & Rovelli 1994 — equilibrium-clock identification
.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameEuclidean

open QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — Euclidean distance (Riemannian arc-length companion) -/

/-- **Euclidean distance** between two points on `EuclideanSpace ℝ (Fin sd)`:

  `d_E(q, p) := ‖p − q‖`.

This is the bare Riemannian arc-length companion of the
Lorentzian `SpaceTime.properTime` (`= √⟪p − q, p − q⟫ₘ`).  In the
positive-definite signature, every interval is "spacelike" and
`d_E ≥ 0` always. -/
def euclideanDistance {sd : ℕ}
    (q p : EuclideanSpace ℝ (Fin sd)) : ℝ :=
  ‖p - q‖

/-- The Euclidean distance is non-negative. -/
theorem euclideanDistance_nonneg {sd : ℕ}
    (q p : EuclideanSpace ℝ (Fin sd)) :
    0 ≤ euclideanDistance q p :=
  norm_nonneg _

/-- The Euclidean distance vanishes iff the two points coincide. -/
theorem euclideanDistance_eq_zero_iff {sd : ℕ}
    (q p : EuclideanSpace ℝ (Fin sd)) :
    euclideanDistance q p = 0 ↔ q = p := by
  unfold euclideanDistance
  rw [norm_eq_zero, sub_eq_zero]
  exact ⟨Eq.symm, Eq.symm⟩

/-! ## §2 — Euclidean Cameron weight from QIF entropic time -/

/-- **Euclidean Cameron weight** at QIF state `ψ`:

  `W_E(Q, ψ) := exp(−Q.entropicRate ψ)`.

The Wick-rotated companion of the Lorentzian Cameron weight
`exp(−S_I/ℏ) = exp(−τ_ent)`: in the Euclidean picture, the entire
suppression is captured by the entropic rate `λ = ⟨H_I⟩/ℏ`
evaluated at `ψ`.  Multiplied by `Δt` (parameter time) one recovers
the path-weight factor `exp(−τ_ent)` over an interval. -/
def euclideanCameronWeight (Q : QuantumInertialFrame H) (ψ : H) : ℝ :=
  Real.exp (-(Q.entropicRate ψ))

/-- The Euclidean Cameron weight is strictly positive. -/
theorem euclideanCameronWeight_pos (Q : QuantumInertialFrame H) (ψ : H) :
    0 < euclideanCameronWeight Q ψ :=
  Real.exp_pos _

/-- **Euclidean Cameron weight is bounded above by 1** — positivity of
`H_I` (non-negative entropic rate) plus monotonicity of `exp`. -/
theorem euclideanCameronWeight_le_one (Q : QuantumInertialFrame H) (ψ : H) :
    euclideanCameronWeight Q ψ ≤ 1 := by
  unfold euclideanCameronWeight
  have h_neg : -(Q.entropicRate ψ) ≤ 0 := by
    linarith [Q.entropicRate_nonneg ψ]
  exact (Real.exp_le_one_iff).mpr h_neg

/-- **Euclidean Cameron weight = 1 at equilibrium QIF.**

At an equilibrium QIF state (`λ(ψ) = 0`, i.e. `Q.IsEquilibriumAt ψ`),
the Euclidean Cameron weight collapses to `1`: there is no
exponential suppression of this state's contribution to the
Wick-rotated path integral.

This is the Euclidean-frame realisation of the QIF equilibrium
condition.  Combined with the Lorentzian main theorem
(`QuantumInertialFrameLorentzian.totalProperTime_eq_properTime_at_allTimes_equilibrium`),
it shows that equilibrium QIF is exactly the **vacuum / equilibrium**
configuration in both metric signatures:

* **Lorentzian**: total proper time = Minkowski proper time
  (no entropic contribution).
* **Euclidean**: Cameron weight = 1 (no Wick-rotated suppression). -/
theorem euclideanCameronWeight_eq_one_at_equilibrium
    (Q : QuantumInertialFrame H) {ψ : H}
    (h_eq : Q.IsEquilibriumAt ψ) :
    euclideanCameronWeight Q ψ = 1 := by
  unfold euclideanCameronWeight QuantumInertialFrame.IsEquilibriumAt at *
  rw [h_eq]
  simp

/-! ## §3 — Euclidean QIF configuration (data structure) -/

/-- A **Euclidean QIF configuration** packages a QIF with a base point
on `EuclideanSpace ℝ (Fin sd)` and a state assignment.  Unlike the
Lorentzian case (where the worldline has a `τ` parameter), the
Euclidean structure is *static*: a single base point plus the
operator-level QIF data.

For time-dependent Euclidean configurations (Wick-rotated
trajectories), parameterise by an additional `ℝ` and use the same
`euclideanCameronWeight` pointwise.  -/
structure EuclideanQIFConfiguration
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] (sd : ℕ) where
  Q        : QuantumInertialFrame H
  basePoint : EuclideanSpace ℝ (Fin sd)
  state    : H

namespace EuclideanQIFConfiguration

variable {sd : ℕ} (E : EuclideanQIFConfiguration H sd)

/-- The configuration is at **equilibrium QIF** iff its state is an
equilibrium-QIF state for its QIF data. -/
def IsEquilibrium : Prop := E.Q.IsEquilibriumAt E.state

/-- **Euclidean Cameron weight of the configuration**:
`W_E := exp(−Q.entropicRate state)`. -/
def cameronWeight : ℝ := euclideanCameronWeight E.Q E.state

/-- At equilibrium QIF, the configuration's Cameron weight is `1`. -/
theorem cameronWeight_eq_one_of_isEquilibrium
    (h_eq : E.IsEquilibrium) : E.cameronWeight = 1 :=
  euclideanCameronWeight_eq_one_at_equilibrium E.Q h_eq

end EuclideanQIFConfiguration

/-! ## §4 — Wick rotation: Lorentzian QIF → Euclidean QIF

The map `wickRotate` takes a Lorentzian QIF worldline and produces a
Euclidean QIF configuration at a chosen evaluation parameter `τ₀ : ℝ`.

**Conceptual content**: in QFT, Wick rotation `t ↦ −iτ_E` takes the
Minkowski path integral `∫ exp(iS/ℏ)` to the Euclidean
`∫ exp(−S_E/ℏ)`.  At the QIF level — where we already factor
`exp(iS/ℏ) = exp(iS_R/ℏ)·exp(−S_I/ℏ)` and the imaginary-action
factor `exp(−S_I/ℏ) = exp(−τ_ent)` is the **dissipative**
contribution — the Wick rotation is the *identity on the dissipative
sector*: the entropic-time weight `exp(−τ_ent)` survives unchanged
across `t ↦ −iτ_E`.

So the Wick rotation, at the QIF abstraction level, is the
identity-on-`(Q, state)` map that just selects an evaluation point
(parameter `τ₀`) and forgets the worldline parametrisation, replacing
it with a Euclidean base point.

The main theorem identifies the **Lorentzian Cameron weight at evaluation
time `τ₀`** with the **Euclidean Cameron weight of the Wick-rotated
configuration**: a true algebraic identity confirming
`Φ_Lorentz = Φ_Euclid` on the dissipative sector. -/

/-- **Wick rotation** of a Lorentzian QIF worldline to a Euclidean
QIF configuration, at evaluation parameter `τ₀ : ℝ`.

Maps:

* QIF data `Q` unchanged (operator-level content is metric-agnostic),
* `state τ₀` becomes the configuration's static state,
* a Euclidean base point chosen by the consumer (defaulting to `0`
  when none is supplied — Euclidean spacetime has translational
  symmetry).

The Lorentzian worldline `worldline : ℝ → SpaceTime sd` is *not*
mapped into the Euclidean structure (the two spacetime structures have
different signatures); the Euclidean base point is supplied
externally. -/
def wickRotate {sd : ℕ}
    (LQW : Physlib.Relativity.Special.QuantumInertialFrameLorentzian.LorentzianQIFWorldline H sd)
    (τ₀ : ℝ) (basePoint : EuclideanSpace ℝ (Fin sd)) :
    EuclideanQIFConfiguration H sd where
  Q         := LQW.Q
  basePoint := basePoint
  state     := LQW.state τ₀

/-- **Cameron-weight invariance under Wick rotation**.

The Euclidean Cameron weight of the Wick-rotated configuration at
parameter `τ₀` equals the Lorentzian Cameron weight
`exp(−Q.entropicRate (state τ₀))` of the original Lorentzian QIF at
parameter `τ₀`.

This is *trivial* by construction (the Wick rotation is the identity
on the dissipative sector), but stated explicitly to make the
algebraic identification a Lean-checked theorem. -/
theorem wickRotate_cameronWeight {sd : ℕ}
    (LQW : Physlib.Relativity.Special.QuantumInertialFrameLorentzian.LorentzianQIFWorldline H sd)
    (τ₀ : ℝ) (basePoint : EuclideanSpace ℝ (Fin sd)) :
    (wickRotate LQW τ₀ basePoint).cameronWeight
      = euclideanCameronWeight LQW.Q (LQW.state τ₀) := rfl

/-- **Equilibrium under Wick rotation is preserved**: the Wick-rotated
configuration is at equilibrium iff the Lorentzian QIF is at
equilibrium at the evaluation parameter `τ₀`. -/
theorem wickRotate_isEquilibrium_iff {sd : ℕ}
    (LQW : Physlib.Relativity.Special.QuantumInertialFrameLorentzian.LorentzianQIFWorldline H sd)
    (τ₀ : ℝ) (basePoint : EuclideanSpace ℝ (Fin sd)) :
    (wickRotate LQW τ₀ basePoint).IsEquilibrium
      ↔ LQW.IsEquilibriumAt τ₀ := Iff.rfl

/-- **Wick-rotated Cameron weight collapses at all-times
equilibrium** of the Lorentzian QIF.

When the source Lorentzian QIF is at all-times equilibrium (and so
trivially at equilibrium at `τ₀`), the Wick-rotated Cameron weight
collapses to `1`.

This realises, at the QIF level, the operational identity:

  *equilibrium in Minkowski ⟺ vacuum in Euclidean*.

The Wick row and the equilibrium-complex-action/entropic-time case of the paper's Cameron
table (Eq. 20) are not just two rows in a table — they are *the same
QIF state* viewed through two metric signatures, and the equilibrium
condition annihilates the dissipative contribution in both. -/
theorem wickRotate_cameronWeight_eq_one_at_allTimes_equilibrium
    {sd : ℕ}
    (LQW : Physlib.Relativity.Special.QuantumInertialFrameLorentzian.LorentzianQIFWorldline H sd)
    (h_eq : LQW.IsAllTimesEquilibrium)
    (τ₀ : ℝ) (basePoint : EuclideanSpace ℝ (Fin sd)) :
    (wickRotate LQW τ₀ basePoint).cameronWeight = 1 := by
  rw [wickRotate_cameronWeight]
  exact euclideanCameronWeight_eq_one_at_equilibrium LQW.Q (h_eq τ₀)

end Physlib.Relativity.Special.QuantumInertialFrameEuclidean

end
