/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The York canonical basis: conformal/tidal split & the York time (Lusanna 2015, §4)

Formalizes the geometric kernel of Lusanna's **York canonical basis** (§4, Eq 4.1) — the canonical
transformation diagonalizing the **York–Lichnerowicz** approach — continuing `CanonicalTetradGravity.TetradADMGravity` (the
tetrad metric, the constraints) and `NonHermitianComplexAction.DiracConstraints` (the Dirac constraint algebra).

In the York basis the `3`-metric of the instantaneous `3`-space splits into a **conformal (scale)** factor `φ̃`
and a **unimodular (shape / tidal)** part (Eq 4.1):

  `³g_rs = φ̃^{2/3} Σ_a V_ra V_sa Q_a²`,   `Q_a = exp(Σ_ā γ_āa R_ā)`,

where `R_ā` are the *tidal* variables (the two gravitational-wave polarizations) and `γ_āa` the York-map
numerical parameters satisfying `Σ_a γ_āa = 0`, `Σ_a γ_āa γ_ja = δ_āj` (Lusanna ref. [5]). The key facts:

* the tidal part is **unimodular** `Π_a Q_a = 1` — *because* `Σ_a γ_āa = 0` (`tidal_unimodular`); the conformal
  factor `φ̃` includes the *entire* `3`-volume, `det ³g = φ̃²` (`conformal_det_three`), the shape/scale split;
* the **York time** `³K = tr K` is the **momentum conjugate to the conformal factor**, `π_φ̃ = (12πG/c)³K`
  (`yorkConjugateMomentum`, `york_momentum_eq_yorkTime`) — Lusanna's single inertial gauge variable
  (clock synchronization), tying back to `CanonicalTetradGravity.TetradADMGravity.yorkTime`;
* the tidal variables are **recoverable** from the shape via the York-map orthonormality
  (`tidal_recover`) — the `R_ā` are the genuine (Dirac-observable, tidal) degrees of freedom.

* **§A — the York-map parameters** (`YorkGammaOrtho`). The `Σγ=0`, `Σγγ=δ` conditions.
* **§B — the conformal/tidal split** (`tidalLog`, `tidalFactor`, `tidal_unimodular`, `tidal_recover`).
* **§C — the `3`-metric determinant & the York time** (`conformal_det`, `conformal_det_three`,
  `yorkConjugateMomentum`, `york_momentum_eq_yorkTime`).

The full Hamilton equations of the York basis, the explicit Shanmugadhasan/tidal canonical pairs and the
Hamiltonian Post-Minkowskian linearization are the analytic/dynamical layer; the conformal/tidal kinematic
kernel is formalized here.

## References

* L. Lusanna, IJGMMP 12 (2015) 1530001, §4 (the York canonical basis Eq 4.1, the York–Lichnerowicz conformal
  decomposition, `π_φ̃ = (12πG/c)³K`).
* Repo structure: `CanonicalTetradGravity.TetradADMGravity` (`yorkTime = tr K`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis

open Finset
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

variable {m n : ℕ}

/-! ## §A — the York-map parameters -/

/-- **[Lusanna ref. 5] The York-map parameters `γ_āa`** — `m` tidal indices `ā` over `n` spatial `a`, with
`Σ_a γ_āa = 0` (the unimodularity condition) and `Σ_a γ_āa γ_ja = δ_āj` (orthonormality). -/
structure YorkGammaOrtho (γ : Fin m → Fin n → ℝ) : Prop where
  /-- `Σ_a γ_āa = 0`. -/
  sum_zero : ∀ ā, ∑ a : Fin n, γ ā a = 0
  /-- `Σ_a γ_āa γ_ja = δ_āj`. -/
  ortho : ∀ ā j, ∑ a : Fin n, γ ā a * γ j a = if ā = j then 1 else 0

/-! ## §B — the conformal/tidal split -/

/-- **The tidal exponent** `Σ_ā γ_āa R_ā` — the logarithm of the tidal factor `Q_a`. -/
def tidalLog (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (a : Fin n) : ℝ :=
  ∑ ā : Fin m, γ ā a * R ā

/-- **The tidal factor** `Q_a = exp(Σ_ā γ_āa R_ā)** — the shape part of the `3`-metric eigenvalue, with
the tidal (gravitational-wave) variables `R_ā`. -/
noncomputable def tidalFactor (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (a : Fin n) : ℝ :=
  Real.exp (tidalLog γ R a)

/-- **[York–Lichnerowicz, the tidal part is unimodular] `Π_a Q_a = 1`.** Because `Σ_a γ_āa = 0`, the product
of the tidal factors is `1`: the tidal (shape) degrees of freedom encode *no* `3`-volume — the entire volume
is in the conformal factor `φ̃`. -/
theorem tidal_unimodular (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ)
    (hγ : YorkGammaOrtho γ) : ∏ a : Fin n, tidalFactor γ R a = 1 := by
  unfold tidalFactor tidalLog
  rw [← Real.exp_sum, Finset.sum_comm]
  have : ∑ ā : Fin m, ∑ a : Fin n, γ ā a * R ā = 0 := by
    apply Finset.sum_eq_zero; intro ā _; rw [← Finset.sum_mul, hγ.sum_zero ā, zero_mul]
  rw [this, Real.exp_zero]

/-- **[The tidal variables are recoverable] `Σ_a γ_ja (log Q_a) = R_j`.** Via the orthonormality
`Σ_a γ_āa γ_ja = δ_āj`, the tidal `R_ā` (the GW polarizations) are recovered from the shape — they are the
genuine dynamical (tidal) degrees of freedom. -/
theorem tidal_recover (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (hγ : YorkGammaOrtho γ) (j : Fin m) :
    ∑ a : Fin n, γ j a * tidalLog γ R a = R j := by
  unfold tidalLog
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ ā : Fin m, ∑ a : Fin n, γ j a * (γ ā a * R ā) = (if ā = j then 1 else 0) * R ā := by
    intro ā
    rw [← hγ.ortho ā j, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [Finset.sum_congr rfl fun ā _ => h ā]
  simp [Finset.sum_ite_eq']

/-! ## §C — the `3`-metric determinant and the York time -/

/-- **[The conformal factor includes the volume] `det ³g = (φ̃^{2/3})^n`.** The `3`-metric eigenvalues are
`φ̃^{2/3} Q_a²`; since the tidal part is unimodular (`tidal_unimodular`), their product is `(φ̃^{2/3})^n`. -/
theorem conformal_det (φ : ℝ) (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (hγ : YorkGammaOrtho γ) :
    ∏ a : Fin n, (φ ^ ((2 : ℝ) / 3) * tidalFactor γ R a ^ 2) = (φ ^ ((2 : ℝ) / 3)) ^ n := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow, tidal_unimodular γ R hγ, one_pow, mul_one]

/-- **[`det ³g = φ̃²` in `3` dimensions] `Π_a (φ̃^{2/3} Q_a²) = φ̃²`.** For the physical `3`-space (`n = 3`) the
conformal factor `φ̃` is exactly the square root of the `3`-volume — `φ̃ = √(det ³g)`. -/
theorem conformal_det_three (φ : ℝ) (hφ : 0 ≤ φ) (γ : Fin 3 → Fin 3 → ℝ) (R : Fin 3 → ℝ)
    (hγ : YorkGammaOrtho γ) :
    ∏ a : Fin 3, (φ ^ ((2 : ℝ) / 3) * tidalFactor γ R a ^ 2) = φ ^ (2 : ℝ) := by
  rw [conformal_det φ γ R hγ, ← Real.rpow_natCast (φ ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hφ]
  norm_num

/-- **[York time = momentum conjugate to the conformal factor] `π_φ̃ = (12πG/c)³K`.** Lusanna Eq 4.1: the
momentum conjugate to `φ̃` is the York time `³K` (up to `12πG/c`); the single inertial gauge variable. -/
noncomputable def yorkConjugateMomentum (G c K3 : ℝ) : ℝ := 12 * Real.pi * G / c * K3

/-- **The conjugate momentum is the York time `tr K`** — `π_φ̃ = (12πG/c)·tr K`, tying to
`CanonicalTetradGravity.TetradADMGravity.yorkTime` (the trace of the extrinsic curvature). -/
theorem york_momentum_eq_yorkTime {d : ℕ} (G c : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    yorkConjugateMomentum G c (yorkTime K) = 12 * Real.pi * G / c * Matrix.trace K := by
  rw [yorkConjugateMomentum, yorkTime]

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis

end
