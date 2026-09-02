/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis

/-!
# The weak ADM energy & the York-time negative kinetic term (Alba–Lusanna 2012)

Formalizes the central physical results of *D. Alba, L. Lusanna, "The Einstein–Maxwell-particle system in the
York canonical basis of ADM tetrad gravity. Part 1", Can. J. Phys. 90 (2012) 1017* — the **tidal eigenvalue
symmetric polynomials** of the unimodular `3`-metric and the **negative kinetic term of the York time in the
weak ADM energy** (the candidate inertial origin of dark energy / back-reaction) — building on
`CanonicalTetradGravity.YorkCanonicalBasis` (the conformal/tidal split) and `CanonicalTetradGravity.TetradADMGravity` (the York time `tr K`).

In the York basis the unimodular tidal `3`-metric `³ĝ_rs` (determinant `1`) has eigenvalues `Q_a²`,
`Q_a = exp(Σ_ā γ_āa R_ā)`, and its symmetric invariants are the tidal `3`-scalars (Alba–Lusanna footnote 7):

* `Tr ³ĝ = Σ_a Q_a²` (`tidalTrace`, the first symmetric polynomial — the new tidal variable `X`);
* `det ³ĝ = Π_a Q_a² = 1` (`tidal_eigenvalue_det`, the unimodularity, third symmetric polynomial).

The Dirac Hamiltonian is weakly the **weak ADM energy** `Ê_ADM`, in which the inertial York time `³K = tr K`
(the clock-synchronization remnant, whose *time* nature reflects the Lorentz signature) enters as a
**negative** kinetic term `−a·³K²` (`yorkKineticTerm`): it is `≤ 0` (`yorkKineticTerm_nonpos`) and **vanishes
exactly in the `³K = 0` gauge** (`yorkKineticTerm_eq_zero_iff`). This sign — a genuinely general-relativistic
inertial effect absent in Newtonian gravity — is Alba–Lusanna's candidate for (part of) dark energy.

* **§A — the tidal eigenvalue symmetric polynomials** (`tidalTrace`, `tidal_eigenvalue_det`,
  `tidalTrace_minkowski`).
* **§B — the York-time negative kinetic term** (`yorkKineticTerm`, `yorkKineticTerm_nonpos`,
  `yorkKineticTerm_eq_zero_iff`, `yorkKinetic_yorkTime`).

The full weak ADM energy volume integral, the four sets of Hamilton equations (Bianchi / inertial / tidal /
matter), the transverse-EM radiation gauge and the generalized Coulomb interaction are the dynamical layer;
the eigenvalue invariants and the York-time energy sign are formalized here.

## References

* D. Alba, L. Lusanna, Can. J. Phys. 90 (2012) 1017 (the weak ADM energy, the York-time negative kinetic
  term, the tidal eigenvalue symmetric polynomials, footnote 7).
* Repo carriers: `CanonicalTetradGravity.YorkCanonicalBasis` (`tidalFactor`, `tidal_unimodular`),
  `CanonicalTetradGravity.TetradADMGravity` (`yorkTime = tr K`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.YorkADMEnergy

open Finset
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.YorkCanonicalBasis

variable {m n : ℕ}


/-- **[Alba–Lusanna footnote 7(i)] `Tr ³ĝ = Σ_a Q_a²`** — the trace of the unimodular tidal `3`-metric is the
sum of its eigenvalues `Q_a²` (`Q_a = exp(Σ_ā γ_āa R_ā)`), the first symmetric polynomial; the new tidal
`3`-scalar variable `X`. -/
noncomputable def tidalTrace (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) : ℝ :=
  ∑ a : Fin n, tidalFactor γ R a ^ 2

/-- **[det `³ĝ = 1`, unimodular] `Π_a Q_a² = 1`** — the product of the tidal eigenvalues (the third symmetric
polynomial) is `1`: the tidal part carries no `3`-volume (`tidal_unimodular`). -/
lemma tidal_eigenvalue_det (γ : Fin m → Fin n → ℝ) (R : Fin m → ℝ) (hγ : YorkGammaOrtho γ) :
    ∏ a : Fin n, tidalFactor γ R a ^ 2 = 1 := by
  rw [Finset.prod_pow, tidal_unimodular γ R hγ, one_pow]

/-- **[Minkowski background] `Tr ³ĝ = n` at `R = 0`** — at flat tidal data every eigenvalue is `Q_a² = 1`, so
the trace equals the spatial dimension. -/
lemma tidalTrace_minkowski (γ : Fin m → Fin n → ℝ) :
    tidalTrace γ 0 = (n : ℝ) := by
  unfold tidalTrace tidalFactor tidalLog
  simp [Finset.card_univ]


/-- **[Alba–Lusanna, the York-time energy] the negative kinetic term `−a·³K²`** — the inertial York time
`³K = tr K` (the clock-synchronization gauge variable) contributes to the weak ADM energy `Ê_ADM` with a
*negative* kinetic term (`a > 0`), its sign a reflex of the Lorentz signature. -/
noncomputable def yorkKineticTerm (a K3 : ℝ) : ℝ := -a * K3 ^ 2

/-- **[The York-time kinetic term is non-positive] `−a·³K² ≤ 0`** (for `a ≥ 0`) — the York time *lowers* the
weak ADM energy, a genuinely general-relativistic inertial effect. -/
lemma yorkKineticTerm_nonpos (a K3 : ℝ) (ha : 0 ≤ a) : yorkKineticTerm a K3 ≤ 0 := by
  rw [yorkKineticTerm]; nlinarith [sq_nonneg K3]

/-- **[Vanishes only in the `³K = 0` gauge] `−a·³K² = 0 ⟺ ³K = 0`** (for `a > 0`) — the negative York-time
kinetic term is absent exactly when the York time vanishes; otherwise it is strictly negative — Alba–Lusanna's
candidate inertial contribution to dark energy / back-reaction. -/
lemma yorkKineticTerm_eq_zero_iff (a K3 : ℝ) (ha : 0 < a) :
    yorkKineticTerm a K3 = 0 ↔ K3 = 0 := by
  rw [yorkKineticTerm]
  constructor
  · intro h
    have hsq : K3 ^ 2 = 0 := by nlinarith [sq_nonneg K3]
    exact pow_eq_zero_iff (by norm_num) |>.mp hsq
  · intro h; rw [h]; ring

/-- **The York-time kinetic term as a function of `tr K`** — `−a·(tr K)²`, tying the weak-ADM-energy term to
`CanonicalTetradGravity.TetradADMGravity.yorkTime` (the trace of the extrinsic curvature). -/
lemma yorkKinetic_yorkTime {d : ℕ} (a : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    yorkKineticTerm a (yorkTime K) = -a * Matrix.trace K ^ 2 := by
  rw [yorkKineticTerm, yorkTime]

end Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.YorkADMEnergy

end
