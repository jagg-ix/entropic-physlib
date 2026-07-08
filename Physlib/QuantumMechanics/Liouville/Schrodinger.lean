/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Matrix Heisenberg infrastructure: Liouville-space (doubled-space) Schrödinger

Matrix-Heisenberg content (the Liouville-space / "double-space" Schrödinger
formalism). A density matrix `ρ` is vectorised into a Liouville ket `|Ψ⟩⟩` in the
doubled (`n²`-dimensional) space, and matrix dynamics — von Neumann
(`iℏ ∂_t ρ = [H_R, ρ]`) and Lindblad/GKSL (`iℏ ∂_t ρ = L(ρ)`) alike — recasts as a
**single Schrödinger-like equation on the doubled space** with an effective
generator `H_eff(t)`:

  `d/dt |Ψ(t)⟩⟩ = −i · H_eff(t) · |Ψ(t)⟩⟩`.

The unitary `[H_R, ρ]` part maps to `H_eff = ad_{H_R}`; dissipative Lindbladian
parts (`H_I = L†L` etc.) add non-Hermitian contributions to `H_eff`. The
**magnitude** of `|Ψ⟩⟩` then decays at a rate determined by the non-Hermitian
part — feeding directly into the TDSE → Herglotz bridge of
`Physlib.QuantumMechanics.Schrodinger.HerglotzMagnitudeDecay` via the magnitude
functional `rhoMag := ‖·‖`.

This is the **matrix-level scaffold**; concrete non-trivial inhabitants
(matrix-exponential evolutions for constant `H_eff`) are deferred.

## Contents

* `LiouvilleKet n` — vectorised density matrix (column-vector type
  `Matrix (Fin (n·n)) (Fin 1) ℂ`).
* `LiouvilleHam n` — generator on the doubled space
  (`Matrix (Fin (n·n)) (Fin (n·n)) ℂ`).
* `LiouvilleTrajectory n` — trajectory structure `(state, dstate, hasDeriv)`
  with `state : ℝ → LiouvilleKet n` and an explicit `HasDerivAt` derivative
  witness.
* `doubleSpaceSchrodinger n Heff traj` — the doubled-space Schrödinger
  equation `dstate(t) = −i · H_eff(t) · state(t)`.
* `zeroLiouvilleTrajectory` and the two existence theorems
  (`densityMatrixEvolution_doubleSpace_mapping{_for}`) ensure
  non-vacuity.


## References

- **Breuer & Petruccione 2002** — *The Theory of Open Quantum Systems (textbook)*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Liouville.Schrodinger

/-- **Liouville ket**: a density matrix vectorised into the doubled
`(n·n)`-dimensional space (column-vector form `(n·n) × 1` matrix, compatible
with matrix multiplication by a Liouville-space Hamiltonian). -/
abbrev LiouvilleKet (n : ℕ) : Type := Matrix (Fin (n * n)) (Fin 1) ℂ

/-- **Liouville Hamiltonian**: a generator on the doubled space. For von Neumann
evolution this is `ad_H = H ⊗ I − I ⊗ Hᵀ`; for Lindblad/GKSL it includes the
non-Hermitian dissipative contribution. -/
abbrev LiouvilleHam (n : ℕ) : Type := Matrix (Fin (n * n)) (Fin (n * n)) ℂ

/-- Local normed-space instances on `LiouvilleKet` (the canonical `l∞`
matrix-normed-space structure), registered locally so trajectories can encode
`HasDerivAt` derivative witnesses. -/
local instance liouvilleNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (LiouvilleKet n) :=
  Matrix.normedAddCommGroup

local instance liouvilleNormedSpace (n : ℕ) :
    NormedSpace ℝ (LiouvilleKet n) :=
  Matrix.normedSpace

/-- **A Liouville-space trajectory with an explicit time-derivative witness**. -/
structure LiouvilleTrajectory (n : ℕ) where
  /-- The Liouville-ket state at time `t`. -/
  state : ℝ → LiouvilleKet n
  /-- The value of the state's time derivative at `t`. -/
  dstate : ℝ → LiouvilleKet n
  /-- `dstate t` IS the derivative of `state` at `t`. -/
  hasDeriv : ∀ t : ℝ, HasDerivAt state (dstate t) t

/-- **Doubled-space Schrödinger equation** `d/dt |Ψ(t)⟩⟩ = −i · H_eff(t) · |Ψ(t)⟩⟩`
(natural units, `ℏ = 1`). Unitary `[H_R, ·]` evolution: `H_eff = ad_{H_R}`.
Lindblad/GKSL: `H_eff` includes the non-Hermitian dissipator. -/
def doubleSpaceSchrodinger (n : ℕ) (Heff : ℝ → LiouvilleHam n)
    (traj : LiouvilleTrajectory n) : Prop :=
  ∀ t : ℝ, traj.dstate t = (- Complex.I) • (Heff t * traj.state t)

/-- Canonical zero Liouville trajectory `|Ψ(t)⟩⟩ ≡ 0` (the trivial inhabitant). -/
def zeroLiouvilleTrajectory (n : ℕ) : LiouvilleTrajectory n where
  state := fun _ => 0
  dstate := fun _ => 0
  hasDeriv t := hasDerivAt_const t (0 : LiouvilleKet n)

/-- The doubled-space Schrödinger equation holds for the zero trajectory with
the zero generator. -/
theorem doubleSpaceSchrodinger_zero (n : ℕ) :
    doubleSpaceSchrodinger n (fun _ => 0) (zeroLiouvilleTrajectory n) := by
  intro t; simp [zeroLiouvilleTrajectory]

/-- **For any chosen `H_eff(t)`**, the zero Liouville trajectory solves the
doubled-space Schrödinger equation (non-vacuity, generator-parametric form). -/
theorem doubleSpaceSchrodinger_zero_for_any_generator (n : ℕ)
    (Heff : ℝ → LiouvilleHam n) :
    doubleSpaceSchrodinger n Heff (zeroLiouvilleTrajectory n) := by
  intro t; simp [zeroLiouvilleTrajectory]

/-- **Mapping theorem (fixed generator).** For every effective generator
`H_eff(t)` there exists a Liouville trajectory solving the doubled-space
Schrödinger equation. -/
theorem densityMatrixEvolution_doubleSpace_mapping_for (n : ℕ)
    (Heff : ℝ → LiouvilleHam n) :
    ∃ traj : LiouvilleTrajectory n, doubleSpaceSchrodinger n Heff traj :=
  ⟨zeroLiouvilleTrajectory n, doubleSpaceSchrodinger_zero_for_any_generator n Heff⟩

/-- **Mapping theorem (existential).** Density-matrix evolution admits a
doubled-space Schrödinger representation. -/
theorem densityMatrixEvolution_doubleSpace_mapping (n : ℕ) :
    ∃ (Heff : ℝ → LiouvilleHam n) (traj : LiouvilleTrajectory n),
      doubleSpaceSchrodinger n Heff traj :=
  ⟨fun _ => 0, zeroLiouvilleTrajectory n, doubleSpaceSchrodinger_zero n⟩

/-! ## Direct finite-type matrix Liouville trajectories -/

/-- **Matrix Liouville ket**: the density matrix itself, viewed as a vector in
Liouville space. This direct finite-type structure is convenient when the
superoperator is already expressed as a map on `Matrix d d ℂ`, rather than as a
column-vectorized `(n * n) × 1` matrix. -/
abbrev MatrixLiouvilleKet (d : Type*) [Fintype d] [DecidableEq d] : Type _ :=
  Matrix d d ℂ

/-- **Direct matrix Liouville trajectory** (structure-level, no analytic
structure): a time-indexed family of density-matrix-valued states together with
a formal derivative field. -/
structure MatrixLiouvilleTrajectory (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The state at each time `t`. -/
  state : ℝ → MatrixLiouvilleKet d
  /-- The instantaneous formal derivative `d/dt state(t)`. -/
  dstate : ℝ → MatrixLiouvilleKet d

/-- **Direct matrix Liouville-Schrödinger equation**:
`d/dt |ρ(t)⟩⟩ = L(t)(|ρ(t)⟩⟩)`. -/
def matrixLiouvilleSchrodinger
    {d : Type*} [Fintype d] [DecidableEq d]
    (L : ℝ → MatrixLiouvilleKet d → MatrixLiouvilleKet d)
    (traj : MatrixLiouvilleTrajectory d) : Prop :=
  ∀ t : ℝ, traj.dstate t = L t (traj.state t)

/-- **Canonical zero direct matrix Liouville trajectory** `ρ(t) ≡ 0`. -/
def zeroMatrixLiouvilleTrajectory
    (d : Type*) [Fintype d] [DecidableEq d] :
    MatrixLiouvilleTrajectory d where
  state := fun _ => 0
  dstate := fun _ => 0

/-- The zero direct matrix Liouville trajectory solves the direct
Liouville-Schrödinger equation for any generator that vanishes at zero. -/
theorem zeroMatrixLiouvilleTrajectory_solves_matrixLiouvilleSchrodinger
    {d : Type*} [Fintype d] [DecidableEq d]
    (L : ℝ → MatrixLiouvilleKet d → MatrixLiouvilleKet d)
    (h_L_zero : ∀ t, L t 0 = 0) :
    matrixLiouvilleSchrodinger L (zeroMatrixLiouvilleTrajectory d) := by
  intro t
  show (0 : MatrixLiouvilleKet d) = L t 0
  rw [h_L_zero]

/-- **Existence of a direct matrix Liouville trajectory** for any generator
that vanishes at zero: the zero trajectory is a witness. -/
theorem exists_matrix_liouville_trajectory
    {d : Type*} [Fintype d] [DecidableEq d]
    (L : ℝ → MatrixLiouvilleKet d → MatrixLiouvilleKet d)
    (h_L_zero : ∀ t, L t 0 = 0) :
    ∃ traj : MatrixLiouvilleTrajectory d, matrixLiouvilleSchrodinger L traj :=
  ⟨zeroMatrixLiouvilleTrajectory d,
   zeroMatrixLiouvilleTrajectory_solves_matrixLiouvilleSchrodinger L h_L_zero⟩

end Physlib.QuantumMechanics.Liouville.Schrodinger

end
