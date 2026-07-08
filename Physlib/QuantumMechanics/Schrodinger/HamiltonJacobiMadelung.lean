/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Schrodinger.BohmianQuantumPotential
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The quantum Hamilton–Jacobi–Madelung (de Broglie–Bohm) equation

Completes the Phase-2 PDE content deferred by `MadelungPolarDecomposition`: the **quantum Hamilton–Jacobi
equation** of de Broglie–Bohm mechanics. Writing the Madelung amplitude/phase as `ψ = R·e^{iS/ℏ}` for a
genuine spacetime phase field `S : ℝ → E → ℝ` on a finite-dimensional real inner-product space `E`, the real
part of the Schrödinger equation is

  `∂tS + |∇S|²/(2m) + V + Q = 0`,   `Q = −ℏ²·ΔR/(2mR)`   (the Bohmian quantum potential),

stated here with the **actual differential calculus** of the space: `∂tS = deriv (fun τ => S τ x) t`, the
kinetic density `|∇S|² = ‖∇(S t) x‖²` with Mathlib's gradient `∇`, and the *concrete*
`quantumPotential (R t) m ℏ` (`BohmianQuantumPotential`, built on Mathlib's Laplacian `Δ`). The residuals

  `classicalHJResidual = ∂tS + |∇S|²/(2m) + V`   (`classicalHJResidual`),
  `quantumHJResidual   = classicalHJResidual + Q` (`quantumHJResidual`),

vanish exactly on solutions (`ClassicalHamiltonJacobi`, `QuantumHamiltonJacobi`).

The two genuinely physical facts:

* **The Bohm equation is the classical Hamilton–Jacobi equation in the effective potential `V + Q`**
  (`quantumHamiltonJacobi_iff_effective_classical`): a Bohmian particle moves *classically* under
  `V_eff = V + Q`. This is the entire content of the de Broglie–Bohm picture.
* **The classical limit**: at `ℏ = 0` the quantum potential vanishes (`quantumPotential_zero_hbar`) and the
  quantum equation collapses to the classical Hamilton–Jacobi equation
  (`quantumHamiltonJacobi_hbar_zero_iff`); a **constant amplitude** likewise kills `Q`
  (`quantumPotential_const`). The free particle (constant amplitude, phase `S = ⟪k,x⟫ − (‖k‖²/2m)t`) is a
  worked solution of *both* equations (`freeParticle_classicalHamiltonJacobi`,
  `freeParticle_quantumHamiltonJacobi`), with the gradient `∇S = k` and `∂tS = −‖k‖²/2m` computed from the
  actual calculus and the dispersion relation `E = ‖k‖²/2m` falling out.

* **§A — the residuals and the equations** (`classicalHJResidual`, `quantumHJResidual`,
  `ClassicalHamiltonJacobi`, `QuantumHamiltonJacobi`).
* **§B — the de Broglie–Bohm effective potential** (`quantumHJResidual_eq_effective_classical`,
  `quantumHamiltonJacobi_iff_effective_classical`).
* **§C — classical limit and the free particle** (`quantumPotential_zero_hbar`, `quantumPotential_const`,
  `quantumHamiltonJacobi_hbar_zero_iff`, `freePhase`, `freeParticle_classicalHamiltonJacobi`,
  `freeParticle_quantumHamiltonJacobi`).

## References

* D. Bohm (1952); E. Madelung (1927); B. J. Hiley (2015, the Baker/Bohm Hamilton–Jacobi limit). structure:
  `Physlib` (`quantumPotential`, Mathlib `Δ`, `∇`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.Schrodinger

open scoped Laplacian Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## §A — the residuals and the equations -/

/-- **The classical Hamilton–Jacobi residual** `∂tS + |∇S|²/(2m) + V`, with the genuine time derivative
`∂tS = deriv (fun τ => S τ x) t` and spatial gradient `∇(S t) x`. -/
noncomputable def classicalHJResidual (S : ℝ → E → ℝ) (V : ℝ → E → ℝ) (m t : ℝ) (x : E) : ℝ :=
  deriv (fun τ => S τ x) t + ‖∇ (S t) x‖ ^ 2 / (2 * m) + V t x

/-- **The quantum (de Broglie–Bohm) Hamilton–Jacobi residual** `∂tS + |∇S|²/(2m) + V + Q`, the classical
residual plus the Bohmian `quantumPotential` of the amplitude `R`. -/
noncomputable def quantumHJResidual (S : ℝ → E → ℝ) (V R : ℝ → E → ℝ) (m ℏ t : ℝ) (x : E) : ℝ :=
  classicalHJResidual S V m t x + quantumPotential (R t) m ℏ x

/-- **The classical Hamilton–Jacobi equation** — the residual vanishes everywhere on spacetime. -/
def ClassicalHamiltonJacobi (S : ℝ → E → ℝ) (V : ℝ → E → ℝ) (m : ℝ) : Prop :=
  ∀ t x, classicalHJResidual S V m t x = 0

/-- **The quantum (de Broglie–Bohm) Hamilton–Jacobi equation** — the quantum residual vanishes everywhere. -/
def QuantumHamiltonJacobi (S : ℝ → E → ℝ) (V R : ℝ → E → ℝ) (m ℏ : ℝ) : Prop :=
  ∀ t x, quantumHJResidual S V R m ℏ t x = 0

/-! ## §B — the de Broglie–Bohm effective potential -/

/-- **[The Bohm equation is classical Hamilton–Jacobi in the effective potential `V + Q`].** The quantum
residual for potential `V` equals the *classical* residual for the effective potential `V + Q`. -/
theorem quantumHJResidual_eq_effective_classical (S V R : ℝ → E → ℝ) (m ℏ t : ℝ) (x : E) :
    quantumHJResidual S V R m ℏ t x
      = classicalHJResidual S (fun τ y => V τ y + quantumPotential (R τ) m ℏ y) m t x := by
  simp only [quantumHJResidual, classicalHJResidual]; ring

/-- **[de Broglie–Bohm picture] the quantum Hamilton–Jacobi equation holds iff the classical one holds in the
effective potential `V + Q`.** A Bohmian particle moves classically under `V_eff = V + Q`. -/
theorem quantumHamiltonJacobi_iff_effective_classical (S V R : ℝ → E → ℝ) (m ℏ : ℝ) :
    QuantumHamiltonJacobi S V R m ℏ
      ↔ ClassicalHamiltonJacobi S (fun τ y => V τ y + quantumPotential (R τ) m ℏ y) m :=
  forall₂_congr fun t x => by rw [quantumHJResidual_eq_effective_classical]

/-! ## §C — classical limit and the free particle -/

/-- **[Classical limit: the quantum potential vanishes at `ℏ = 0`] `Q = 0` when `ℏ = 0`.** -/
@[simp] theorem quantumPotential_zero_hbar (R : E → ℝ) (m : ℝ) (x : E) :
    quantumPotential R m 0 x = 0 := by
  simp [quantumPotential]

/-- **[A constant amplitude has zero quantum potential] `Q = 0` when `R` is constant.** The regime in which
de Broglie–Bohm trajectories are exactly classical (`ΔR = 0`). -/
@[simp] theorem quantumPotential_const (c m ℏ : ℝ) (x : E) :
    quantumPotential (fun _ => c) m ℏ x = 0 := by
  simp [quantumPotential]

/-- **[At `ℏ = 0` the quantum residual is the classical residual].** -/
theorem quantumHJResidual_hbar_zero (S V R : ℝ → E → ℝ) (m t : ℝ) (x : E) :
    quantumHJResidual S V R m 0 t x = classicalHJResidual S V m t x := by
  rw [quantumHJResidual, quantumPotential_zero_hbar, add_zero]

/-- **[Classical limit] at `ℏ = 0` the quantum Hamilton–Jacobi equation is the classical one.** -/
theorem quantumHamiltonJacobi_hbar_zero_iff (S V R : ℝ → E → ℝ) (m : ℝ) :
    QuantumHamiltonJacobi S V R m 0 ↔ ClassicalHamiltonJacobi S V m :=
  forall₂_congr fun t x => by rw [quantumHJResidual_hbar_zero]

/-- **Gradient of an inner-product functional minus a constant**: `∇(⟪k, ·⟫ − C) = k`, computed from the
Riesz representation (`toDual`). The spatial gradient of the free-particle phase. -/
theorem gradient_inner_sub_const (k x : E) (C : ℝ) :
    ∇ (fun y => (inner ℝ k y : ℝ) - C) x = k := by
  have h : HasGradientAt (fun y => (inner ℝ k y : ℝ) - C)
      ((InnerProductSpace.toDual ℝ E).symm (InnerProductSpace.toDual ℝ E k)) x :=
    (((InnerProductSpace.toDual ℝ E k).hasFDerivAt).sub_const C).hasGradientAt
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.gradient

/-- **The free-particle Madelung phase** `S(t, x) = ⟪k, x⟫ − (‖k‖²/2m)·t` — a plane wave of wavevector `k`
with energy `‖k‖²/2m`. -/
noncomputable def freePhase (k : E) (m : ℝ) : ℝ → E → ℝ :=
  fun t x => (inner ℝ k x : ℝ) - ‖k‖ ^ 2 / (2 * m) * t

/-- **[Worked solution: the free particle solves the classical Hamilton–Jacobi equation].** With `V = 0` and
phase `freePhase`, the actual time derivative is `∂tS = −‖k‖²/(2m)` and the actual gradient is `∇S = k`
(so `|∇S|² = ‖k‖²`); the residual vanishes — the dispersion relation `E = ‖k‖²/(2m)`. -/
theorem freeParticle_classicalHamiltonJacobi (k : E) (m : ℝ) :
    ClassicalHamiltonJacobi (freePhase k m) (fun _ _ => 0) m := by
  intro t x
  have hd : deriv (fun τ => freePhase k m τ x) t = -(‖k‖ ^ 2 / (2 * m)) := by
    have h1 : HasDerivAt (fun τ : ℝ => (inner ℝ k x : ℝ) - ‖k‖ ^ 2 / (2 * m) * τ)
        (-(‖k‖ ^ 2 / (2 * m))) t := by
      simpa using ((hasDerivAt_id t).const_mul (‖k‖ ^ 2 / (2 * m))).const_sub (inner ℝ k x : ℝ)
    exact h1.deriv
  have hg : ∇ (freePhase k m t) x = k := gradient_inner_sub_const k x (‖k‖ ^ 2 / (2 * m) * t)
  rw [classicalHJResidual, hd, hg]
  simp

/-- **[Worked solution: the free particle solves the quantum Hamilton–Jacobi equation too].** A free particle
has constant amplitude, so `Q = 0` and the quantum equation reduces to the (satisfied) classical one —
de Broglie–Bohm trajectories of a free particle are exactly classical straight lines. -/
theorem freeParticle_quantumHamiltonJacobi (k : E) (m c ℏ : ℝ) :
    QuantumHamiltonJacobi (freePhase k m) (fun _ _ => 0) (fun _ _ => c) m ℏ := by
  intro t x
  rw [quantumHJResidual,
    show quantumPotential ((fun (_ : ℝ) (_ : E) => c) t) m ℏ x = 0 from quantumPotential_const c m ℏ x,
    add_zero]
  exact freeParticle_classicalHamiltonJacobi k m t x

/-! ## §D — the de Broglie guidance velocity -/

/-- **The de Broglie–Bohm guidance velocity** `v = ∇S / m` — the guidance equation `m·ẋ = ∇S`, the actual
vector field on `E`. `MadelungPolarDecomposition` documents this equation but used only a scalar proxy;
here it is the genuine gradient field. -/
noncomputable def guidanceVelocity (S : ℝ → E → ℝ) (m t : ℝ) (x : E) : E :=
  (m⁻¹ : ℝ) • ∇ (S t) x

/-- **[The Hamilton–Jacobi kinetic term is the kinetic energy `½m‖v‖²`]** `|∇S|²/(2m) = ½m‖v‖²` — the
kinetic density written through the guidance velocity. -/
theorem kinetic_eq_half_m_guidanceVelocity_sq (S : ℝ → E → ℝ) (m t : ℝ) (hm : m ≠ 0) (x : E) :
    ‖∇ (S t) x‖ ^ 2 / (2 * m) = m / 2 * ‖guidanceVelocity S m t x‖ ^ 2 := by
  rw [guidanceVelocity, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp

/-- **[The Bohm equation in Bernoulli / velocity form]** `∂tS + ½m‖v‖² + V + Q = 0`. -/
theorem quantumHJResidual_velocity_form (S V R : ℝ → E → ℝ) (m ℏ t : ℝ) (hm : m ≠ 0) (x : E) :
    quantumHJResidual S V R m ℏ t x
      = deriv (fun τ => S τ x) t + m / 2 * ‖guidanceVelocity S m t x‖ ^ 2 + V t x
          + quantumPotential (R t) m ℏ x := by
  rw [quantumHJResidual, classicalHJResidual, kinetic_eq_half_m_guidanceVelocity_sq S m t hm]

/-- **[The free particle has constant guidance velocity] `v = k/m`** — uniform classical motion, the
straight-line Bohmian trajectories of a free particle. -/
theorem freeParticle_guidanceVelocity (k : E) (m t : ℝ) (x : E) :
    guidanceVelocity (freePhase k m) m t x = (m⁻¹ : ℝ) • k := by
  rw [guidanceVelocity]
  congr 1
  exact gradient_inner_sub_const k x (‖k‖ ^ 2 / (2 * m) * t)

end Physlib.QuantumMechanics.Schrodinger

end
