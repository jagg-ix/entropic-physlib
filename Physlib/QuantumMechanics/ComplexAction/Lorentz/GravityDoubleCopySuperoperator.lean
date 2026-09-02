/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual

/-!
# The gauge/gravity double-copy superoperator pair of the Lorentz force

Constructs the **operator-level** superoperators for the Lorentz-force BCJ double copy (previously at the
*amplitude* level, `(F·V)²/D` in `Lorentz.ForceBCJDual`). The field strength `F = dA`, a Lorentz generator,
gives two linear generators on the velocity space `ℝ⁴`:

* the **gauge** Lorentz-force generator `lorentzGen F = (F · ·)` — the cyclotron/boost rotation of the
  velocity (`V̇ ∝ F·V`), the gauge-side flow;
* its **gravity** double copy `gravCurvatureGen F = (F² · ·) = ad_F ∘ ad_F` — the curvature/tidal generator,
  the field strength squared (`gravity = gauge²` at the operator level).

The gauge generator does no work (`F` antisymmetric ⟹ `V·(F V) = 0`), and the gravity generator's quadratic
form is exactly minus the Lorentz-force magnitude `V·(F² V) = −|F V|²`, tying the operator-level double copy
to the amplitude-level Lorentz-force dual `(F·V)²/D` and, through it, to the Jacobson-diamond channel.

* **§A — the gauge Lorentz-force generator** (`lorentzGen`, `lorentzGen_no_work`,
  `lorentzGen_timeReversal`). The velocity-space generator `F·V`; antisymmetric `F` does no work; `T`-odd.
* **§B — the gravity double-copy generator** (`gravCurvatureGen`, `gravCurvatureGen_eq_comp`,
  `gravCurvatureGen_timeReversal`). `F² = ad_F ∘ ad_F`, the curvature/tidal generator; `T`-odd.
* **§C — the operator/amplitude link** (`gravCurvatureGen_quadratic`, `gravCurvatureGen_quadratic_lorentz`).
  `V·(F² V) = −|F V|² = −∑_μ (lorentzForceNum F V μ)²` — the gravity generator's quadratic form is minus the
  squared Lorentz force, the amplitude that doubles to the gravitational dual.

## References

* The double copy `gravity = gauge²`; the field strength `F` as a Lorentz generator (cyclotron/boost) and
  `F²` as the curvature/tidal term.
* Repo carriers: `Vlasov.MaxwellEM.antisym_no_work`; `Lorentz.ForceBCJDual` (`lorentzForceNum`,
  `lorentzForceDual`); `PTSymmetricQFT.MaxwellFaraday.faraday`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator

open Matrix
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual


/-- **The gauge Lorentz-force generator** `lorentzGen F : V ↦ F·V` — the field strength acting on the
velocity, the cyclotron/boost rotation generator (the gauge-side flow `V̇ ∝ F·V`). -/
noncomputable def lorentzGen (F : Matrix (Fin 4) (Fin 4) ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.mulVecLin F

@[simp] lemma lorentzGen_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) :
    lorentzGen F V = F *ᵥ V := rfl

/-- **The gauge generator does no work** `V·(F V) = 0` for antisymmetric `F` — the Lorentz force is
orthogonal to the velocity (`antisym_no_work`). -/
lemma lorentzGen_no_work (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = -F j i)
    (V : Fin 4 → ℝ) : V ⬝ᵥ (lorentzGen F V) = 0 :=
  antisym_no_work F hF V

/-- **[`T`-odd] The gauge generator flips under velocity reversal** `F·(−V) = −(F·V)`. -/
lemma lorentzGen_timeReversal (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) :
    lorentzGen F (-V) = -(lorentzGen F V) := map_neg _ _


/-- **The gravity double-copy generator** `gravCurvatureGen F : V ↦ F²·V` — the field strength squared, the
curvature/tidal generator (`gravity = gauge²` at the operator level). -/
noncomputable def gravCurvatureGen (F : Matrix (Fin 4) (Fin 4) ℝ) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.mulVecLin (F * F)

/-- **The gravity generator is the gauge generator composed with itself** `F² = ad_F ∘ ad_F` — the
double-copy structure at the operator level. -/
lemma gravCurvatureGen_eq_comp (F : Matrix (Fin 4) (Fin 4) ℝ) :
    gravCurvatureGen F = (lorentzGen F).comp (lorentzGen F) := by
  rw [gravCurvatureGen, lorentzGen, Matrix.mulVecLin_mul]

/-- **[`T`-odd] The gravity generator flips under velocity reversal** `F²·(−V) = −(F²·V)`. -/
lemma gravCurvatureGen_timeReversal (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) :
    gravCurvatureGen F (-V) = -(gravCurvatureGen F V) := map_neg _ _


/-- **[Gravity quadratic form] `V·(F² V) = −|F V|²`** for antisymmetric `F` — the gravity generator's
quadratic form is minus the squared Lorentz force. -/
lemma gravCurvatureGen_quadratic (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = -F j i)
    (V : Fin 4 → ℝ) : V ⬝ᵥ (gravCurvatureGen F V) = -((F *ᵥ V) ⬝ᵥ (F *ᵥ V)) := by
  have hT : Fᵀ = -F := by funext i j; rw [Matrix.transpose_apply, Matrix.neg_apply]; exact hF j i
  rw [gravCurvatureGen, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hT, Matrix.neg_mulVec, neg_dotProduct]

/-- **[Link to the Lorentz-force dual] `V·(F² V) = −∑_μ (lorentzForceNum F V μ)²`.** The gravity generator's
quadratic form is minus the sum of squared Lorentz-force components — the gauge amplitude that the BCJ double
copy lifts to the gravitational dual `lorentzForceDual` (and, at the diamond mode, to the diamond velocity²).
-/
lemma gravCurvatureGen_quadratic_lorentz (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : ∀ i j, F i j = -F j i)
    (V : Fin 4 → ℝ) :
    V ⬝ᵥ (gravCurvatureGen F V) = -(∑ μ, (lorentzForceNum F V μ) ^ 2) := by
  rw [gravCurvatureGen_quadratic F hF V]
  congr 1
  simp only [dotProduct, lorentzForceNum, sq]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator

end
