/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

/-!
# The tetrad connection one-form is `𝔰𝔬(1,3)`-valued: Jacobi–Ricci–Bianchi ↔ Lusanna ADM tetrad gravity

Bridges the two tetrad-formalism files. `Curvature.JacobiRicciBianchiTetrad` includes the rigid orthonormal connection
coefficients `Γ_abc` (antisymmetric in the first two, lowered, indices — Van den Bergh Eq 7), while
`CanonicalTetradGravity.TetradADMGravity` includes the local Lorentz gauge algebra `𝔰𝔬(1,3)` of the tetrad
(`IsLorentzAlg J : Jᵀη = −ηJ`, with the lowered form `ηJ` plain-antisymmetric).

These are the same structure: for each fixed form index `c`, the **connection one-form** `(Γ_{··c})` is a
matrix that is plain-antisymmetric, i.e. it is precisely the lowered (`ηJ`) form of a Lorentz-Lie-algebra
generator. The **Ricci rotation coefficients of the tetrad are `𝔰𝔬(1,3)`-valued** — the connection that the
Jacobi–Ricci–Bianchi curvature is built from lives in the very Lorentz gauge algebra that Lusanna's tetrad
gravity gauges away into the inertial freedom.

* `connMatrix` — the connection one-form `M_c` with `(M_c)_ab = Γ_abc`.
* `connMatrix_antisymm` — `M_cᵀ = −M_c` (from the rigid orthonormal antisymmetry, Eq 7).
* `connMatrix_isLorentz` — `IsLorentzAlg (η · M_c)`: the `η`-dressed connection one-form is a genuine
 `𝔰𝔬(1,3)` generator (using `η² = 1`).
* `tetrad_connection_lorentz_valued` — the main result: `M_c` is antisymmetric, `η M_c ∈ 𝔰𝔬(1,3)`, and (reusing
 Lusanna's `infinitesimal_lorentz_metric_invariant`) it generates a **metric-preserving** frame variation
 `Eᵀ((ηM_c)ᵀη + η(ηM_c))E = 0` — the connection acts as an infinitesimal local Lorentz rotation of the frame.

Proven purely algebraically: the rigid-tetrad antisymmetry makes each connection one-form
a lowered `𝔰𝔬(1,3)` element, hence a metric-preserving frame generator. This identifies the *structure* algebra
of the two formalisms; the full curvature two-form `R = dΓ + Γ∧Γ` and the dynamics are not built (see the
`layering` notes of the two parent files).

## References

* N. Van den Bergh, *On the relation between the Einstein field equations and the Jacobi–Ricci–Bianchi
 system*, Class. Quantum Grav. **31** (2014) 145007, doi:10.1088/0264-9381/31/14/145007;
 arXiv:1302.6448v3 [gr-qc] (10 June 2013) — rigid orthonormal connection antisymmetry `Γ_{(ab)c}=0`,
 Eq (7), p. 3.
* L. Lusanna, *Canonical ADM tetrad gravity and cosmology*, Int. J. Geom. Methods Mod. Phys. **12** (2015)
 1530001, doi:10.1142/S0219887815300019 — the local Lorentz `𝔰𝔬(1,3)` gauge freedom of the tetrad.
* `Physlib` (`Curvature.JacobiRicciBianchiTetrad.TetradConnection`, `CanonicalTetradGravity.TetradADMGravity`).

No new axioms.
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiLusanna

variable {d : ℕ} (T : TetradConnection (Fin 1 ⊕ Fin d)) (c : Fin 1 ⊕ Fin d)

/-- The **connection one-form** `M_c` of the rigid tetrad: the matrix with entries `(M_c)_ab = Γ_abc` (the
form index `c` held fixed). -/
def connMatrix : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ := Matrix.of (fun a b => T.Γ a b c)

/-- **[The connection one-form is antisymmetric]** `M_cᵀ = −M_c` — the rigid orthonormal-tetrad antisymmetry
`Γ_{(ab)c} = 0` (Van den Bergh Eq 7) read as a matrix statement. -/
theorem connMatrix_antisymm : (connMatrix T c)ᵀ = -(connMatrix T c) := by
  ext a b
  simp only [connMatrix, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
  exact T.rigid b a c

/-- **[The connection one-form is `𝔰𝔬(1,3)`-valued]** `IsLorentzAlg (η · M_c)` — dressing the antisymmetric
connection matrix with the Minkowski metric yields a genuine Lorentz-Lie-algebra generator (the Ricci rotation
coefficients live in `𝔰𝔬(1,3)`). Uses `η² = 1`. -/
theorem connMatrix_isLorentz : IsLorentzAlg (minkowskiMatrix * connMatrix T c) := by
  unfold IsLorentzAlg
  rw [transpose_mul, minkowskiMatrix.eq_transpose, Matrix.mul_assoc, minkowskiMatrix.sq,
    mul_one, connMatrix_antisymm, ← Matrix.mul_assoc, minkowskiMatrix.sq, one_mul]

/-- **[The tetrad connection one-form is a metric-preserving Lorentz generator]** the main result bridge: for each
form index `c` the connection one-form `M_c` is antisymmetric, its `η`-dressed form `η M_c` is an `𝔰𝔬(1,3)`
generator, and (by `infinitesimal_lorentz_metric_invariant`) it generates a **metric-preserving** infinitesimal
frame rotation `Eᵀ((ηM_c)ᵀη + η(ηM_c))E = 0`. The Jacobi–Ricci–Bianchi connection and Lusanna's tetrad Lorentz
gauge algebra are the same `𝔰𝔬(1,3)`. -/
theorem tetrad_connection_lorentz_valued
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    (connMatrix T c)ᵀ = -(connMatrix T c)
      ∧ IsLorentzAlg (minkowskiMatrix * connMatrix T c)
      ∧ Eᵀ * ((minkowskiMatrix * connMatrix T c)ᵀ * minkowskiMatrix
            + minkowskiMatrix * (minkowskiMatrix * connMatrix T c)) * E = 0 :=
  ⟨connMatrix_antisymm T c, connMatrix_isLorentz T c,
    infinitesimal_lorentz_metric_invariant (connMatrix_isLorentz T c) E⟩

end Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiLusanna

end
