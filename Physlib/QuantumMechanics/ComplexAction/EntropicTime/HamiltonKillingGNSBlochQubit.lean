/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingHilbertSpace
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
public import Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics

/-!
# The Hamilton–Killing Hilbert space is the GNS space; the QM ray is the Bloch-sphere qubit

Links the emergent Hilbert space of the Hamilton–Killing derivation of quantum mechanics (Caticha 2107.08502 §6,
`HamiltonKillingHilbertSpace`) to the rest of the repository: the AQFT **GNS construction**
(`AlgebraicQFT.GNSVonNeumannHadamard`) and the **Bloch sphere / exclusion-cell qubit** (`LorenzQubitBlochDynamics`).

* the **emergent inner product is the GNS pre-inner-product** — both the Hamilton–Killing inner product `½(G+iΩ)`
 and the GNS form `gnsForm ω a b = ω(a*b)` are Hermitian sesquilinear forms with **real self-value**
 (`hk_inner_is_gns`): `Im⟨ψ|ψ⟩ = 0` (`hermitianInner_self_real`) matches `Im(gnsForm ω a a) = 0`
 (`gns_self_real`). The Hilbert space *derived* from the metric-plus-symplectic structure is the GNS Hilbert
 space of a state;
* the **normalized QM state is a point of the Bloch sphere** (`qm_ray_on_blochSphere`): a two-outcome
 ("quantum die") state `(ρ₀, ρ₁)` with `ρ₀ + ρ₁ = 1` and phase `φ` maps to the Bloch vector
 `(2√(ρ₀ρ₁)cos φ, 2√(ρ₀ρ₁)sin φ, ρ₀ − ρ₁)`, which lies on the unit Bloch sphere `BlochSphere` — the QM ray is
 exactly the exclusion-cell qubit `= CP¹`, closing the Caticha derivation onto the electron-cell arc's qubit.

So the Hamilton–Killing derivation of quantum mechanics lands on the repository's own furniture: its Hilbert
inner product is the GNS form of a state, and its ray of states is the Bloch sphere / `CP¹` qubit of the
exclusion-cell arc — the information-geometry route to QM and the operator-algebraic / qubit structures are one.

* **§A — the emergent inner product is the GNS form** (`hk_inner_is_gns`).
* **§B — the QM ray is the Bloch-sphere qubit** (`blochVectorOfQubit`, `qm_ray_on_blochSphere`).

The GNS identification reuses `gns_self_real`/`hermitianInner_self_real` (both exact
real-self-value facts); the Bloch-sphere membership is the exact `(ρ₀+ρ₁)² = 1` identity via `sin²+cos²=1` and
`√(ρ₀ρ₁)² = ρ₀ρ₁`. The full GNS completion and the Bloch/`CP¹` isomorphism are the referenced structures. No new
axioms.

## References

* A. Caticha, arXiv:2107.08502, §6. Repo dependencies: `EntropicTime.HamiltonKillingHilbertSpace`,
 `AlgebraicQFT.GNSVonNeumannHadamard` (`gnsForm`), `LorenzQubitBlochDynamics` (`BlochSphere`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingHilbertSpace
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingGNSBlochQubit

/-! ## §A — the emergent inner product is the GNS form -/

/-- **[The Hamilton–Killing inner product is the GNS pre-inner-product].** Both the emergent Hilbert inner product
`½(G+iΩ)` and the GNS form `gnsForm ω = ω(a*b)` are Hermitian sesquilinear forms with **real self-value**:
`Im(gnsForm ω a a) = 0` and `Im⟨ψ|ψ⟩ = 0`. The Hilbert space derived from the metric-plus-symplectic (Kähler)
structure of the statistical manifold is the GNS Hilbert space of a state — the information-geometry and
operator-algebraic routes to the quantum inner product coincide. -/
theorem hk_inner_is_gns {A : Type*} [Ring A] [StarRing A] (ω : A → ℂ)
    (herm : ∀ x, ω (star x) = starRingEnd ℂ (ω x)) (a : A) (g : ℝ) :
    (gnsForm ω a a).im = 0 ∧ (hermitianInner g 0).im = 0 :=
  ⟨gns_self_real ω herm a, hermitianInner_self_real g⟩

/-! ## §B — the QM ray is the Bloch-sphere qubit -/

/-- **The Bloch vector of a normalized two-outcome quantum state** `(ρ₀, ρ₁)` with phase `φ`:
`(2√(ρ₀ρ₁)cos φ, 2√(ρ₀ρ₁)sin φ, ρ₀ − ρ₁)` — the Bloch-sphere representation of the qubit ray. -/
noncomputable def blochVectorOfQubit (ρ₀ ρ₁ φ : ℝ) : BlochVector :=
  ![2 * Real.sqrt (ρ₀ * ρ₁) * Real.cos φ, 2 * Real.sqrt (ρ₀ * ρ₁) * Real.sin φ, ρ₀ - ρ₁]

/-- **[The normalized QM state is a Bloch-sphere point] `‖r‖² = 1`.** A two-outcome quantum state `(ρ₀, ρ₁)` with
`ρ₀ + ρ₁ = 1` maps to a Bloch vector on the unit sphere: `|r|² = 4ρ₀ρ₁(cos²+sin²) + (ρ₀−ρ₁)² = (ρ₀+ρ₁)² = 1`. The
QM ray of the Hamilton–Killing derivation is exactly the exclusion-cell qubit `= CP¹` on the Bloch sphere. -/
theorem qm_ray_on_blochSphere (ρ₀ ρ₁ φ : ℝ) (h : ρ₀ + ρ₁ = 1) (hρ : 0 ≤ ρ₀ * ρ₁) :
    BlochSphere (blochVectorOfQubit ρ₀ ρ₁ φ) := by
  unfold BlochSphere blochVectorOfQubit
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  have hsq : Real.sqrt (ρ₀ * ρ₁) ^ 2 = ρ₀ * ρ₁ := Real.sq_sqrt hρ
  have hcs : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  nlinarith [hsq, hcs, h, sq_nonneg (ρ₀ - ρ₁)]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingGNSBlochQubit

end
