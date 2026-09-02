/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CartanDecompositionDoubleCovers
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Lorentz double cover `SL(2,ℂ)`: complex Euler angles and the six-factor Cartan
decomposition

Continues `CartanDecompositionDoubleCovers` (§§2–3 of Varlamov, *Towards the Quantum
Electrodynamics on the Poincaré Group*, arXiv:hep-th/0403070) into **§4, the group
`SL(2,ℂ)`**, on the same Pauli carriers:

* `su2CanonicalForm`, `su11CanonicalForm` (Eqs. (1), (19)) — the canonical matrix forms
  `[[α,β],[−β̄,ᾱ]]` and `[[γ,δ],[δ̄,γ̄]]` with determinants `|α|²+|β|²` resp.
  `|γ|²−|δ|²`, and `su2Euler_canonicalForm` / `su11Euler_canonicalForm` identifying the
  Euler matrices (Eqs. (2), (19)) as instances;
* **complex Euler angles** (Eqs. (36)–(37)): `complex_half_angle_cos/sin` — the
  complexification identities `cos((θ−iτ)/2) = cos(θ/2)cosh(τ/2) + i sin(θ/2)sinh(τ/2)`
  (and the sine partner) stated under Eq. (37);
* `torusFactor_mul_realTorusFactor`, `middleRotation_mul_middleBoost` — **the pair
  collapses**: a compact torus times the new noncompact `realTorusFactor` is one complex
  torus of angle `φ − iε`, and Eq. (73): the compact rotation times the boost is one
  `complexMiddleRotation` of angle `θ − iτ` — rotation and boost fuse into a rotation by
  a complex angle;
* `sl2c_cartan_kak` (Eq. (38)) — **the six-factor Cartan decomposition of `SL(2,ℂ)`**:
  the product of the six real factors *is* the `SU(2)` KAK of
  `CartanDecompositionDoubleCovers` with all three Euler angles complexified;
  `complexTorusFactor_det`, `complexMiddleRotation_det` — each complex factor has
  determinant one, so the product lies in `SL(2,ℂ)`;
* the **six one-parameter subgroups** `a₁,a₂,a₃,b₁,b₂,b₃` (§4, after Eq. (39)) as one
  complex family on two axes: `middleRotation_eq_complexOnAxis` /
  `middleBoost_eq_complexOnAxis` (`a₁`, `b₁` are `complexMiddleRotation` at `θ` resp.
  `−iτ`) and `torusFactor_eq_complexOnAxis` / `realTorusFactor_eq_complexOnAxis`
  (`a₃`, `b₃` are `complexTorusFactor` at `φ` resp. `−iε`) — §2's `cos` and §3's `cosh`
  are one function; the `B`-tangent completing the `su11Tangent` pair is the new
  `sl2cBoostB3 = (1/2)σ_z` (the paper's tangent-derivative face is definitional and not
  re-proven);
* `sl2c_cross_commutators`, `sl2c_boost_boost` (Eq. (40)) — the twelve-relation
  `sl(2,ℂ)` table completed: `[A_i,B_i] = 0`, the six mixed relations, and the two
  boost-boost relations `[B₂,B₃] = −A₁`, `[B₃,B₁] = −A₂` missing from the double-cover
  module (whose `su11_sign_flip` used the compact `B₃ = A₃` convention of §3);
* `weylLeft_closed_form`, `weylRight_eq_zero`, `weylLeft_su2` (Eqs. (41)–(43)) — the
  chiral split `X_l = (i/2)(A_l + iB_l)`, `Y_l = (i/2)(A_l − iB_l)`: in the fundamental
  representation the left generators close on `su(2)` (`[X_k,X_l] = iε_{klm}X_m`,
  Eq. (42)) and the right generators **vanish identically** — the fundamental is the
  left-handed (undotted, `(1/2,0)`) Weyl spinor, the seed of the local isomorphism
  `SL(2,ℂ) ≃ SU(2)⊗SU(2)` (Eq. (44)) carried elsewhere by the repository's spinor
  lattice (`Particles.SpinorStructureInternalSymmetries`) and the `(j,j)` floors of
  `PeriodicTableMadelungSpinTower`.

**Honest layering.**  Exact `2×2` matrix, elementary-function, and derivative algebra.
The paper's harmonic-analytic §§4.1–5 — hyperspherical functions `Z^l_{mn}` (Eq. (69)),
principal/supplementary series (Eqs. (80)–(84)), Plancherel (Eq. (90)) — and the
§§6–7 field superstructure on the homogeneous spaces `M₈ = ℝ^{1,3} × S²` are the
analytic layer, cited not re-proven; §§8–10 (Dirac/Maxwell boundary problems, N- and
T-products, interaction) likewise.

## References

* V. V. Varlamov, *Towards the Quantum Electrodynamics on the Poincaré Group*,
  arXiv:hep-th/0403070.  §4: Eqs. (36)–(44), (73); §2: Eqs. (1)–(3); §3: Eq. (19).
* Carrier reuse: `CartanDecompositionDoubleCovers` (`torusFactor`, `middleRotation`,
  `middleBoost`, `su2Tangent*`, `su11Tangent*`, Pauli product lemmas),
  `QuantumMechanics.SpinDensityFunctionalOperators` (Pauli matrices).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.SpinDensityFunctionalOperators
open Physlib.QuantumMechanics.ComplexAction.CartanDecompositionDoubleCovers
open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CartanDecompositionLorentzGroup

/-! ## §A — the canonical forms of the two double covers (Eqs. (1), (19)) -/

/-- **The `SU(2)` canonical form** (Eq. (1)): `[[α, β], [−β̄, ᾱ]]`. -/
def su2CanonicalForm (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α]

/-- **The `SU(1,1)` canonical form** (Eq. (19)): `[[γ, δ], [δ̄, γ̄]]`. -/
def su11CanonicalForm (γ δ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![γ, δ; (starRingEnd ℂ) δ, (starRingEnd ℂ) γ]

/-- The canonical `SU(2)` determinant is `|α|² + |β|²` — Eq. (1)'s unit condition is
exactly `det = 1`. -/
theorem su2CanonicalForm_det (α β : ℂ) :
    (su2CanonicalForm α β).det = ((Complex.normSq α + Complex.normSq β : ℝ) : ℂ) := by
  rw [su2CanonicalForm, Matrix.det_fin_two_of]
  rw [Complex.mul_conj, mul_neg, Complex.mul_conj]
  push_cast
  ring

/-- The canonical `SU(1,1)` determinant is `|γ|² − |δ|²` — Eq. (19)'s unit condition. -/
theorem su11CanonicalForm_det (γ δ : ℂ) :
    (su11CanonicalForm γ δ).det = ((Complex.normSq γ - Complex.normSq δ : ℝ) : ℂ) := by
  rw [su11CanonicalForm, Matrix.det_fin_two_of]
  rw [Complex.mul_conj, Complex.mul_conj]
  push_cast
  ring

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **The Euler matrix is a canonical form** (Eq. (2)): `su2Euler φ θ ψ` is
`su2CanonicalForm` at `α = cos(θ/2)e^{i(φ+ψ)/2}`, `β = i sin(θ/2)e^{i(φ−ψ)/2}`. -/
theorem su2Euler_canonicalForm (φ θ ψ : ℝ) :
    su2Euler φ θ ψ =
      su2CanonicalForm ((Real.cos (θ / 2) : ℂ) * Complex.exp (Complex.I * ((φ + ψ) / 2 : ℝ)))
        (Complex.I * (Real.sin (θ / 2) : ℝ) * Complex.exp (Complex.I * ((φ - ψ) / 2 : ℝ))) := by
  unfold su2Euler su2CanonicalForm
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [map_mul, map_ofNat, map_div₀, ← Complex.exp_conj, Complex.conj_I,
        Complex.conj_ofReal, -Complex.ofReal_sin, -Complex.ofReal_cos,
        -Complex.ofReal_sinh, -Complex.ofReal_cosh]
      all_goals
        first
          | rfl
          | (left; trivial)
          | (congr 1 <;> ring1)
          | (left; congr 1 <;> ring1)

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **The `SU(1,1)` Euler matrix is a canonical form** (Eq. (19)): `su11Euler φ τ ψ` is
`su11CanonicalForm` at `γ = cosh(τ/2)e^{i(φ+ψ)/2}`, `δ = sinh(τ/2)e^{i(φ−ψ)/2}`. -/
theorem su11Euler_canonicalForm (φ τ ψ : ℝ) :
    su11Euler φ τ ψ =
      su11CanonicalForm ((Real.cosh (τ / 2) : ℂ) * Complex.exp (Complex.I * ((φ + ψ) / 2 : ℝ)))
        ((Real.sinh (τ / 2) : ℂ) * Complex.exp (Complex.I * ((φ - ψ) / 2 : ℝ))) := by
  unfold su11Euler su11CanonicalForm
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [map_mul, map_ofNat, map_div₀, ← Complex.exp_conj, Complex.conj_I,
        Complex.conj_ofReal, -Complex.ofReal_sin, -Complex.ofReal_cos,
        -Complex.ofReal_sinh, -Complex.ofReal_cosh]
      all_goals
        first
          | rfl
          | (left; trivial)
          | (congr 1 <;> ring1)
          | (left; congr 1 <;> ring1)

/-! ## §B — complex Euler angles and the six-factor Cartan decomposition (Eqs. (36)–(38)) -/

/-- **The half-angle complexification, cosine** (stated under Eq. (37)):
`cos((θ − iτ)/2) = cos(θ/2)cosh(τ/2) + i sin(θ/2)sinh(τ/2)`. -/
theorem complex_half_angle_cos (θ τ : ℝ) :
    Complex.cos (((θ : ℂ) - Complex.I * τ) / 2) =
      (Real.cos (θ / 2) : ℂ) * (Real.cosh (τ / 2) : ℂ) +
        Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.sinh (τ / 2) : ℂ) := by
  rw [show (((θ : ℂ) - Complex.I * τ) / 2) = ((θ / 2 : ℝ) : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.cos_sub, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  ring

/-- **The half-angle complexification, sine**:
`sin((θ − iτ)/2) = sin(θ/2)cosh(τ/2) − i cos(θ/2)sinh(τ/2)`. -/
theorem complex_half_angle_sin (θ τ : ℝ) :
    Complex.sin (((θ : ℂ) - Complex.I * τ) / 2) =
      (Real.sin (θ / 2) : ℂ) * (Real.cosh (τ / 2) : ℂ) -
        Complex.I * (Real.cos (θ / 2) : ℂ) * (Real.sinh (τ / 2) : ℂ) := by
  rw [show (((θ : ℂ) - Complex.I * τ) / 2) = ((θ / 2 : ℝ) : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.sin_sub, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  ring

/-- The noncompact torus factor `diag(e^{ε/2}, e^{−ε/2})` — the `b₃` subgroup, the real
sibling of `torusFactor`. -/
noncomputable def realTorusFactor (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp (ε / 2) : ℂ), 0; 0, (Real.exp (-ε / 2) : ℂ)]

/-- The torus factor of a *complex* angle `diag(e^{iz/2}, e^{−iz/2})`. -/
noncomputable def complexTorusFactor (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * z / 2), 0; 0, Complex.exp (-(Complex.I * z / 2))]

/-- The middle rotation of a *complex* angle. -/
noncomputable def complexMiddleRotation (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos (z / 2), Complex.I * Complex.sin (z / 2);
     Complex.I * Complex.sin (z / 2), Complex.cos (z / 2)]

/-- **Pair collapse, tori**: the compact torus times the noncompact torus is one complex
torus of angle `φ − iε` — the first complexification of Eq. (38). -/
theorem torusFactor_mul_realTorusFactor (φ ε : ℝ) :
    torusFactor φ * realTorusFactor ε = complexTorusFactor ((φ : ℂ) - Complex.I * ε) := by
  unfold torusFactor realTorusFactor complexTorusFactor
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    linear_combination ((ε : ℂ) / 2) * Complex.I_sq
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    linear_combination (-(ε : ℂ) / 2) * Complex.I_sq

/-- **Pair collapse, middle factors** (Eq. (73)): the compact rotation times the boost is
one rotation by the complex angle `θ − iτ` — rotation and boost fuse. -/
theorem middleRotation_mul_middleBoost (θ τ : ℝ) :
    middleRotation θ * middleBoost τ =
      complexMiddleRotation ((θ : ℂ) - Complex.I * τ) := by
  unfold middleRotation middleBoost complexMiddleRotation
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two, complex_half_angle_cos, complex_half_angle_sin]
      all_goals
        first
          | ring1
          | linear_combination
              (Complex.cos ((θ : ℂ) / 2) * Complex.sinh ((τ : ℂ) / 2)) * Complex.I_sq

/-- **The six-factor Cartan decomposition of `SL(2,ℂ)`** (Eq. (38)): the product of the
six real one-parameter factors is the `SU(2)` Cartan `KAK` with all three Euler angles
complexified — `φᶜ = φ − iε`, `θᶜ = θ − iτ`, `ψᶜ = ψ − iε̂`. -/
theorem sl2c_cartan_kak (φ ε θ τ ψ ε' : ℝ) :
    (torusFactor φ * realTorusFactor ε) * (middleRotation θ * middleBoost τ) *
      (torusFactor ψ * realTorusFactor ε') =
    complexTorusFactor ((φ : ℂ) - Complex.I * ε) *
      complexMiddleRotation ((θ : ℂ) - Complex.I * τ) *
      complexTorusFactor ((ψ : ℂ) - Complex.I * ε') := by
  rw [torusFactor_mul_realTorusFactor, middleRotation_mul_middleBoost,
    torusFactor_mul_realTorusFactor]

/-- The complex torus factor has determinant one. -/
theorem complexTorusFactor_det (z : ℂ) : (complexTorusFactor z).det = 1 := by
  rw [complexTorusFactor, Matrix.det_fin_two_of]
  rw [mul_zero, sub_zero, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- The complex middle rotation has determinant one: `cos² + sin² = 1` for the complex
angle — the factors of Eq. (38) all lie in `SL(2,ℂ)`. -/
theorem complexMiddleRotation_det (z : ℂ) : (complexMiddleRotation z).det = 1 := by
  rw [complexMiddleRotation, Matrix.det_fin_two_of]
  have hz := Complex.sin_sq_add_cos_sq (z / 2)
  linear_combination hz - (Complex.sin (z / 2)) ^ 2 * Complex.I_sq

/-! ## §C — the six one-parameter subgroups: one complex family on two axes -/

/-- `B₃ = (1/2)σ_z` — the tangent of the noncompact torus `b₃`, the §4 boost partner of
the shared Cartan direction `A₃ = (i/2)σ_z`. -/
noncomputable def sl2cBoostB3 : Matrix (Fin 2) (Fin 2) ℂ := ((1 : ℂ) / 2) • pauliZ

/-- **The compact rotation is the complex rotation on the real axis**: the subgroup `a₁`
of §4 is `complexMiddleRotation` at real angle. -/
theorem middleRotation_eq_complexOnAxis (θ : ℝ) :
    middleRotation θ = complexMiddleRotation (θ : ℂ) := by
  unfold middleRotation complexMiddleRotation
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.ofReal_cos, Complex.ofReal_sin]

/-- **The boost is the complex rotation on the imaginary axis**: the subgroup `b₁` is
`complexMiddleRotation` at `−iτ` — the paper's `cos ↦ cosh` complexification (§3 vs §2)
is one function on two axes. -/
theorem middleBoost_eq_complexOnAxis (τ : ℝ) :
    middleBoost τ = complexMiddleRotation (-(Complex.I * τ)) := by
  unfold middleBoost complexMiddleRotation
  have harg : (-(Complex.I * (τ : ℂ)) / 2) = -(((τ / 2 : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [harg, Complex.cos_neg, Complex.sin_neg, Complex.cos_mul_I, Complex.sin_mul_I]
      all_goals
        first
          | rfl
          | linear_combination Complex.sinh ((τ : ℂ) / 2) * Complex.I_sq

/-- **The compact torus is the complex torus on the real axis**: the subgroup `a₃`. -/
theorem torusFactor_eq_complexOnAxis (φ : ℝ) :
    torusFactor φ = complexTorusFactor (φ : ℂ) := by
  unfold torusFactor complexTorusFactor
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp
      all_goals
        congr 1
        ring

/-- **The noncompact torus is the complex torus on the imaginary axis**: the subgroup
`b₃` is `complexTorusFactor` at `−iε` — with §B's pair collapses, all six one-parameter
subgroups of `SL(2,ℂ)` are the three complex families `complexTorusFactor`,
`complexMiddleRotation` (and their product) evaluated on the real and imaginary axes. -/
theorem realTorusFactor_eq_complexOnAxis (ε : ℝ) :
    realTorusFactor ε = complexTorusFactor (-(Complex.I * ε)) := by
  unfold realTorusFactor complexTorusFactor
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Complex.ofReal_exp]
      all_goals
        congr 1
        first
          | ring1
          | linear_combination ((ε : ℂ) / 2) * Complex.I_sq
          | linear_combination (-(ε : ℂ) / 2) * Complex.I_sq

/-! ## §D — the `sl(2,ℂ)` relations completed and the chiral split (Eqs. (40)–(43)) -/

/-- **The mixed `[A, B]` relations of Eq. (40)**: the three vanishing diagonal brackets
and the six cyclic mixed brackets, on the `su2Tangent` and `su11Tangent` carriers with
the §4 boost `B₃ = (1/2)σ_z`. -/
theorem sl2c_cross_commutators :
    (su2TangentA1 * su11TangentB1 - su11TangentB1 * su2TangentA1 = 0) ∧
    (su2TangentA2 * su11TangentB2 - su11TangentB2 * su2TangentA2 = 0) ∧
    (su2TangentA3 * sl2cBoostB3 - sl2cBoostB3 * su2TangentA3 = 0) ∧
    (su2TangentA1 * su11TangentB2 - su11TangentB2 * su2TangentA1 = sl2cBoostB3) ∧
    (su2TangentA1 * sl2cBoostB3 - sl2cBoostB3 * su2TangentA1 = -su11TangentB2) ∧
    (su2TangentA2 * sl2cBoostB3 - sl2cBoostB3 * su2TangentA2 = su11TangentB1) ∧
    (su2TangentA2 * su11TangentB1 - su11TangentB1 * su2TangentA2 = -sl2cBoostB3) ∧
    (su2TangentA3 * su11TangentB1 - su11TangentB1 * su2TangentA3 = su11TangentB2) ∧
    (su2TangentA3 * su11TangentB2 - su11TangentB2 * su2TangentA3 = -su11TangentB1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [su2TangentA1, su2TangentA2, su2TangentA3, su11TangentB1, su11TangentB2,
        sl2cBoostB3]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pauliX_sq, pauliY_sq, pauliZ_sq,
        pauliX_mul_pauliY, pauliY_mul_pauliX, pauliY_mul_pauliZ, pauliZ_mul_pauliY,
        pauliZ_mul_pauliX, pauliX_mul_pauliZ, smul_smul]
      match_scalars
      all_goals
        first
          | ring1
          | linear_combination (Complex.I / 2) * Complex.I_sq
          | linear_combination (-(Complex.I) / 2) * Complex.I_sq
          | linear_combination (Complex.I / 4) * Complex.I_sq
          | linear_combination (-(Complex.I) / 4) * Complex.I_sq
          | linear_combination ((1 : ℂ) / 4) * Complex.I_sq
          | linear_combination (-(1 : ℂ) / 4) * Complex.I_sq
          | linear_combination ((1 : ℂ) / 2) * Complex.I_sq
          | linear_combination (-(1 : ℂ) / 2) * Complex.I_sq

/-- **The boost–boost relations of Eq. (40)** missing from `su11_sign_flip`:
`[B₂,B₃] = −A₁` and `[B₃,B₁] = −A₂` — with the §4 boost `B₃`, the pure boosts close on
*minus* the rotations: boosts do not form a subalgebra. -/
theorem sl2c_boost_boost :
    (su11TangentB2 * sl2cBoostB3 - sl2cBoostB3 * su11TangentB2 = -su2TangentA1) ∧
    (sl2cBoostB3 * su11TangentB1 - su11TangentB1 * sl2cBoostB3 = -su2TangentA2) := by
  refine ⟨?_, ?_⟩ <;>
    · simp only [su2TangentA1, su2TangentA2, su11TangentB1, su11TangentB2, sl2cBoostB3]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
        pauliY_mul_pauliZ, pauliZ_mul_pauliY, pauliZ_mul_pauliX, pauliX_mul_pauliZ]
      match_scalars
      all_goals ring1

/-- `X₁ = (i/2)(A₁ + iB₁)` — the first left (undotted) Weyl generator (Eq. (41)). -/
noncomputable def weylLeft1 : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (su2TangentA1 + Complex.I • su11TangentB1)
/-- `X₂ = (i/2)(A₂ + iB₂)`. -/
noncomputable def weylLeft2 : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (su2TangentA2 + Complex.I • su11TangentB2)
/-- `X₃ = (i/2)(A₃ + iB₃)`. -/
noncomputable def weylLeft3 : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (su2TangentA3 + Complex.I • sl2cBoostB3)
/-- `Y₁ = (i/2)(A₁ − iB₁)` — the first right (dotted) Weyl generator. -/
noncomputable def weylRight1 : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (su2TangentA1 - Complex.I • su11TangentB1)
/-- `Y₂ = (i/2)(A₂ − iB₂)`. -/
noncomputable def weylRight2 : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (su2TangentA2 - Complex.I • su11TangentB2)
/-- `Y₃ = (i/2)(A₃ − iB₃)`. -/
noncomputable def weylRight3 : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (su2TangentA3 - Complex.I • sl2cBoostB3)

/-- **The left generators in closed form**: `X = (−σ_x/2, σ_y/2, −σ_z/2)` — the
fundamental representation realizes the left `su(2)` on half-Pauli matrices. -/
theorem weylLeft_closed_form :
    weylLeft1 = (-(1 : ℂ) / 2) • pauliX ∧
    weylLeft2 = ((1 : ℂ) / 2) • pauliY ∧
    weylLeft3 = (-(1 : ℂ) / 2) • pauliZ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [weylLeft1, weylLeft2, weylLeft3, su2TangentA1, su2TangentA2, su2TangentA3,
        su11TangentB1, su11TangentB2, sl2cBoostB3]
      match_scalars
      all_goals
        first
          | ring1
          | linear_combination (Complex.I / 2) * Complex.I_sq
          | linear_combination (-(Complex.I) / 2) * Complex.I_sq
          | linear_combination ((1 : ℂ) / 2) * Complex.I_sq
          | linear_combination (-(1 : ℂ) / 2) * Complex.I_sq

/-- **The right generators vanish** (Eqs. (41)–(44)): in the fundamental representation
`Y₁ = Y₂ = Y₃ = 0` — the fundamental of `SL(2,ℂ)` is the *left-handed* (undotted,
`(1/2, 0)`) Weyl spinor; the dotted factor of the local `SU(2)⊗SU(2)` acts trivially. -/
theorem weylRight_eq_zero : weylRight1 = 0 ∧ weylRight2 = 0 ∧ weylRight3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [weylRight1, weylRight2, weylRight3, su2TangentA1, su2TangentA2, su2TangentA3,
        su11TangentB1, su11TangentB2, sl2cBoostB3]
      match_scalars
      all_goals ring1

/-- **The left generators close on `su(2)`** (Eq. (42)): `[X_k, X_l] = iε_{klm} X_m` —
one of the two commuting `su(2)`'s of the local isomorphism `SL(2,ℂ) ≃ SU(2)⊗SU(2)`
(Eq. (44)); the other acts as zero here (`weylRight_eq_zero`). -/
theorem weylLeft_su2 :
    (weylLeft1 * weylLeft2 - weylLeft2 * weylLeft1 = Complex.I • weylLeft3) ∧
    (weylLeft2 * weylLeft3 - weylLeft3 * weylLeft2 = Complex.I • weylLeft1) ∧
    (weylLeft3 * weylLeft1 - weylLeft1 * weylLeft3 = Complex.I • weylLeft2) := by
  obtain ⟨h1, h2, h3⟩ := weylLeft_closed_form
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [h1, h2, h3]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
        pauliX_mul_pauliY, pauliY_mul_pauliX, pauliY_mul_pauliZ, pauliZ_mul_pauliY,
        pauliZ_mul_pauliX, pauliX_mul_pauliZ]
      match_scalars
      all_goals ring1

end Physlib.QuantumMechanics.ComplexAction.CartanDecompositionLorentzGroup

end
