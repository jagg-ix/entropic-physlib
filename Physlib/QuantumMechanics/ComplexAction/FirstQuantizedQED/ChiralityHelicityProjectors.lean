/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.DiracProjectors
public import Physlib.Relativity.CliffordAlgebra
public import Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

/-!
# Bennett's chirality and helicity projectors (Eqs. 20–21)

Formalizes the spin/chirality/helicity projectors of *A. F. Bennett, "First Quantized Electrodynamics",
arXiv:1406.0750v3*, Eqs. 20–21, reusing the involution → projector machinery of `FirstQuantizedQED.DiracProjectors`:

* **chirality** `P_± = (1 ± γ⁵)/2` — from the involution `γ⁵` (`γ5² = 1`);
* **helicity** `P_± = (1 ± σ·p̂)/2` — from the involution `σ·p̂` (`(σ·p̂)² = 1` for a unit momentum `p̂`,
  Bennett's ultrarelativistic helicity eigenvalue `±φ_p`).

Each is `bennettProjU`/`bennettProjV` of `FirstQuantizedQED.DiracProjectors` (now size-polymorphic) at the appropriate
involution, so the completeness / idempotency / orthogonality come straight from the generic projector
lemmas.

* **§A — chirality** (`γ5_sq`, `chirality_projectors`). `γ⁵² = 1`, so `(1 ± γ⁵)/2` are complementary
  orthogonal idempotents (the left/right chirality projectors).
* **§B — helicity** (`sigmaDot_involution`, `helicity_projectors`). For a unit momentum `p̂`
  (`dotR p̂ p̂ = 1`), `(σ·p̂)² = 1` (`Dirac.PauliEquationSpinOrbit.sigmaDot_sq`), so `(1 ± σ·p̂)/2` are the
  helicity-`±½` projectors.
* **§C — spin** (`γ5γ3_sq`, `spin_projectors`). For the rest-frame `z`-axis spin (`s̸ = γ³`),
  `(γ⁵γ³)² = 1`, so `(1 ∓ γ⁵s̸)/2` are the spin-`±½` projectors (Eq. 20).
* **§D — the discrete symmetries** (`parity_sq`, `tpc_matrix_sq`). Bennett's `C, P, T, TPC` matrices
  (Eqs. 7–10): parity `P = γ⁰` is an involution (`P² = I₄`), and the TPC matrix `−iγ⁵` satisfies
  `(−iγ⁵)² = −I₄` — the fermionic `(TPC)² = −1`.

## References

* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3 (2020), Eqs. 20–21.
* Repo dependencies: `FirstQuantizedQED.DiracProjectors` (`bennettProjU/V`, the projector lemmas), `Relativity.CliffordAlgebra`
  (`γ5`), `Dirac.PauliEquationSpinOrbit` (`sigmaDot`, `sigmaDot_sq`, `dotR`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors

open Matrix
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.DiracProjectors
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

/-! ## §A — the chirality projectors `(1 ± γ⁵)/2` -/

/-- **`γ⁵² = 1`** — the chirality matrix is an involution (`γ5 = iγ⁰γ¹γ²γ³`). -/
theorem γ5_sq : γ5 * γ5 = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [γ5, γ0, γ1, γ2, γ3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **[Bennett — chirality] The left/right chirality projectors `(1 ∓ γ⁵)/2` are complementary orthogonal
idempotents.** `P_L = (1−γ⁵)/2 = bennettProjU γ⁵`, `P_R = (1+γ⁵)/2 = bennettProjV γ⁵`: `P_L + P_R = I₄`,
`P_L² = P_L`, `P_R² = P_R`, `P_R P_L = 0` — from `γ5² = 1` via the `FirstQuantizedQED.DiracProjectors` lemmas. -/
theorem chirality_projectors :
    bennettProjU γ5 + bennettProjV γ5 = 1
      ∧ bennettProjU γ5 * bennettProjU γ5 = bennettProjU γ5
      ∧ bennettProjV γ5 * bennettProjV γ5 = bennettProjV γ5
      ∧ bennettProjV γ5 * bennettProjU γ5 = 0 :=
  ⟨bennett_proj_complete γ5, bennett_projU_idem γ5 γ5_sq, bennett_projV_idem γ5 γ5_sq,
   bennett_proj_orthogonal γ5 γ5_sq⟩

/-! ## §B — the helicity projectors `(1 ± σ·p̂)/2` -/

/-- **For a unit momentum, `σ·p̂` is an involution** `(σ·p̂)² = 1` (`sigmaDot_sq` with `dotR p̂ p̂ = 1`). -/
theorem sigmaDot_involution (p : Fin 3 → ℝ) (hp : dotR p p = 1) :
    sigmaDot p * sigmaDot p = 1 := by
  rw [sigmaDot_sq, hp]; norm_num

/-- **[Bennett Eq. 21 — helicity] The helicity-`±½` projectors `(1 ∓ σ·p̂)/2` are complementary orthogonal
idempotents** for a unit momentum `p̂`. `bennettProjU/V (σ·p̂)`: complete, idempotent, orthogonal — from
`(σ·p̂)² = 1` via the `FirstQuantizedQED.DiracProjectors` lemmas. These are the helicity eigenprojectors that, in
Bennett's ultrarelativistic limit, coincide with the chirality projectors (eigenvalues `±φ_p`). -/
theorem helicity_projectors (p : Fin 3 → ℝ) (hp : dotR p p = 1) :
    bennettProjU (sigmaDot p) + bennettProjV (sigmaDot p) = 1
      ∧ bennettProjU (sigmaDot p) * bennettProjU (sigmaDot p) = bennettProjU (sigmaDot p)
      ∧ bennettProjV (sigmaDot p) * bennettProjV (sigmaDot p) = bennettProjV (sigmaDot p)
      ∧ bennettProjV (sigmaDot p) * bennettProjU (sigmaDot p) = 0 :=
  ⟨bennett_proj_complete (sigmaDot p), bennett_projU_idem (sigmaDot p) (sigmaDot_involution p hp),
   bennett_projV_idem (sigmaDot p) (sigmaDot_involution p hp),
   bennett_proj_orthogonal (sigmaDot p) (sigmaDot_involution p hp)⟩

/-! ## §C — the rest-frame spin projector `(1 ∓ γ⁵γ³)/2` (Eq. 20) -/

/-- **`(γ⁵γ³)² = 1`** — the rest-frame `z`-axis spin slash `γ⁵s̸` (`s = ẑ`, `s̸ = γ³`) is an involution
(`γ³² = −1`, `γ⁵` anticommutes with `γ³`). -/
theorem γ5γ3_sq : (γ5 * γ3) * (γ5 * γ3) = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [γ5, γ1, γ2, γ3, γ0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **[Bennett Eq. 20 — spin] The rest-frame spin-`±½` projectors `(1 ∓ γ⁵γ³)/2` are complementary
orthogonal idempotents.** With the `z`-axis spin `s = ẑ`, `P(±s) = (I₄ ∓ γ⁵s̸)/2 = bennettProjU/V (γ⁵γ³)`:
complete, idempotent, orthogonal — from `(γ⁵γ³)² = 1`. (A general spin direction is a Lorentz boost of
this.) -/
theorem spin_projectors :
    bennettProjU (γ5 * γ3) + bennettProjV (γ5 * γ3) = 1
      ∧ bennettProjU (γ5 * γ3) * bennettProjU (γ5 * γ3) = bennettProjU (γ5 * γ3)
      ∧ bennettProjV (γ5 * γ3) * bennettProjV (γ5 * γ3) = bennettProjV (γ5 * γ3)
      ∧ bennettProjV (γ5 * γ3) * bennettProjU (γ5 * γ3) = 0 :=
  ⟨bennett_proj_complete (γ5 * γ3), bennett_projU_idem (γ5 * γ3) γ5γ3_sq,
   bennett_projV_idem (γ5 * γ3) γ5γ3_sq, bennett_proj_orthogonal (γ5 * γ3) γ5γ3_sq⟩

/-! ## §D — the discrete-symmetry matrices `C, P, T, TPC` (Eqs. 7–10) -/

/-- **[Bennett Eq. 8 — parity] `P² = I₄`.** The parity matrix `P = γ⁰` (`(Pψ)(t,x,τ) = γ⁰ψ(t,−x,τ)`)
satisfies `γ⁰² = 1` — parity is an involution. -/
theorem parity_sq : (γ0 : Matrix (Fin 4) (Fin 4) ℂ) * γ0 = 1 := γ0_mul_γ0

/-- **[Bennett Eq. 10 — TPC] The TPC matrix `−iγ⁵` squares to `−I₄`.** `(TPCψ)(x,τ) = −iγ⁵ψ(−x,τ)`; the
matrix `−iγ⁵` satisfies `(−iγ⁵)² = −γ⁵² = −1` — the fermionic `(TPC)² = −1` (consistent with the spin-½
double cover). -/
theorem tpc_matrix_sq : ((-Complex.I) • γ5) * ((-Complex.I) • γ5) = (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [smul_mul_smul_comm, γ5_sq, neg_mul_neg, Complex.I_mul_I, neg_one_smul]

/-! ## §E — the general-direction spin slash `γ⁵s̸` (Eq. 20, any spin direction)

The Clifford relations needed to prove `(γ⁵s̸)² = |s|²·1` for a general spatial spin `s̸ = sⁱγⁱ`. -/

theorem gamma1_sq : γ1 * γ1 = (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [γ1]; ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma2_sq : γ2 * γ2 = (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [γ2]; ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma3_sq : γ3 * γ3 = (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [γ3]; ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma12_anticomm : γ1 * γ2 + γ2 * γ1 = 0 := by
  simp only [γ1, γ2]; ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma13_anticomm : γ1 * γ3 + γ3 * γ1 = 0 := by
  simp only [γ1, γ3]; ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma23_anticomm : γ2 * γ3 + γ3 * γ2 = 0 := by
  simp only [γ2, γ3]; ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma51_anticomm : γ5 * γ1 = -(γ1 * γ5) := by
  simp only [γ5, γ0, γ1, γ2, γ3]; ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma52_anticomm : γ5 * γ2 = -(γ2 * γ5) := by
  simp only [γ5, γ0, γ1, γ2, γ3]; ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
theorem gamma53_anticomm : γ5 * γ3 = -(γ3 * γ5) := by
  simp only [γ5, γ0, γ1, γ2, γ3]; ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- **The spatial spin slash** `s̸ = s¹γ¹ + s²γ² + s³γ³` (Bennett's `φp̸`-type spin 4-vector, spatial part). -/
noncomputable def spinSlash (s : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (s 0 : ℂ) • γ1 + (s 1 : ℂ) • γ2 + (s 2 : ℂ) • γ3

/-- **The spin slash squares to `−|s|²·1`** `s̸² = −(s₁²+s₂²+s₃²)·1` (the Clifford relation
`{γⁱ,γʲ} = 2g^{ij}`, spatial `g^{ii} = −1`). -/
theorem spinSlash_sq (s : Fin 3 → ℝ) :
    spinSlash s * spinSlash s = (-(s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 : ℝ) : ℂ) • 1 := by
  have h12 : γ1 * γ2 = -(γ2 * γ1) := eq_neg_of_add_eq_zero_left gamma12_anticomm
  have h13 : γ1 * γ3 = -(γ3 * γ1) := eq_neg_of_add_eq_zero_left gamma13_anticomm
  have h23 : γ2 * γ3 = -(γ3 * γ2) := eq_neg_of_add_eq_zero_left gamma23_anticomm
  simp only [spinSlash, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [gamma1_sq, gamma2_sq, gamma3_sq, h12, h13, h23]
  push_cast
  module

/-- **`γ⁵` anticommutes with the spin slash** `γ⁵s̸ = −s̸γ⁵`. -/
theorem gamma5_spinSlash_anticomm (s : Fin 3 → ℝ) : γ5 * spinSlash s = -(spinSlash s * γ5) := by
  simp only [spinSlash, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    gamma51_anticomm, gamma52_anticomm, gamma53_anticomm]
  module

/-- **[Bennett Eq. 20 — general spin] `(γ⁵s̸)² = |s|²·1`.** For a general spatial spin direction `s`,
`γ⁵s̸` squares to `(s₁²+s₂²+s₃²)·1` (`= −γ⁵²s̸² = −s̸² = |s|²`); for a unit spin (`|s| = 1`) it is an
involution, so `(1 ∓ γ⁵s̸)/2` are the spin-`±½` projectors in **any** direction. -/
theorem gamma5_spinSlash_sq (s : Fin 3 → ℝ) :
    (γ5 * spinSlash s) * (γ5 * spinSlash s) = ((s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 : ℝ) : ℂ) • 1 := by
  have hanti : spinSlash s * γ5 = -(γ5 * spinSlash s) := by
    rw [gamma5_spinSlash_anticomm, neg_neg]
  calc (γ5 * spinSlash s) * (γ5 * spinSlash s)
      = γ5 * (spinSlash s * γ5) * spinSlash s := by noncomm_ring
    _ = γ5 * (-(γ5 * spinSlash s)) * spinSlash s := by rw [hanti]
    _ = -(γ5 * γ5 * (spinSlash s * spinSlash s)) := by noncomm_ring
    _ = ((s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 : ℝ) : ℂ) • 1 := by rw [γ5_sq, spinSlash_sq, one_mul]; module

/-- **[Bennett Eq. 20 — general spin projectors] The spin-`±½` projectors `(1 ∓ γ⁵s̸)/2` in any direction.**
For a unit spin `s` (`s₁²+s₂²+s₃² = 1`), `γ⁵s̸` is an involution, so `bennettProjU/V (γ⁵s̸)` are complete,
idempotent and orthogonal. -/
theorem spin_projectors_general (s : Fin 3 → ℝ) (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1) :
    bennettProjU (γ5 * spinSlash s) + bennettProjV (γ5 * spinSlash s) = 1
      ∧ bennettProjU (γ5 * spinSlash s) * bennettProjU (γ5 * spinSlash s) = bennettProjU (γ5 * spinSlash s)
      ∧ bennettProjV (γ5 * spinSlash s) * bennettProjV (γ5 * spinSlash s) = bennettProjV (γ5 * spinSlash s)
      ∧ bennettProjV (γ5 * spinSlash s) * bennettProjU (γ5 * spinSlash s) = 0 := by
  have hu : (γ5 * spinSlash s) * (γ5 * spinSlash s) = 1 := by
    rw [gamma5_spinSlash_sq, hs]; simp
  exact ⟨bennett_proj_complete _, bennett_projU_idem _ hu, bennett_projV_idem _ hu,
    bennett_proj_orthogonal _ hu⟩

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors

end
