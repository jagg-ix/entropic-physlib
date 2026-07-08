/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-!
# Bennett's Dirac projectors `Λ_u, Λ_v` (Eqs. 16–17) and the Dirac energy projectors

Formalizes the spinor-projector algebra of *A. F. Bennett, "First Quantized Electrodynamics",
arXiv:1406.0750v3*, Eqs. 16–17: the forward/backward projections
`Λ_u = (m I₄ − φ p̸)/2m = uū`, `Λ_v = (m I₄ + φ p̸)/2m = −v̄v`, which satisfy completeness, idempotency and
orthogonality. The essential algebra is the **involution → projectors** fact: the on-shell slash
`s = φ p̸` has `s² = m² I₄` (the mass-shell `p̸² = −p·p = m²`, `φ² = 1`), so `u = s/m` is an involution
(`u² = 1`), and `(1 ∓ u)/2` are complementary orthogonal idempotents.

* **§A — the involution from the mass shell** (`diracInvolution`, `diracInvolution_sq`). For a matrix `s`
  with `s² = m²·1` (`m ≠ 0`), `u = s/m` satisfies `u² = 1`.
* **§B — the projectors** (`bennettProjU`, `bennettProjV`, `bennett_proj_complete`, `bennett_projU_idem`,
  `bennett_projV_idem`, `bennett_proj_orthogonal`). `Λ_u = (1−u)/2`, `Λ_v = (1+u)/2`:
  `Λ_u + Λ_v = 1`, `Λ_u² = Λ_u`, `Λ_v² = Λ_v`, `Λ_u Λ_v = 0` — exactly the relations Bennett's Eq. 17
  orthonormality (`ūu = I₂`, `v̄v = −I₂`, `ūv = 0`) implies for the projectors.
* **§C — the concrete Dirac energy projectors** (`diracHamiltonian_energy_involution`,
  `dirac_energy_projectors`). The four-spinor Dirac Hamiltonian `H` of `Dirac.FourSpinorDiracHamiltonian` has
  `H² = (p²+m²)·1 = E²·1` (`diracHamiltonian4_sq`), so `u = H/E` is an involution and the **positive/negative
  energy projectors** `(E I₄ ± H)/2E` are Bennett-type complementary idempotents — the same projector
  structure as Bennett's `Λ_u, Λ_v` with `(H, E)` in place of `(φp̸, m)`.

## References

* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3 (2020), Eqs. 16–17.
* Repo structure: `Dirac.FourSpinorDiracHamiltonian` (`diracHamiltonian4`, `diracHamiltonian4_sq`,
  `H² = (p²+m²)·1`); the Bennett mass-shell agreement is in `FirstQuantizedQED.ParametrizedDirac`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.DiracProjectors

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian

/-- 4×4 complex matrices (the Dirac four-spinor operator algebra). -/
abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ

variable {n : ℕ}

/-! ## §A — the involution `u = s/m` from the on-shell slash `s² = m²·1`

The projectors and the involution are stated for `Matrix (Fin n) (Fin n) ℂ` of **any** size `n`, so the
same algebra serves the 4×4 Dirac energy/chirality projectors and the 2×2 helicity projectors. -/

/-- **The Dirac involution** `u = s/m` from an on-shell slash `s` (= `φp̸`). -/
noncomputable def diracInvolution (m : ℝ) (s : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / m : ℂ) • s

/-- **[Bennett mass-shell] The slash gives an involution.** If `s² = m²·1` (the on-shell `p̸² = m²`) and
`m ≠ 0`, then `u = s/m` satisfies `u² = 1`. -/
theorem diracInvolution_sq (m : ℝ) (s : Matrix (Fin n) (Fin n) ℂ) (hm : m ≠ 0)
    (hs : s * s = ((m : ℂ) ^ 2) • 1) :
    diracInvolution m s * diracInvolution m s = 1 := by
  unfold diracInvolution
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  calc (1 / m : ℂ) • s * ((1 / m : ℂ) • s)
      = (1 / (m : ℂ)) • ((1 / (m : ℂ)) • (s * s)) := by push_cast; rw [smul_mul_assoc, mul_smul_comm]
    _ = (1 / (m : ℂ)) • ((1 / (m : ℂ)) • (((m : ℂ) ^ 2) • 1)) := by rw [hs]
    _ = 1 := by
        rw [smul_smul, smul_smul,
          show (1 / (m : ℂ)) * (1 / (m : ℂ)) * (m : ℂ) ^ 2 = 1 by field_simp]
        simp

/-! ## §B — the projectors `Λ_u = (1−u)/2`, `Λ_v = (1+u)/2` -/

/-- **[Bennett Eq. 16] The backward (`v`) projector** `Λ_v = (1+u)/2 = (m I₄ + φp̸)/2m`. -/
noncomputable def bennettProjV (u : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (1 + u)

/-- **[Bennett Eq. 16] The forward (`u`) projector** `Λ_u = (1−u)/2 = (m I₄ − φp̸)/2m`. -/
noncomputable def bennettProjU (u : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (1 - u)

/-- **[Bennett Eq. 16] Completeness** `Λ_u + Λ_v = I₄`. -/
theorem bennett_proj_complete (u : Matrix (Fin n) (Fin n) ℂ) : bennettProjU u + bennettProjV u = 1 := by
  unfold bennettProjU bennettProjV; module

/-- **[Bennett Eq. 16] `Λ_v` is idempotent** `Λ_v² = Λ_v` (from `u² = 1`). -/
theorem bennett_projV_idem (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * u = 1) :
    bennettProjV u * bennettProjV u = bennettProjV u := by
  unfold bennettProjV
  have e : (1 + u) * (1 + u) = (2 : ℂ) • (1 + u) := by
    have h2 : (1 + u) * (1 + u) = 1 + u + u + u * u := by noncomm_ring
    rw [h2, hu]; module
  calc (1 / 2 : ℂ) • (1 + u) * ((1 / 2 : ℂ) • (1 + u))
      = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • ((1 + u) * (1 + u))) := by rw [smul_mul_assoc, mul_smul_comm]
    _ = (1 / 2 : ℂ) • (1 + u) := by rw [e]; module

/-- **[Bennett Eq. 16] `Λ_u` is idempotent** `Λ_u² = Λ_u`. -/
theorem bennett_projU_idem (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * u = 1) :
    bennettProjU u * bennettProjU u = bennettProjU u := by
  unfold bennettProjU
  have e : (1 - u) * (1 - u) = (2 : ℂ) • (1 - u) := by
    have h2 : (1 - u) * (1 - u) = 1 - u - u + u * u := by noncomm_ring
    rw [h2, hu]; module
  calc (1 / 2 : ℂ) • (1 - u) * ((1 / 2 : ℂ) • (1 - u))
      = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • ((1 - u) * (1 - u))) := by rw [smul_mul_assoc, mul_smul_comm]
    _ = (1 / 2 : ℂ) • (1 - u) := by rw [e]; module

/-- **[Bennett Eq. 16] The projectors are orthogonal** `Λ_v Λ_u = 0` (the forward and backward subspaces are
disjoint). -/
theorem bennett_proj_orthogonal (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * u = 1) :
    bennettProjV u * bennettProjU u = 0 := by
  unfold bennettProjV bennettProjU
  have e : (1 + u) * (1 - u) = (0 : Matrix (Fin n) (Fin n) ℂ) := by
    have h2 : (1 + u) * (1 - u) = 1 - u + u - u * u := by noncomm_ring
    rw [h2, hu]; module
  calc (1 / 2 : ℂ) • (1 + u) * ((1 / 2 : ℂ) • (1 - u))
      = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • ((1 + u) * (1 - u))) := by rw [smul_mul_assoc, mul_smul_comm]
    _ = 0 := by rw [e]; module

/-! ## §C — the concrete Dirac energy projectors from `Dirac.FourSpinorDiracHamiltonian` -/

/-- **[Link] The Dirac Hamiltonian over its energy is an involution.** From `H² = (p²+m²)·1 = E²·1`
(`diracHamiltonian4_sq`, `E = √(p²+m²)`), `u = H/E` satisfies `u² = 1` — the on-shell condition that makes
the energy projectors Bennett-type idempotents. -/
theorem diracHamiltonian_energy_involution (p1 p2 p3 m : ℝ)
    (hE : 0 < p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2) :
    diracInvolution (Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2)) (diracHamiltonian4 p1 p2 p3 m)
        * diracInvolution (Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2)) (diracHamiltonian4 p1 p2 p3 m)
      = 1 := by
  apply diracInvolution_sq
  · exact (Real.sqrt_pos.mpr hE).ne'
  · rw [diracHamiltonian4_sq]
    congr 1
    rw [← Complex.ofReal_pow, Real.sq_sqrt hE.le]

/-- **[Link — Bennett Eq. 16 for the Dirac Hamiltonian] The positive/negative energy projectors
`(E I₄ ± H)/2E` are complete, idempotent and orthogonal.** With `u = H/E` (`E = √(p²+m²)`) the Dirac energy
projectors are Bennett-type projectors — the same `(1 ∓ u)/2` structure as `Λ_u, Λ_v`, with `(H, E)` in
place of `(φp̸, m)`. -/
theorem dirac_energy_projectors (p1 p2 p3 m : ℝ) (hE : 0 < p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2) :
    let u := diracInvolution (Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2)) (diracHamiltonian4 p1 p2 p3 m)
    bennettProjU u + bennettProjV u = 1
      ∧ bennettProjU u * bennettProjU u = bennettProjU u
      ∧ bennettProjV u * bennettProjV u = bennettProjV u
      ∧ bennettProjV u * bennettProjU u = 0 := by
  intro u
  have hu : u * u = 1 := diracHamiltonian_energy_involution p1 p2 p3 m hE
  exact ⟨bennett_proj_complete u, bennett_projU_idem u hu, bennett_projV_idem u hu,
    bennett_proj_orthogonal u hu⟩

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.DiracProjectors

end
