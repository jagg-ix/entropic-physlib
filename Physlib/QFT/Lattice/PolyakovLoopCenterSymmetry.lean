/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# The Polyakov loop, center symmetry, and the deconfinement order parameter

Ports `lean4/QCDVortex/PolyakovLoop.lean` of the qcd-vortex-entanglement tree (Lean layer own
authorship; finite-temperature SU(N) gauge theory, Svetitsky–Yaffe context):

* `centerElement_norm`, `center_preserves_norm` — the `Z(N)` center acts on the Polyakov loop
  by unit-modulus phases, so `‖L‖` is the center-invariant order parameter;
* `polyakovFreeEnergy` `F_q = −T·log‖L‖` — the static quark free energy: zero on the unit
  circle, nonnegative on the physical band `0 < ‖L‖ ≤ 1` (`deconfined_energy_nonneg`), and
  antitone in `‖L‖` (`freeEnergy_antitone`) — more deconfined is cheaper;
* `polyakovSusceptibility` — `χ_L = ⟨‖L‖²⟩ − ⟨‖L‖⟩² ≥ 0` given the moment inequality, with
  the equality characterisation.

**Honest layering.**  Exact analysis on the observable formulas; that `⟨L⟩ = 0` in the
confined phase (unbroken center) and the transition itself are the statistical-mechanics
layer, cited not re-proven.  Companion module: `WilsonLoopAreaLaw` (the spatial confinement
signal to this temporal one).

## References

* B. Svetitsky, L. G. Yaffe, *Critical behavior at finite-temperature confinement
  transitions*, Nucl. Phys. B **210** (1982).
* Source: `lean4/QCDVortex/PolyakovLoop.lean` (own authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QFT.Lattice.PolyakovLoopCenterSymmetry

open Real Complex

/-! ## 1. Center symmetry Z(N) -/

/--
The k-th element of the Z(N) center group of SU(N):
  z_k = exp(2πi·k/N) · I_N
Here we represent it as a complex scalar (the eigenvalue).
-/
noncomputable def centerElement (N k : ℕ) : ℂ :=
  Complex.exp (2 * π * Complex.I * k / N)

/-- Center elements have unit norm: ‖z_k‖ = 1 for N > 0. -/
theorem centerElement_norm (N k : ℕ) :
    ‖centerElement N k‖ = 1 := by
  simp only [centerElement]
  have h : (2 * (π : ℂ) * Complex.I * (k : ℂ) / (N : ℂ)) =
           ↑((2 * Real.pi * (k : ℝ) / (N : ℝ)) : ℝ) * Complex.I := by push_cast; ring
  rw [h, ← Circle.coe_exp]
  exact Circle.norm_coe _

/-- Z(N) transformation preserves the norm of L: ‖z_k · L‖ = ‖L‖. -/
theorem center_preserves_norm (L : ℂ) (N k : ℕ) :
    ‖centerElement N k * L‖ = ‖L‖ := by
  rw [norm_mul, centerElement_norm N k, one_mul]

/-! ## 2. Polyakov loop configuration -/

/--
Polyakov loop configuration: normalized trace L ∈ ℂ with ‖L‖ ≤ 1
(from SU(N) unitarity: |Tr[U]| ≤ NC, normalized by 1/NC).
-/
structure PolyakovConfig where
  L     : ℂ
  hBound : ‖L‖ ≤ 1

/-! ## 3. Static quark free energy -/

/--
Static quark free energy at temperature T > 0:
  F_q = −T · log‖L‖

Extended by 0 at ‖L‖ = 0 (boundary convention; physically F_q → +∞).
-/
noncomputable def polyakovFreeEnergy (T : ℝ) (L : ℂ) : ℝ :=
  if ‖L‖ = 0 then 0
  else -T * Real.log ‖L‖

/-- Confined phase (‖L‖ = 0): boundary value 0. -/
theorem polyakovFreeEnergy_confined (T : ℝ) (L : ℂ) (h : ‖L‖ = 0) :
    polyakovFreeEnergy T L = 0 :=
  if_pos h

/-- Deconfined phase (‖L‖ > 0): F_q = −T log‖L‖. -/
theorem polyakovFreeEnergy_deconfined (T : ℝ) (L : ℂ) (h : 0 < ‖L‖) :
    polyakovFreeEnergy T L = -T * Real.log ‖L‖ :=
  if_neg (ne_of_gt h)

/-- At ‖L‖ = 1 (pure phase / fully deconfined), F_q = 0. -/
theorem polyakovFreeEnergy_unit_circle (T : ℝ) (L : ℂ) (h : ‖L‖ = 1) :
    polyakovFreeEnergy T L = 0 := by
  rw [polyakovFreeEnergy_deconfined T L (by linarith [h.symm ▸ one_pos])]
  simp [h, Real.log_one]

/--
In the deconfined phase with T > 0 and ‖L‖ ∈ (0, 1], F_q ≥ 0.
This is because log‖L‖ ≤ 0 (since ‖L‖ ≤ 1) and −T·(≤0) ≥ 0.
-/
theorem deconfined_energy_nonneg {T : ℝ} (hT : 0 < T) {L : ℂ}
    (hL_pos : 0 < ‖L‖) (hL_le : ‖L‖ ≤ 1) :
    0 ≤ polyakovFreeEnergy T L := by
  rw [polyakovFreeEnergy_deconfined T L hL_pos]
  have hlog : Real.log ‖L‖ ≤ 0 :=
    Real.log_nonpos hL_pos.le hL_le
  have hmul : T * Real.log ‖L‖ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hT.le hlog
  linarith

/-! ## 4. Deconfinement criterion -/

/--
A Polyakov loop configuration is deconfined if ‖L‖ > 0
(Z(N) center symmetry spontaneously broken).
-/
def isDeconfined (normL : ℝ) : Prop := 0 < normL

/-- Deconfinement implies finite (nonneg) free energy at T > 0. -/
theorem deconfined_implies_bounded_energy {T : ℝ} (hT : 0 < T) {L : ℂ}
    (hD : isDeconfined ‖L‖) (hB : ‖L‖ ≤ 1) :
    0 ≤ polyakovFreeEnergy T L :=
  deconfined_energy_nonneg hT hD hB

/--
Rising free energy: larger ‖L‖ ↔ lower free energy (more deconfined).
-/
theorem freeEnergy_antitone {T : ℝ} (hT : 0 < T) {L₁ L₂ : ℂ}
    (h1 : 0 < ‖L₁‖) (h2 : 0 < ‖L₂‖)
    (h12 : ‖L₁‖ ≤ ‖L₂‖) :
    polyakovFreeEnergy T L₂ ≤ polyakovFreeEnergy T L₁ := by
  rw [polyakovFreeEnergy_deconfined T L₁ h1,
      polyakovFreeEnergy_deconfined T L₂ h2]
  have hlog : Real.log ‖L₁‖ ≤ Real.log ‖L₂‖ :=
    Real.log_le_log h1 h12
  nlinarith

/-! ## 5. Polyakov susceptibility -/

/--
Polyakov loop susceptibility χ_L = ⟨‖L‖²⟩ − ⟨‖L‖⟩²

Peaks at the deconfinement transition (diverges at T_c in infinite volume).
Vanishes in both pure phases at large volume.
-/
noncomputable def polyakovSusceptibility (L_sq_avg L_avg_sq : ℝ) : ℝ :=
  L_sq_avg - L_avg_sq

/-- Susceptibility is nonneg when ⟨‖L‖²⟩ ≥ ⟨‖L‖⟩² (Cauchy–Schwarz). -/
theorem polyakovSusceptibility_nonneg {L_sq_avg L_avg_sq : ℝ}
    (h : L_avg_sq ≤ L_sq_avg) :
    0 ≤ polyakovSusceptibility L_sq_avg L_avg_sq := by
  simp [polyakovSusceptibility]; linarith

/-- χ_L = 0 iff ⟨‖L‖²⟩ = ⟨‖L‖⟩². -/
theorem polyakovSusceptibility_zero_iff {a b : ℝ} :
    polyakovSusceptibility a b = 0 ↔ a = b := by
  simp [polyakovSusceptibility, sub_eq_zero]

end Physlib.QFT.Lattice.PolyakovLoopCenterSymmetry

end
