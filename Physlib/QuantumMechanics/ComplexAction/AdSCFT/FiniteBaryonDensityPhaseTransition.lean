/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Positivity

/-!
# Holographic thermodynamics at finite baryon density: the second-order transition at `μ = m`

A. Karch and A. O'Bannon, *Holographic thermodynamics at finite baryon density: some exact results*,
JHEP 11 (2007) 074, use the D3/D7 probe-brane system to compute the exact zero-temperature thermodynamics
of the flavour hypermultiplets of `𝒩 = 2` matter in `𝒩 = 4` `SU(N_c)` super-Yang–Mills at finite baryon
chemical potential `μ` and quark mass `m`. Because the warp factors cancel in the DBI action, the embedding
integrates exactly, and the on-shell (black-hole embedding) results are closed forms in `μ` and `m`.

Writing `γ𝒩(2πα')^k` prefactors as `γN`, `t = 2πα'`, this formalizes their Eqs. 2.20–2.22:

* **§A — the exact condensate, density and free energy.** the quark condensate `c = γN t³ (μ²−m²) m`
  (`condensate`), the baryon density `d = γN t⁴ (μ²−m²) μ` (`density`), and the renormalized on-shell action
  `S_ren = ¼ γN t⁴ (μ²−m²)²` (`sRen`); the grand potential is `Ω = −S_ren` (`grandPotential`). The
  thermodynamic relation `d = ∂S_ren/∂μ = −∂Ω/∂μ` holds exactly (`sRen_hasDerivAt`), and `S_ren ≥ 0`
  (`sRen_nonneg`), so the black-hole embedding is favoured.
* **§B — the second-order phase transition at `μ = m`.** the condensate, density and free energy all
  vanish at `μ = m` (`condensate_transition`, `density_transition`, `grandPotential_transition`); `Ω` and
  its first `μ`-derivative are zero there (`grandPotential_hasDerivAt_transition`) while the second
  derivative jumps to `−2 γN t⁴ m²` (`density_slope_transition`, since `∂²Ω/∂μ² = −∂d/∂μ`) — a genuine
  second-order transition.
* **§C — mean-field critical exponents.** for `μ = m + ε` the order parameters factor as
  `c = γN t³ m (2m+ε) ε ∼ ε`, `d = γN t⁴ (m+ε)(2m+ε) ε ∼ ε`, `Ω = −¼ γN t⁴ (2m+ε)² ε² ∼ ε²`
  (`condensate_shift`, `density_shift`, `grandPotential_shift`), the mean-field values `c ∼ ε`, `d ∼ ε`,
  `Ω ∼ ε²`; the order-parameter slope `∂c/∂μ = 2 γN t³ m²` at the transition (`condensate_slope_transition`).
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.FiniteBaryonDensityPhaseTransition


/-- **The quark condensate** `⟨𝒪_m⟩ ∝ c = γN t³ (μ²−m²) m` (Eq. 2.20), `t = 2πα'`. It is the order
parameter of a charged boson in a chemical potential: a wine-bottle potential whose minimum leaves the
origin once `μ > m`. -/
def condensate (γN t μ m : ℝ) : ℝ := γN * t ^ 3 * ((μ ^ 2 - m ^ 2) * m)

/-- **The baryon number density** `⟨J^t⟩ = d = γN t⁴ (μ²−m²) μ` (Eq. 2.20). It is nonzero only for
`μ > m`: below the mass gap the chemical potential is trivial. -/
def density (γN t μ m : ℝ) : ℝ := γN * t ^ 4 * ((μ ^ 2 - m ^ 2) * μ)

/-- **The renormalized on-shell action** `S_ren = ¼ γN t⁴ (μ²−m²)²` (Eq. 2.22) of the black-hole
embedding. -/
noncomputable def sRen (γN t μ m : ℝ) : ℝ := γN * t ^ 4 / 4 * (μ ^ 2 - m ^ 2) ^ 2

/-- **The grand potential** `Ω = −S_ren`. -/
noncomputable def grandPotential (γN t μ m : ℝ) : ℝ := -sRen γN t μ m

/-- **The thermodynamic relation** `d = ∂S_ren/∂μ` (`= −∂Ω/∂μ`): differentiating the exact free energy
(Eq. 2.22) in the chemical potential reproduces the exact density (Eq. 2.20). -/
lemma sRen_hasDerivAt (γN t m μ : ℝ) :
    HasDerivAt (fun x => sRen γN t x m) (density γN t μ m) μ := by
  have hb : HasDerivAt (fun x : ℝ => x ^ 2 - m ^ 2) (2 * μ) μ := by
    simpa using (hasDerivAt_pow 2 μ).sub_const (m ^ 2)
  have h := (hb.pow 2).const_mul (γN * t ^ 4 / 4)
  simp only [sRen, density]
  exact h.congr_deriv (by ring)

/-- **The black-hole embedding is thermodynamically favoured**: `S_ren ≥ 0` for `γN ≥ 0`. -/
lemma sRen_nonneg (γN t μ m : ℝ) (hγN : 0 ≤ γN) : 0 ≤ sRen γN t μ m := by
  unfold sRen
  positivity

/-- The `μ`-derivative of the density, `∂d/∂μ = γN t⁴ (3μ²−m²)`. -/
lemma density_hasDerivAt (γN t m μ : ℝ) :
    HasDerivAt (fun x => density γN t x m) (γN * t ^ 4 * (3 * μ ^ 2 - m ^ 2)) μ := by
  have hb : HasDerivAt (fun x : ℝ => x ^ 2 - m ^ 2) (2 * μ) μ := by
    simpa using (hasDerivAt_pow 2 μ).sub_const (m ^ 2)
  have h := (hb.mul (hasDerivAt_id μ)).const_mul (γN * t ^ 4)
  simp only [density]
  exact h.congr_deriv (by simp only [id_eq]; ring)

/-- The `μ`-derivative of the condensate, `∂c/∂μ = 2 γN t³ μ m`. -/
lemma condensate_hasDerivAt (γN t m μ : ℝ) :
    HasDerivAt (fun x => condensate γN t x m) (2 * γN * t ^ 3 * μ * m) μ := by
  have hb : HasDerivAt (fun x : ℝ => x ^ 2 - m ^ 2) (2 * μ) μ := by
    simpa using (hasDerivAt_pow 2 μ).sub_const (m ^ 2)
  have h := (hb.mul_const m).const_mul (γN * t ^ 3)
  simp only [condensate]
  exact h.congr_deriv (by ring)


/-- The condensate vanishes at the transition `μ = m`. -/
lemma condensate_transition (γN t m : ℝ) : condensate γN t m m = 0 := by
  unfold condensate; ring

/-- The baryon density vanishes at the transition `μ = m` — the order parameter is continuous. -/
lemma density_transition (γN t m : ℝ) : density γN t m m = 0 := by
  unfold density; ring

/-- The free energy vanishes at the transition `μ = m`. -/
lemma sRen_transition (γN t m : ℝ) : sRen γN t m m = 0 := by
  unfold sRen; ring

/-- The grand potential vanishes at the transition `μ = m`, matching the trivial (Minkowski) phase. -/
lemma grandPotential_transition (γN t m : ℝ) : grandPotential γN t m m = 0 := by
  unfold grandPotential; rw [sRen_transition]; ring

/-- **`Ω` and its first `μ`-derivative vanish at `μ = m`**: `∂Ω/∂μ = −d = 0` there, so the grand
potential joins the trivial phase to first order — a hallmark of a *continuous* (second-order) transition. -/
lemma grandPotential_hasDerivAt_transition (γN t m : ℝ) :
    HasDerivAt (fun μ => grandPotential γN t μ m) 0 m := by
  have h := (sRen_hasDerivAt γN t m m).neg
  simp only [grandPotential]
  rw [density_transition] at h
  exact h.congr_deriv (by ring)

/-- **The second derivative jumps to `−2 γN t⁴ m²`**: `∂²Ω/∂μ² = −∂d/∂μ`, and `∂d/∂μ = 2 γN t⁴ m²` at
`μ = m` (from `density_hasDerivAt`, `3m²−m² = 2m²`). This nonzero jump from the trivial phase (`Ω`
constant, `∂²Ω/∂μ² = 0`) is exactly the paper's `−2γ𝒩(2πα')⁴m²`, establishing the transition is second
order. -/
lemma density_slope_transition (γN t m : ℝ) :
    HasDerivAt (fun μ => density γN t μ m) (2 * γN * t ^ 4 * m ^ 2) m := by
  have h := density_hasDerivAt γN t m m
  exact h.congr_deriv (by ring)


/-- **`c ∼ ε`**: for `μ = m + ε` the condensate factors as `γN t³ m (2m+ε) ε`, linear in `ε` — the
mean-field order-parameter exponent. -/
lemma condensate_shift (γN t m ε : ℝ) :
    condensate γN t (m + ε) m = γN * t ^ 3 * m * (2 * m + ε) * ε := by
  unfold condensate; ring

/-- **`d ∼ ε`**: for `μ = m + ε` the density factors as `γN t⁴ (m+ε)(2m+ε) ε`, linear in `ε`. -/
lemma density_shift (γN t m ε : ℝ) :
    density γN t (m + ε) m = γN * t ^ 4 * (m + ε) * (2 * m + ε) * ε := by
  unfold density; ring

/-- **`Ω ∼ ε²`**: for `μ = m + ε` the grand potential factors as `−¼ γN t⁴ (2m+ε)² ε²`, quadratic in
`ε` — the mean-field free-energy exponent, so `Ω` and `∂Ω/∂μ` vanish but `∂²Ω/∂μ²` does not. -/
lemma grandPotential_shift (γN t m ε : ℝ) :
    grandPotential γN t (m + ε) m = -(γN * t ^ 4 / 4) * (2 * m + ε) ^ 2 * ε ^ 2 := by
  unfold grandPotential sRen; ring

/-- **The order-parameter slope at the transition** `∂c/∂μ = 2 γN t³ m²` (`μ = m`): the condensate rises
linearly out of the transition, the mean-field `c ∼ ε` behaviour. -/
lemma condensate_slope_transition (γN t m : ℝ) :
    HasDerivAt (fun μ => condensate γN t μ m) (2 * γN * t ^ 3 * m ^ 2) m := by
  have h := condensate_hasDerivAt γN t m m
  exact h.congr_deriv (by ring)

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.FiniteBaryonDensityPhaseTransition

end
