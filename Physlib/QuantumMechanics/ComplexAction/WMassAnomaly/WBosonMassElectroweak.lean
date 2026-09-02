/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Field.Basic

/-!
# The W boson mass: the electroweak Higgs mechanism and the tree-level mass relation

The `W` boson acquires mass through the Higgs mechanism, `M_W = ½ g v` (`g` the `SU(2)_L` coupling, `v` the
Higgs vacuum expectation value), while `M_Z = ½ √(g²+g'²) v` (`g'` the `U(1)_Y` coupling). Their ratio is the
**weak mixing (Weinberg) angle** `cos θ_W = g/√(g²+g'²)`, giving the **tree-level electroweak mass relation**

  `M_W = M_Z cos θ_W`,  equivalently the `ρ`-parameter `ρ = M_W² / (M_Z² cos²θ_W) = 1`.

* **§A — masses from the Higgs mechanism.** `wMass = ½ g v`, `zMass = ½ √(g²+g'²) v`, and the orthogonal
  photon stays massless (`photonMass = 0`).
* **§B — the weak mixing angle.** `cosWeinberg`, `sinWeinberg`, with `sin²θ_W + cos²θ_W = 1`
  (`sinSq_add_cosSq_weinberg`).
* **§C — the W boson mass relations.** `wMass_eq_zMass_mul_cosWeinberg` (`M_W = M_Z cos θ_W`),
  `rho_parameter_one` (`ρ = 1`), `wMass_lt_zMass` (`M_W < M_Z`, the `W` is lighter than the `Z`),
  `sinSq_weinberg_eq_one_sub_massSq_ratio` (the on-shell `sin²θ_W = 1 − M_W²/M_Z²`), and `wMass_pos`.

**Honest layering.** Proven: the tree-level algebraic relations between `M_W, M_Z, θ_W` and the couplings
`(g, g', v)` — `M_W = ½gv = M_Z cos θ_W`, `ρ = 1`, `M_W < M_Z`, `sin²+cos²=1`. The measured magnitudes
(`M_W ≈ 80.4 GeV`, `M_Z ≈ 91.19 GeV`, `sin²θ_W ≈ 0.223`), the radiative corrections to `ρ`, and the derivation
of the mass terms from the gauge-covariant kinetic term `|D_μ Φ|²` are inputs / analytic content, not derived
here.

## References

* S. Weinberg, *A model of leptons*, Phys. Rev. Lett. **19** (1967) 1264, doi:10.1103/PhysRevLett.19.1264;
  Particle Data Group, *Review of Particle Physics* (electroweak `M_W = M_Z cos θ_W`, `ρ = 1`). `Physlib`
  (`Particles.GaugeBosonZoo`, `Particles.GaugeBosonClassification`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak


/-- **The W boson mass** `M_W = ½ g v` — from the `SU(2)_L` coupling `g` and the Higgs VEV `v`. -/
noncomputable def wMass (g v : ℝ) : ℝ := g * v / 2

/-- **The Z boson mass** `M_Z = ½ √(g²+g'²) v` — `g'` is the `U(1)_Y` coupling. -/
noncomputable def zMass (g g' v : ℝ) : ℝ := Real.sqrt (g ^ 2 + g' ^ 2) * v / 2

/-- **The photon mass** `M_γ = 0` — the gauge combination orthogonal to the `Z` stays massless. -/
def photonMass : ℝ := 0

/-- **[The W boson is massive]** `M_W > 0` for `g, v > 0` — distinguishing it from the massless `γ` (the broken
vs unbroken generators of the electroweak group). -/
lemma wMass_pos (g v : ℝ) (hg : 0 < g) (hv : 0 < v) : 0 < wMass g v := by
  unfold wMass; positivity


/-- **`cos θ_W = g/√(g²+g'²)`** — the weak mixing angle's cosine. -/
noncomputable def cosWeinberg (g g' : ℝ) : ℝ := g / Real.sqrt (g ^ 2 + g' ^ 2)

/-- **`sin θ_W = g'/√(g²+g'²)`**. -/
noncomputable def sinWeinberg (g g' : ℝ) : ℝ := g' / Real.sqrt (g ^ 2 + g' ^ 2)

/-- **[The Weinberg angle is a genuine angle]** `sin²θ_W + cos²θ_W = 1`. -/
lemma sinSq_add_cosSq_weinberg (g g' : ℝ) (h : 0 < g ^ 2 + g' ^ 2) :
    sinWeinberg g g' ^ 2 + cosWeinberg g g' ^ 2 = 1 := by
  unfold sinWeinberg cosWeinberg
  rw [div_pow, div_pow, Real.sq_sqrt h.le, ← add_div, add_comm (g' ^ 2) (g ^ 2), div_self h.ne']


/-- **[The tree-level electroweak mass relation] `M_W = M_Z cos θ_W`** — the W boson mass is the Z mass times
the weak-mixing cosine; the `√(g²+g'²)` cancels, leaving `M_W = ½ g v`. -/
lemma wMass_eq_zMass_mul_cosWeinberg (g g' v : ℝ) (h : 0 < g ^ 2 + g' ^ 2) :
    wMass g v = zMass g g' v * cosWeinberg g g' := by
  have hS : Real.sqrt (g ^ 2 + g' ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr h
  unfold wMass zMass cosWeinberg
  field_simp

/-- **[The ρ-parameter is 1 at tree level] `ρ = M_W²/(M_Z² cos²θ_W) = 1`** — the custodial-symmetry relation,
a direct consequence of `M_W = M_Z cos θ_W`. -/
lemma rho_parameter_one (g g' v : ℝ) (hg : 0 < g) (hg' : 0 < g') (hv : 0 < v) :
    wMass g v ^ 2 / (zMass g g' v ^ 2 * cosWeinberg g g' ^ 2) = 1 := by
  have hS : 0 < g ^ 2 + g' ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt (g ^ 2 + g' ^ 2) := Real.sqrt_pos.mpr hS
  have hz : zMass g g' v ≠ 0 := by
    unfold zMass; exact div_ne_zero (mul_ne_zero hsqrt.ne' hv.ne') two_ne_zero
  have hc : cosWeinberg g g' ≠ 0 := by
    unfold cosWeinberg; exact div_ne_zero hg.ne' hsqrt.ne'
  rw [wMass_eq_zMass_mul_cosWeinberg g g' v hS, mul_pow,
    div_self (mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 hc))]

/-- **[The W is lighter than the Z] `M_W < M_Z`** — since `cos θ_W < 1` when `g' ≠ 0`. -/
lemma wMass_lt_zMass (g g' v : ℝ) (hg : 0 < g) (hg' : 0 < g') (hv : 0 < v) :
    wMass g v < zMass g g' v := by
  have hgs : g < Real.sqrt (g ^ 2 + g' ^ 2) := by
    rw [Real.lt_sqrt hg.le]; nlinarith [mul_pos hg' hg']
  unfold wMass zMass
  have hmul : g * v < Real.sqrt (g ^ 2 + g' ^ 2) * v := by gcongr
  linarith

/-- **[The on-shell weak mixing angle] `sin²θ_W = 1 − M_W²/M_Z²`** — the standard on-shell definition of the
Weinberg angle from the measured `W` and `Z` masses. -/
lemma sinSq_weinberg_eq_one_sub_massSq_ratio (g g' v : ℝ) (hg : 0 < g) (hg' : 0 < g') (hv : 0 < v) :
    sinWeinberg g g' ^ 2 = 1 - wMass g v ^ 2 / zMass g g' v ^ 2 := by
  have hS : 0 < g ^ 2 + g' ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt (g ^ 2 + g' ^ 2) := Real.sqrt_pos.mpr hS
  have hz : zMass g g' v ≠ 0 := by
    unfold zMass; exact div_ne_zero (mul_ne_zero hsqrt.ne' hv.ne') two_ne_zero
  have key : wMass g v ^ 2 / zMass g g' v ^ 2 = cosWeinberg g g' ^ 2 := by
    rw [wMass_eq_zMass_mul_cosWeinberg g g' v hS, mul_pow, mul_comm,
      mul_div_assoc, div_self (pow_ne_zero 2 hz), mul_one]
  rw [key, ← sinSq_add_cosSq_weinberg g g' hS]; ring

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak

end
