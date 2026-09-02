/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc

/-!
# The Yukawa (screened) potential and the entropic mass `M_eff = √(m² + λ)`

Formalizes the **exact, knot-free** content of the Yukawa-type Green's function with the complex-action/entropic-time entropic
mass shift (`equations-cal.md`, Eq. 26–27): the Euclidean propagator `1/(k² + M_eff²)` Fourier-transforms
to the **Yukawa / screened-Coulomb potential** `G(r) = e^{−M_eff r}/(4πr)` with effective mass

  `M_eff = √(m² + λ)`   (`entropicMass`),

the entropic action `λ` *screening* the potential by shifting `m² → m² + λ` (`entropicMass_sq`). The full
3-d Fourier transform needs analysis infrastructure beyond scope, so instead the **defining ODE** of the
Yukawa Green's function is formalized directly: the reduced potential `v(r) = r·G(r) ∝ e^{−M r}` satisfies
the **1-d screened Helmholtz equation**

  `v''(r) = M² v(r)`   (`reducedYukawa_screenedHelmholtz`),

the radial reduction of `(−Δ + M²)G = 0` away from the origin. With the entropic mass this reads
`v'' = (m² + λ) v` (`yukawa_entropic_screening`): the imaginary/entropic action `λ` is precisely the
screening mass-squared of the potential.

* the **entropic mass** `M_eff = √(m² + λ)`, `M_eff² = m² + λ` (`entropicMass`, `entropicMass_sq`);
* the **Yukawa potential** `G(r) = e^{−M r}/r` (`yukawaPotential`), positive (`yukawaPotential_pos`) and
  bounded by the Coulomb potential `1/r` (`yukawaPotential_le_coulomb`) — the screening;
* the **reduced potential** `v(r) = e^{−M r}` with `r·G = v` (`reducedYukawa_eq`), whose derivative is
  `−M v` (`hasDerivAt_reducedYukawa`) and which solves the screened Helmholtz equation `v'' = M² v`
  (`reducedYukawa_screenedHelmholtz`), `= (m² + λ) v` at the entropic mass (`yukawa_entropic_screening`).

* **§A — the entropic mass** (`entropicMass`, `entropicMass_sq`).
* **§B — the Yukawa potential and its screening** (`yukawaPotential`, `yukawaPotential_pos`,
  `yukawaPotential_le_coulomb`, `reducedYukawa`, `reducedYukawa_eq`).
* **§C — the screened Helmholtz equation** (`hasDerivAt_reducedYukawa`, `reducedYukawa_deriv`,
  `hasDerivAt_reducedYukawa_deriv`, `reducedYukawa_screenedHelmholtz`, `yukawa_entropic_screening`).

## References

* The Yukawa potential `e^{−Mr}/r` and the screened Poisson / modified Helmholtz equation (standard).
  Source note: `equations-cal.md` Eq. 26–27 (`M_eff = √(m² + λ)`, `G_E(r) ∼ e^{−M_eff r}/r`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential


/-- **The entropic effective mass** `M_eff = √(m² + λ)` — the propagator mass `m` shifted by the entropic
(imaginary) action `λ`, screening the Yukawa potential. -/
noncomputable def entropicMass (m lam : ℝ) : ℝ := Real.sqrt (m ^ 2 + lam)

/-- **[`M_eff² = m² + λ`]** the squared entropic mass is the propagator mass shifted by `λ` (for
`m² + λ ≥ 0`). -/
lemma entropicMass_sq (m lam : ℝ) (h : 0 ≤ m ^ 2 + lam) : entropicMass m lam ^ 2 = m ^ 2 + lam := by
  rw [entropicMass, Real.sq_sqrt h]


/-- **The Yukawa (screened-Coulomb) potential** `G(r) = e^{−M r}/r` — the radial Green's function of the
screened Poisson equation (dropping the `4π`). -/
noncomputable def yukawaPotential (M r : ℝ) : ℝ := Real.exp (-(M * r)) / r

/-- **[The Yukawa potential is positive] `G(r) > 0`** for `r > 0`. -/
lemma yukawaPotential_pos (M r : ℝ) (hr : 0 < r) : 0 < yukawaPotential M r :=
  div_pos (Real.exp_pos _) hr

/-- **[Screening: the Yukawa potential is bounded by the Coulomb potential] `G(r) ≤ 1/r`** for `M ≥ 0`,
`r > 0`. The exponential factor `e^{−M r} ≤ 1` screens the long-range Coulomb tail — the effect of the
entropic mass. -/
lemma yukawaPotential_le_coulomb (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r) :
    yukawaPotential M r ≤ 1 / r := by
  unfold yukawaPotential
  gcongr
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hM hr.le))

/-- **The reduced Yukawa potential** `v(r) = e^{−M r} = r·G(r)` — the radial Green's function with the
`1/r` removed, satisfying the 1-d screened Helmholtz equation. -/
noncomputable def reducedYukawa (M r : ℝ) : ℝ := Real.exp (-(M * r))

/-- **[`r·G(r) = v(r)`]** the reduced potential is `r` times the Yukawa potential (`r ≠ 0`). -/
lemma reducedYukawa_eq (M r : ℝ) (hr : r ≠ 0) : r * yukawaPotential M r = reducedYukawa M r := by
  unfold yukawaPotential reducedYukawa; field_simp


/-- **[First derivative] `v'(r) = −M v(r)`.** -/
lemma hasDerivAt_reducedYukawa (M r : ℝ) :
    HasDerivAt (reducedYukawa M) (-M * reducedYukawa M r) r := by
  have h1 : HasDerivAt (fun s => M * s) M r := by simpa using (hasDerivAt_id r).const_mul M
  have h2 := h1.neg.exp
  exact h2.congr_deriv (by simp [reducedYukawa, mul_comm])

/-- **The derivative of the reduced potential** as a function: `v' = −M v`. -/
lemma reducedYukawa_deriv (M : ℝ) : deriv (reducedYukawa M) = fun s => -M * reducedYukawa M s := by
  funext s; exact (hasDerivAt_reducedYukawa M s).deriv

/-- **[Second derivative] `(v')'(r) = M² v(r)`** — the derivative of `−M v` is `M² v`. -/
lemma hasDerivAt_reducedYukawa_deriv (M r : ℝ) :
    HasDerivAt (fun s => -M * reducedYukawa M s) (M ^ 2 * reducedYukawa M r) r := by
  have h := (hasDerivAt_reducedYukawa M r).const_mul (-M)
  exact h.congr_deriv (by ring)

/-- **[The reduced Yukawa potential solves the screened Helmholtz equation] `v'' = M² v`.** The reduced
radial Green's function `v(r) = e^{−M r}` satisfies the 1-d screened Helmholtz equation — the radial
reduction of `(−Δ + M²)G = 0` away from the origin, the defining ODE of the Yukawa Green's function. -/
lemma reducedYukawa_screenedHelmholtz (M r : ℝ) :
    deriv (deriv (reducedYukawa M)) r = M ^ 2 * reducedYukawa M r := by
  rw [reducedYukawa_deriv]
  exact (hasDerivAt_reducedYukawa_deriv M r).deriv

/-- **[The entropic action is the screening mass-squared] `v'' = (m² + λ) v`.** At the entropic mass
`M_eff = √(m² + λ)`, the reduced Yukawa potential solves the screened Helmholtz equation with screening
mass-squared `m² + λ`: the imaginary/entropic action `λ` is exactly the amount by which the propagator mass
is shifted to screen the potential. -/
lemma yukawa_entropic_screening (m lam r : ℝ) (h : 0 ≤ m ^ 2 + lam) :
    deriv (deriv (reducedYukawa (entropicMass m lam))) r
      = (m ^ 2 + lam) * reducedYukawa (entropicMass m lam) r := by
  rw [reducedYukawa_screenedHelmholtz, entropicMass_sq m lam h]



/-- **The screening length is the Compton wavelength**: in SI carriers the natural-units
screening mass is `M = mc/ħ`, and the reduced Yukawa factor is exactly the exponential decay
over the mediator's Compton wavelength — the range of the force *is* the mediator's clock
length (`FrequencyTrinity.comptonWavelength`).  The de Sitter face of this identity is
`Cosmology.FLRW.HorizonEntropyExpansion.comptonWavelength_eq_hubbleRadius_iff`. -/
theorem reducedYukawa_compton_screening {m c ħ r : ℝ} (hm : m ≠ 0) (hc : c ≠ 0)
    (hħ : ħ ≠ 0) :
    reducedYukawa (m * c / ħ) r
      = Real.exp (-(r / Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength m c ħ)) := by
  unfold reducedYukawa Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
  congr 1
  field_simp



/-- **The massless limit is the Coulomb/Newton kernel** `1/r` — the common kernel the BCJ
double copy squares (gauge `1/r` ↦ gravity `1/r`); a massive mediator deforms both sides of
the copy symmetrically. -/
theorem yukawaPotential_massless (r : ℝ) : yukawaPotential 0 r = 1 / r := by
  unfold yukawaPotential
  rw [zero_mul, neg_zero, Real.exp_zero]

/-- **One radius decides the screening mass**: at any fixed `r ≠ 0` the screened kernel is
injective in the mass — two screening masses that agree at a single radius are equal
(`Real.exp` is injective and the `1/r` prefactor cancels).  No sign hypothesis on the
masses is needed. -/
theorem yukawaPotential_inj {r : ℝ} (hr : r ≠ 0) {M₁ M₂ : ℝ}
    (h : yukawaPotential M₁ r = yukawaPotential M₂ r) : M₁ = M₂ := by
  unfold yukawaPotential at h
  rw [div_eq_div_iff hr hr] at h
  exact mul_right_cancel₀ hr (neg_inj.mp (Real.exp_injective (mul_right_cancel₀ hr h)))

/-- **The `1/r` kernel singles out zero screening mass**: matching the Coulomb/Newton
kernel at one radius forces `M = 0` exactly.  The derived static potential
(`EntropicNewtonConstantConvergence.newtonPotential_eq_massless_yukawa`) is therefore not
merely *a* member of the screened family — it is the *only* member passing through it:
every `M ≠ 0` alternative is excluded, and a graviton-mass bound is this exclusion read at
finite precision. -/
theorem yukawaPotential_screeningMass_unique {M r : ℝ} (hr : r ≠ 0)
    (h : yukawaPotential M r = 1 / r) : M = 0 :=
  yukawaPotential_inj hr (h.trans (yukawaPotential_massless r).symm)

/-- **Force screening is vacuum-entanglement decay**: the reduced Yukawa factor evaluated at
the Reeh–Schlieder scale `r = λ_C·log K` equals `tanh η = 1/K` — the inverse Schmidt number,
the Bogoliubov boost velocity (`FrequencyArc.vacuumBell_at_entropicScale`).  The screening
exponential and the vacuum Bell decay are the *same carrier*: a force's range is the distance
at which its mediator's vacuum correlations have decayed by one Schmidt unit. -/
theorem reducedYukawa_at_entropicScale {η m c ħ : ℝ} (hη : 0 < η)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    reducedYukawa (m * c / ħ)
        (Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength m c ħ * Real.log (Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber η))
      = Real.tanh η := by
  have hlam : Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength m c ħ ≠ 0 := by
    unfold Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength
    exact div_ne_zero hħ (mul_ne_zero hm hc)
  rw [reducedYukawa_compton_screening hm hc hħ]
  exact Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyArc.vacuumBell_at_entropicScale η m c ħ hη hlam

end Physlib.QuantumMechanics.ComplexAction.Yukawa.ScreenedPotential

end
