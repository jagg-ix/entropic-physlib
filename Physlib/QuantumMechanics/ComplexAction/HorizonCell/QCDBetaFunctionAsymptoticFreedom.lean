/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecificLimits.Basic
meta import Zil

/-!
# QCD asymptotic freedom: the UV partner of the IR confinement area law (PDG 2026 §9)

Extends `ConfinementAreaLawEntropicWeight` with the **ultraviolet** face of QCD from the PDG 2026 Review of
Particle Physics (§9, *Quantum Chromodynamics*, Huston–Rabbertz–Zanderighi). Confinement (the area law, linear
potential) is the infrared behavior; **asymptotic freedom** is the ultraviolet behavior, and both follow from the
one-loop `β`-function.

The renormalization-group equation (PDG Eq. 9.3) is
`μ² dα_s/dμ² = β(α_s) = −(b₀ α_s² + b₁ α_s³ + …)`, with the **one-loop coefficient**
`b₀ = (11 C_A − 4 n_f T_R)/(12π) = (33 − 2 n_f)/(12π)` (SU(3), `C_A = 3`, `T_R = 1/2`). The **minus sign** is the
origin of asymptotic freedom.

* **`b₀` from the color Casimirs** (`betaZeroCoeff`, `betaZeroCoeff_casimir_su3`) — the SU(3) `C_A = 3`, `T_R = 1/2`
  give `b₀ = (33 − 2 n_f)/(12π)`;
* **asymptotic freedom ⟺ few flavors** (`asymptotic_freedom_iff`): `b₀ > 0 ⟺ n_f < 33/2`, so real QCD
  (`n_f ≤ 6`, `qcd_asymptotically_free`) is asymptotically free;
* **the `β`-function is negative** (`asymptotic_freedom_beta_negative`): `β = −b₀ α_s² < 0`, so the coupling runs
  *down* at high scale — free quarks in the UV;
* the **SU(3) color factors** (`su3_color_factors`): `C_F = (N²−1)/2N = 4/3`, `C_A = N = 3`, `N²−1 = 8` gluons.

Together with the confinement module this is the **UV/IR complementarity of QCD** (`qcd_uv_ir_complementarity`):
the same SU(3) that confines in the infrared (`b₀ > 0` drives `α_s` up near `Λ`, area-law Wilson loops) is
asymptotically free in the ultraviolet (`β < 0`, `α_s → 0`). One `β`-function, two regimes.

* **§A — `b₀` from the color Casimirs** (`betaZeroCoeff`, `betaZeroCoeff_casimir_su3`).
* **§B — asymptotic freedom ⟺ `n_f < 33/2`** (`asymptotic_freedom_iff`, `qcd_asymptotically_free`).
* **§C — the `β`-function is negative** (`asymptotic_freedom_beta_negative`).
* **§D — the SU(3) color factors** (`casimirFundamental`, `su3_color_factors`).
* **§E — UV/IR complementarity** (`qcd_uv_ir_complementarity`).
* **§F — dimensional transmutation** (`landauPoleTime`, `qcdScale`, `dimensional_transmutation`): the running
  coupling trades the dimensionless `α₀` for a dimensionful scale `Λ = μ₀ e^{−1/(b₀α₀)}` where `α_s` diverges.

**Honest layering.** Exact algebra/`positivity` on the one-loop coefficient and color Casimirs; the running
solution `α_s = 1/(b₀ ln Q²/Λ²)` and higher loops are *recorded*, not the full RGE flow. The confinement side is
the reused `ConfinementAreaLawEntropicWeight`. ## References

* Particle Data Group, PDG 2026 Review, §9 Quantum Chromodynamics, Eqs. 9.1–9.3 (`β`-function, color Casimirs).
  Repo carrier: `HorizonCell.ConfinementAreaLawEntropicWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom


/-- **The one-loop `β`-function coefficient** `b₀ = (33 − 2 n_f)/(12π)` (PDG Eq. 9.3) — `n_f` the number of quark
flavors. -/
noncomputable def betaZeroCoeff (n_f : ℝ) : ℝ := (33 - 2 * n_f) / (12 * Real.pi)

/-- **The adjoint Casimir** `C_A = N` (`= 3` for SU(3)). -/
def casimirAdjoint (N : ℝ) : ℝ := N

/-- **[`b₀` from the color Casimirs] `(11 C_A − 4 n_f T_R)/(12π) = (33 − 2 n_f)/(12π)`.** With the SU(3) color
factors `C_A = 3`, `T_R = 1/2`, the general one-loop coefficient reduces to the PDG value. -/
lemma betaZeroCoeff_casimir_su3 (n_f : ℝ) :
    (11 * casimirAdjoint 3 - 4 * n_f * (1 / 2)) / (12 * Real.pi) = betaZeroCoeff n_f := by
  unfold betaZeroCoeff casimirAdjoint; ring


/-- **[Asymptotic freedom ⟺ `n_f < 33/2`] `b₀ > 0 ⟺ n_f < 33/2`.** The one-loop coefficient is positive — the
coupling runs to zero in the UV — exactly when the number of quark flavors is below `33/2 = 16.5`. -/
lemma asymptotic_freedom_iff (n_f : ℝ) : 0 < betaZeroCoeff n_f ↔ n_f < 33 / 2 := by
  unfold betaZeroCoeff
  rw [div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · nlinarith [Real.pi_pos]
  · intro h
    exact Or.inl ⟨by linarith, by positivity⟩

/-- **[Real QCD is asymptotically free] `b₀ > 0` for `n_f ≤ 6`.** With at most six quark flavors (the Standard
Model), the one-loop coefficient is positive: QCD is asymptotically free. -/
lemma qcd_asymptotically_free (n_f : ℝ) (h : n_f ≤ 6) : 0 < betaZeroCoeff n_f :=
  (asymptotic_freedom_iff n_f).mpr (by linarith)


/-- **The one-loop `β`-function** `β(α_s) = −b₀ α_s²` (PDG Eq. 9.3, leading term). -/
noncomputable def betaFunction (b0 αs : ℝ) : ℝ := -b0 * αs ^ 2

/-- **[The `β`-function is negative — asymptotic freedom] `β < 0`.** For a positive one-loop coefficient `b₀ > 0`
and nonzero coupling, `β = −b₀ α_s² < 0`: the coupling *decreases* with the renormalization scale, becoming weak
at large momentum transfer — asymptotic freedom, the minus sign of PDG Eq. 9.3. -/
lemma asymptotic_freedom_beta_negative (b0 αs : ℝ) (hb : 0 < b0) (ha : αs ≠ 0) :
    betaFunction b0 αs < 0 := by
  unfold betaFunction
  have hsq : 0 < αs ^ 2 := by positivity
  nlinarith [hsq]


/-! ### One-loop running coupling and the asymptotic-freedom limit -/

/-- **The one-loop running coupling** `α_s(t) = α₀/(1 + b₀ α₀ t)`, `t = log(μ/μ₀)` the renormalization
"scale time" — the integral curve of the one-loop RG flow `dα_s/dt = β = −b₀ α_s²`. -/
noncomputable def runningCoupling (b0 α0 t : ℝ) : ℝ := α0 / (1 + b0 * α0 * t)

/-- **[The inverse coupling runs linearly] `1/α_s(t) = 1/α₀ + b₀ t`.** The reciprocal one-loop coupling is
an exact straight line in the scale time — the standard "`1/α` runs linearly" statement. -/
lemma runningCoupling_inv (b0 α0 t : ℝ) (h0 : α0 ≠ 0) (hd : 1 + b0 * α0 * t ≠ 0) :
    (runningCoupling b0 α0 t)⁻¹ = α0⁻¹ + b0 * t := by
  unfold runningCoupling
  rw [inv_div]
  field_simp

/-- **[The running coupling solves the one-loop RG flow] `dα_s/dt = β(α_s) = −b₀ α_s²`.** The *derivation*
(not the hypothesis): `α_s(t) = α₀/(1 + b₀ α₀ t)` is the integral curve of the one-loop `β`-function. -/
lemma runningCoupling_solves_rg (b0 α0 t : ℝ) (hd : 1 + b0 * α0 * t ≠ 0) :
    HasDerivAt (runningCoupling b0 α0) (betaFunction b0 (runningCoupling b0 α0 t)) t := by
  have hu : HasDerivAt (fun s => 1 + b0 * α0 * s) (b0 * α0) t := by
    simpa using ((hasDerivAt_id t).const_mul (b0 * α0)).const_add 1
  have hdiv := (hasDerivAt_const t α0).div hu hd
  have heq : (0 * (1 + b0 * α0 * t) - α0 * (b0 * α0)) / (1 + b0 * α0 * t) ^ 2
      = betaFunction b0 (runningCoupling b0 α0 t) := by
    unfold betaFunction runningCoupling
    rw [div_pow]
    field_simp
    ring
  rw [← heq]
  exact hdiv

/-- **[Asymptotic freedom as a limit] `α_s(t) → 0` as `t → ∞`.** For a positive one-loop coefficient
`b₀ > 0` and positive reference coupling, the running coupling *vanishes* in the deep ultraviolet — the
asymptotic-freedom statement as an actual limit, not merely the sign of `β`. -/
lemma runningCoupling_tendsto_zero (b0 α0 : ℝ) (hb : 0 < b0) (h0 : 0 < α0) :
    Filter.Tendsto (runningCoupling b0 α0) Filter.atTop (nhds 0) := by
  have hden : Filter.Tendsto (fun t => 1 + b0 * α0 * t) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left Filter.atTop 1
      (Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id)
  have hzero := (hden.inv_tendsto_atTop).const_mul α0
  rw [mul_zero] at hzero
  exact hzero.congr (fun x => by simp only [runningCoupling, div_eq_mul_inv, Pi.inv_apply])


/-! ### §F — dimensional transmutation: the running coupling generates the QCD scale `Λ` -/

/-- **The Landau-pole scale time** `t_Λ = −1/(b₀ α₀)` — the scale time at which the one-loop coupling
`α_s(t) = α₀/(1 + b₀ α₀ t)` diverges. Running *down* from the reference scale, asymptotic freedom reverses
into a strong-coupling pole. -/
noncomputable def landauPoleTime (b0 α0 : ℝ) : ℝ := -(b0 * α0)⁻¹

/-- **[The coupling diverges at the Landau pole] `1 + b₀ α₀ t_Λ = 0`.** At the Landau-pole scale time the
denominator of the one-loop running coupling vanishes — the strong-coupling pole. -/
lemma runningCoupling_denom_zero_landauPole (b0 α0 : ℝ) (hb : b0 ≠ 0) (h0 : α0 ≠ 0) :
    1 + b0 * α0 * landauPoleTime b0 α0 = 0 := by
  have hba : b0 * α0 ≠ 0 := mul_ne_zero hb h0
  unfold landauPoleTime
  rw [mul_neg, mul_inv_cancel₀ hba]; ring

/-- **[Dimensional transmutation — the inverse coupling vanishes at the pole] `1/α_s(t_Λ) = 0`**, i.e.
`1/α₀ + b₀ t_Λ = 0`. The dimensionless reference coupling `α₀` is traded for a *dimensionful* scale
`Λ = μ₀ e^{t_Λ}`: the running coupling manufactures a mass scale out of a pure number. -/
lemma inv_coupling_zero_landauPole (b0 α0 : ℝ) (hb : b0 ≠ 0) (h0 : α0 ≠ 0) :
    α0⁻¹ + b0 * landauPoleTime b0 α0 = 0 := by
  have hba : b0 * α0 ≠ 0 := mul_ne_zero hb h0
  unfold landauPoleTime
  field_simp
  ring

/-- **The QCD scale** `Λ = μ₀ · e^{t_Λ} = μ₀ · exp(−1/(b₀α₀))` — the renormalization-group-invariant mass
scale generated by dimensional transmutation, the scale at which `α_s` diverges (`≈ Λ_QCD`). -/
noncomputable def qcdScale (μ0 b0 α0 : ℝ) : ℝ := μ0 * Real.exp (landauPoleTime b0 α0)

/-- **[The QCD scale is positive] `Λ > 0`** for `μ₀ > 0`: a genuine dimensionful mass scale. -/
lemma qcdScale_pos (μ0 b0 α0 : ℝ) (hμ : 0 < μ0) : 0 < qcdScale μ0 b0 α0 := by
  unfold qcdScale; positivity

/-- **[Dimensional transmutation, assembled].** The one-loop running coupling trades the dimensionless
reference coupling `α₀` for a dimensionful scale: at the Landau-pole scale time `t_Λ = −1/(b₀α₀)` the
denominator of `α_s` vanishes (`runningCoupling_denom_zero_landauPole`) and the inverse coupling hits zero
(`inv_coupling_zero_landauPole`, `α_s → ∞`), so the scale `Λ = μ₀ e^{t_Λ} > 0` (`qcdScale_pos`) is
generated. A pure number becomes a mass scale — the origin of `Λ_QCD`, and with it the hadron mass scale
(`≈` the mass gap). -/
theorem dimensional_transmutation (μ0 b0 α0 : ℝ) (hμ : 0 < μ0) (hb : b0 ≠ 0) (h0 : α0 ≠ 0) :
    1 + b0 * α0 * landauPoleTime b0 α0 = 0
      ∧ α0⁻¹ + b0 * landauPoleTime b0 α0 = 0
      ∧ 0 < qcdScale μ0 b0 α0 :=
  ⟨runningCoupling_denom_zero_landauPole b0 α0 hb h0,
    inv_coupling_zero_landauPole b0 α0 hb h0,
    qcdScale_pos μ0 b0 α0 hμ⟩


/-- **The fundamental Casimir** `C_F = (N² − 1)/(2N)` (`= 4/3` for SU(3)) — the color factor for gluon emission
from a quark. -/
noncomputable def casimirFundamental (N : ℝ) : ℝ := (N ^ 2 - 1) / (2 * N)

/-- **[The SU(3) color factors] `C_F = 4/3`, `C_A = 3`, `N² − 1 = 8`.** The fundamental Casimir (quark gluon
emission), the adjoint Casimir (gluon gluon emission), and the eight gluons of `SU(3)` (PDG §9.1). -/
lemma su3_color_factors :
    casimirFundamental 3 = 4 / 3 ∧ casimirAdjoint 3 = 3 ∧ (3 : ℝ) ^ 2 - 1 = 8 := by
  refine ⟨?_, rfl, by norm_num⟩
  unfold casimirFundamental; norm_num


/-- **[QCD UV/IR complementarity].** The one `β`-function governs both regimes of the same SU(3): with `b₀ > 0`
(real QCD, `n_f ≤ 6`) it is

* **asymptotically free** in the UV — `β = −b₀ α_s² < 0`, the coupling runs down at high scale;
* **confining** in the IR — the area-law Wilson loop `e^{−σA} = kuikenWeight 1 (σA)` decreasing with area
  (`ConfinementAreaLawEntropicWeight`).

Asymptotic freedom (UV) and the confinement area law (IR) are the two faces of one QCD. -/
lemma qcd_uv_ir_complementarity (n_f αs σ : ℝ) (hn : n_f ≤ 6) (ha : αs ≠ 0) (hσ : 0 ≤ σ)
    {A1 A2 : ℝ} (hA : A1 ≤ A2) :
    0 < betaZeroCoeff n_f
      ∧ betaFunction (betaZeroCoeff n_f) αs < 0
      ∧ wilsonAreaLaw σ A2 ≤ wilsonAreaLaw σ A1 :=
  ⟨qcd_asymptotically_free n_f hn,
    asymptotic_freedom_beta_negative (betaZeroCoeff n_f) αs (qcd_asymptotically_free n_f hn) ha,
    confinement_obeys_gsl σ hσ hA⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.asymptotic_freedom_iff where
  formalizes @ "claim:su3-is-asymptotically-free-b0-positive-iff-fewer-than-thirty-three-halves-quark-flavours",
  supported_by @ "paper:pdg-2026-review-qcd"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.runningCoupling_solves_rg where
  formalizes @ "claim:the-one-loop-running-coupling-alpha0-over-one-plus-b0-alpha0-t-solves-the-rg-flow-dalpha-dt-equals-minus-b0-alpha-squared",
  requires @ "claim:su3-is-asymptotically-free-b0-positive-iff-fewer-than-thirty-three-halves-quark-flavours",
  supported_by @ "paper:pdg-2026-review-qcd"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.runningCoupling_tendsto_zero where
  formalizes @ "claim:the-running-coupling-vanishes-in-the-deep-ultraviolet-asymptotic-freedom-as-an-actual-limit",
  requires @ "claim:the-one-loop-running-coupling-alpha0-over-one-plus-b0-alpha0-t-solves-the-rg-flow-dalpha-dt-equals-minus-b0-alpha-squared",
  supported_by @ "paper:pdg-2026-review-qcd"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.dimensional_transmutation where
  formalizes @ "claim:dimensional-transmutation-the-running-coupling-trades-the-dimensionless-coupling-for-the-dimensionful-qcd-scale-lambda-where-alpha-diverges",
  requires @ "claim:the-one-loop-running-coupling-alpha0-over-one-plus-b0-alpha0-t-solves-the-rg-flow-dalpha-dt-equals-minus-b0-alpha-squared",
  supported_by @ "paper:pdg-2026-review-qcd",
  caveat @ "claim:the-one-loop-beta-function-coefficient-b0-is-taken-as-input-not-computed-from-the-loop-integral"

zil_file_contract physlib.qcdBetaFunctionAsymptoticFreedom where
  promises "The one-loop QCD beta function and its consequences: SU(3) is asymptotically free (b0 positive) iff fewer than thirty-three-halves quark flavours; the running coupling alpha0/(1+b0*alpha0*t) solves the RG flow d alpha/dt = -b0 alpha^2 and vanishes in the deep ultraviolet; and by dimensional transmutation the same flow trades the dimensionless coupling alpha0 for a dimensionful scale Lambda = mu0*exp(-1/(b0*alpha0)) at which the coupling diverges."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.betaZeroCoeff",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.betaFunction",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.runningCoupling"]
  forbids_substitutes ["a loop computation of the one-loop coefficient b0, which is taken as the PDG input",
    "a derivation of the numerical value of Lambda_QCD, left as a free scale generated from the free coupling"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.asymptotic_freedom_iff,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.runningCoupling_solves_rg,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.runningCoupling_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.dimensional_transmutation]

/- ZIL-END -/
