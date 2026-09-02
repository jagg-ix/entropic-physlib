/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Uncertainty
public import Physlib.QuantumMechanics.DDimensions.Operators.Commutation
public import Physlib.QuantumMechanics.DDimensions.Operators.Position
public import Physlib.QuantumMechanics.DDimensions.Operators.Momentum
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import Physlib.QuantumMechanics.PlanckConstant
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# Fujiwara's time–energy operator in the energy representation, and its clocks

Fujiwara's construction (Prog. Theor. Phys. 1980; *"time operator and the uncertainty relation"*) builds a
self-adjoint time operator canonically conjugate to energy on `L²(ℝ)` in the **energy representation**,
where the Hamiltonian is multiplication `H = E` and the time operator is `T = iℏ ∂_E`. This file realizes
that construction on physlib's `SpaceDHilbertSpace 1 = L²(ℝ)` — reusing the position/momentum `CLM`
machinery (`H ↦ positionCLM`, `T ↦ −momentumCLM`) — and links the resulting clock to the entropic-time
program.

## The canonical time–energy pair

* `energyOperator`, `timeOperator` — the unbounded operators `H = E`, `T = iℏ ∂_E` on the dense Schwartz
  core, each symmetric, densely-defined, and genuinely unbounded.
* `time_energy_ccr` — the exact canonical commutation relation `[T, H] = iℏ I`.
* `time_energy_uncertainty` — the genuine **Robertson** time–energy uncertainty `ΔT · ΔH ≥ ℏ/2` (the
  Mandelstam–Tamm quantum-speed-limit content, now a theorem, not a slogan).
* `generalizedTimeKet` — Fujiwara's generalized time-ket `⟨E|t⟩ = e^{−iEt/ℏ}` (a *generalized*
  eigenfunction, not an `L²` vector), with the eigen-equation `ℏ · age = t` (`generalizedTimeKet_eigen`).
* Fujiwara Eq. (5.9)–(5.11): the power-law transition family's energy/time variances and the strict
  uncertainty product `(ℏ/2)√(1 + correction)`.

## The three clocks the time-ket realizes

* **Misra age operator** (`MisraAgeFutureIncludedHerglotz.ageOperator`) — the generalized time-ket *is* an
  eigenfunction of the Misra internal-age operator, eigenvalue `t/ℏ` (`generalizedTimeKet_eigen`): the
  Fujiwara time operator is the Misra age operator in the energy representation.
* **Compton / entropic clock** `ω_C = mc²/ℏ` (`FrequencyTrinity.comptonFrequency`) — at the rest energy
  `E = mc²` the time-ket is exactly the Compton-clock phase `e^{−iω_C t}`
  (`generalizedTimeKet_restEnergy_eq_comptonClock`); at the Zitterbewegung energy `2mc²` it is `e^{−iω_Z t}`
  with `ω_Z = 2ω_C` (`zitterbewegung_rest_eq_two_compton`, `generalizedTimeKet_zitterbewegung_eq`).
* **The reversible (Connes–Rovelli) face** — the time-ket has unit modulus `‖⟨E|t⟩‖ = 1`
  (`generalizedTimeKet_modulus`): a purely unitary, entropy-free clock. This is the reversible /
  metric-preserving face of `CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge` — the
  bare Connes–Rovelli modular tick, as opposed to the dissipative Page–Wootters envelope `e^{−τ_ent}`.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open Complex

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator

open _root_.QuantumMechanics
open _root_.QuantumMechanics.SpaceDHilbertSpace
open _root_.QuantumMechanics.SpaceDHilbertSpace.SchwartzSubmodule
open LinearPMap
open SchwartzMap
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ## The energy representation: `H = E`, `T = iℏ ∂_E` on `L²(ℝ)` -/

abbrev EnergyHilbert := SpaceDHilbertSpace 1

/-- The energy operator on the Schwartz core: multiplication by `E` (physlib's `positionCLM`). -/
def energySchwartzCLM :
    𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  QuantumMechanics.positionCLM (0 : Fin 1)

/-- The time operator on the Schwartz core: `T = iℏ ∂_E`, i.e. `−momentumCLM` in the energy variable. -/
def timeSchwartzCLM :
    𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  -QuantumMechanics.momentumCLM (0 : Fin 1)

lemma timeEnergySchwartz_ccr (psi : 𝓢(Space 1, ℂ)) :
    timeSchwartzCLM (energySchwartzCLM psi) -
        energySchwartzCLM (timeSchwartzCLM psi) =
      (Complex.I * Constants.ℏ) • psi := by
  have h := congrArg
    (fun A : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) => A psi)
    (QuantumMechanics.position_commutation_momentum
      (d := 1) (0 : Fin 1) (0 : Fin 1))
  simpa [timeSchwartzCLM, energySchwartzCLM, Bracket.bracket,
    sub_eq_add_neg, add_comm] using h

def energyOperator : EnergyHilbert →ₗ.[ℂ] EnergyHilbert where
  domain := SchwartzSubmodule 1
  toFun := (schwartzIncl MeasureTheory.volume).toLinearMap ∘ₗ
    energySchwartzCLM.toLinearMap ∘ₗ
      (schwartzEquiv MeasureTheory.volume).symm.toLinearMap

def timeOperator : EnergyHilbert →ₗ.[ℂ] EnergyHilbert :=
  { domain := SchwartzSubmodule 1
    toFun := (schwartzIncl MeasureTheory.volume).toLinearMap ∘ₗ
      timeSchwartzCLM.toLinearMap ∘ₗ
        (schwartzEquiv MeasureTheory.volume).symm.toLinearMap }

lemma energyOperator_apply (psi : SchwartzSubmodule 1) :
    energyOperator psi =
      schwartzEquiv MeasureTheory.volume
        (energySchwartzCLM ((schwartzEquiv MeasureTheory.volume).symm psi)) := rfl

lemma timeOperator_apply (psi : SchwartzSubmodule 1) :
    timeOperator psi =
      schwartzEquiv MeasureTheory.volume (timeSchwartzCLM ((schwartzEquiv MeasureTheory.volume).symm psi)) := rfl

lemma energyOperator_range (psi : SchwartzSubmodule 1) :
    energyOperator psi ∈ SchwartzSubmodule 1 := by
  rw [energyOperator_apply]
  simp

lemma timeOperator_range (psi : SchwartzSubmodule 1) :
    timeOperator psi ∈ SchwartzSubmodule 1 := by
  rw [timeOperator_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma timeOperator_isSymmetric : timeOperator.IsSymmetric :=
  by
    intro psi phi
    have h := QuantumMechanics.momentumOperator_isSymmetric
      (0 : Fin 1) psi phi
    simpa [timeOperator_apply, timeSchwartzCLM,
      QuantumMechanics.momentumOperator_apply] using congrArg Neg.neg h

lemma timeOperator_hasDenseDomain : timeOperator.HasDenseDomain :=
  QuantumMechanics.SpaceDHilbertSpace.SchwartzSubmodule.dense 1 MeasureTheory.volume

lemma energyOperator_hasDenseDomain : energyOperator.HasDenseDomain :=
  QuantumMechanics.SpaceDHilbertSpace.SchwartzSubmodule.dense 1 MeasureTheory.volume

lemma energyOperator_isSymmetric : energyOperator.IsSymmetric := by
  intro psi phi
  obtain ⟨f, rfl⟩ := (schwartzEquiv MeasureTheory.volume).surjective psi
  obtain ⟨g, rfl⟩ := (schwartzEquiv MeasureTheory.volume).surjective phi
  simp only [energyOperator_apply, ← Submodule.coe_inner, schwartzEquiv_inner,
    (schwartzEquiv MeasureTheory.volume).symm_apply_apply]
  congr 1
  funext x
  simp [energySchwartzCLM, QuantumMechanics.positionCLM_apply]
  ring

lemma timeOperator_isUnbounded : timeOperator.IsUnbounded :=
  (timeOperator_isSymmetric.isUnbounded_iff_hasDenseDomain).mpr
    timeOperator_hasDenseDomain

lemma energyOperator_isUnbounded : energyOperator.IsUnbounded :=
  (energyOperator_isSymmetric.isUnbounded_iff_hasDenseDomain).mpr
    energyOperator_hasDenseDomain

set_option backward.isDefEq.respectTransparency false in
private lemma timeOperator_after_energy (psi : SchwartzSubmodule 1) :
    timeOperator ⟨energyOperator psi, energyOperator_range psi⟩ =
      schwartzEquiv MeasureTheory.volume
        (timeSchwartzCLM (energySchwartzCLM ((schwartzEquiv MeasureTheory.volume).symm psi))) := by
  rw [timeOperator_apply]
  have hsymm :
      (schwartzEquiv MeasureTheory.volume).symm
          (⟨energyOperator psi, energyOperator_range psi⟩ : SchwartzSubmodule 1) =
        energySchwartzCLM ((schwartzEquiv MeasureTheory.volume).symm psi) := by
    apply (schwartzEquiv MeasureTheory.volume).injective
    apply Subtype.ext
    simpa using energyOperator_apply psi
  change (schwartzEquiv MeasureTheory.volume
      (timeSchwartzCLM
        ((schwartzEquiv MeasureTheory.volume).symm
          (⟨energyOperator psi, energyOperator_range psi⟩ : SchwartzSubmodule 1))) :
        EnergyHilbert) =
    _
  rw [hsymm]

set_option backward.isDefEq.respectTransparency false in
private lemma energyOperator_after_time (psi : SchwartzSubmodule 1) :
    energyOperator ⟨timeOperator psi, timeOperator_range psi⟩ =
      schwartzEquiv MeasureTheory.volume
        (energySchwartzCLM (timeSchwartzCLM ((schwartzEquiv MeasureTheory.volume).symm psi))) := by
  rw [energyOperator_apply]
  have hsymm :
      (schwartzEquiv MeasureTheory.volume).symm
          (⟨timeOperator psi, timeOperator_range psi⟩ : SchwartzSubmodule 1) =
        timeSchwartzCLM ((schwartzEquiv MeasureTheory.volume).symm psi) := by
    apply (schwartzEquiv MeasureTheory.volume).injective
    apply Subtype.ext
    simpa using timeOperator_apply psi
  change (schwartzEquiv MeasureTheory.volume
      (energySchwartzCLM
        ((schwartzEquiv MeasureTheory.volume).symm
          (⟨timeOperator psi, timeOperator_range psi⟩ : SchwartzSubmodule 1))) :
        EnergyHilbert) =
    _
  rw [hsymm]

/-- **[The canonical time–energy commutation relation]** `[T, H] = iℏ I` on the Schwartz core — the exact
CCR making `T` conjugate to the energy. -/
lemma time_energy_ccr (psi : SchwartzSubmodule 1) :
    timeOperator ⟨energyOperator psi, energyOperator_range psi⟩ -
      energyOperator ⟨timeOperator psi, timeOperator_range psi⟩ =
        (Complex.I * Constants.ℏ) • (psi : EnergyHilbert) := by
  rw [timeOperator_after_energy, energyOperator_after_time]
  have h := congrArg
    (fun f : 𝓢(Space 1, ℂ) => (schwartzEquiv MeasureTheory.volume f : EnergyHilbert))
    (timeEnergySchwartz_ccr ((schwartzEquiv MeasureTheory.volume).symm psi))
  simpa using h

lemma rawTimeEnergyCommutatorExpectation (psi : SchwartzSubmodule 1)
    (hpsi_norm : ‖(psi : EnergyHilbert)‖ = 1) :
    rawCommutatorExpectation timeOperator energyOperator psi psi.property
        (timeOperator_range psi) (energyOperator_range psi) =
      Complex.I * (Constants.ℏ : ℝ) := by
  have hpsi :
      (⟨(psi : EnergyHilbert), psi.property⟩ : energyOperator.domain) = psi := by
    apply Subtype.ext
    rfl
  simp only [rawCommutatorExpectation, hpsi]
  rw [time_energy_ccr, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hpsi_norm]
  norm_num

/-- **[Robertson time–energy uncertainty]** `ℏ/2 ≤ ΔT · ΔH` — the genuine Robertson bound from the exact
CCR `[T, H] = iℏ`; the Mandelstam–Tamm / quantum-speed-limit content of the Fujiwara time operator. -/
theorem time_energy_uncertainty (psi : SchwartzSubmodule 1)
    (hpsi_norm : ‖(psi : EnergyHilbert)‖ = 1) :
    (Constants.ℏ : ℝ) / 2 ≤
      standardDeviation timeOperator psi *
        standardDeviation energyOperator ⟨psi, psi.property⟩ := by
  have h := state_uncertainty_of_raw_commutator
    timeOperator energyOperator timeOperator_isSymmetric energyOperator_isSymmetric
    psi psi.property hpsi_norm (timeOperator_range psi) (energyOperator_range psi)
    (rawTimeEnergyCommutatorExpectation psi hpsi_norm)
  simpa [abs_of_pos Constants.ℏ_pos] using h

/-! ## Fujiwara's generalized time-ket, and the Misra age operator -/

/-- Fujiwara's generalized time eigenfunction in the full-real-line energy representation `⟨E|t⟩ =
e^{−iEt/ℏ}`. It is a generalized eigenfunction, not an `L²` eigenvector. -/
noncomputable def generalizedTimeKet (t : ℝ) : ℝ → ℂ :=
  liouvilleEvolve (t / (Constants.ℏ : ℝ)) (fun _ => 1)

lemma generalizedTimeKet_eq (t E : ℝ) :
    generalizedTimeKet t E =
      Complex.exp (-Complex.I * (E : ℂ) * (t / (Constants.ℏ : ℝ))) := by
  simp [generalizedTimeKet, liouvilleEvolve]

/-- **[Fujiwara's generalized time-ket is the Misra age eigenfunction]** `ℏ · age ⟨E|t⟩ = t · ⟨E|t⟩` —
the Fujiwara time operator is the Misra internal-age operator (`MisraAgeFutureIncludedHerglotz.ageOperator`)
in the energy representation, with eigenvalue `t/ℏ`. -/
theorem generalizedTimeKet_eigen (t E : ℝ) :
    ((Constants.ℏ : ℝ) : ℂ) * ageOperator (generalizedTimeKet t) E =
      (t : ℂ) * generalizedTimeKet t E := by
  have h := ageOperator_liouvilleEvolve
    (t / (Constants.ℏ : ℝ)) (fun _ : ℝ => (1 : ℂ)) E
      (differentiableAt_const (c := (1 : ℂ)))
  simp only [generalizedTimeKet, ageOperator, deriv_const, mul_zero, zero_add] at h ⊢
  rw [h]
  simp only [liouvilleEvolve, mul_one]
  push_cast
  field_simp [Constants.ℏ_ne_zero]

/-! ## The clocks: Compton / Zitterbewegung phase, and the reversible face -/

/-- **[The time-ket at the rest energy is the Compton clock]** `⟨mc²|t⟩ = e^{−iω_C t}` with
`ω_C = mc²/ℏ = FrequencyTrinity.comptonFrequency`: at the rest energy Fujiwara's generalized time-ket is
exactly the Compton (entropic-clock) phase — the anchored fundamental tick. -/
theorem generalizedTimeKet_restEnergy_eq_comptonClock (t m c : ℝ) :
    generalizedTimeKet t (m * c ^ 2) =
      Complex.exp (-Complex.I * ((comptonFrequency m c (Constants.ℏ : ℝ) : ℝ) : ℂ) * (t : ℂ)) := by
  rw [generalizedTimeKet_eq]
  congr 1
  simp only [comptonFrequency]
  push_cast
  ring

/-- **[The time-ket at the Zitterbewegung energy is the Zitterbewegung clock]** `⟨2mc²|t⟩ = e^{−iω_Z t}`
with `ω_Z = 2ω_C = FrequencyTrinity.zitterbewegungFrequency 0 m c ℏ` (`zitterbewegung_rest_eq_two_compton`):
the `E₊ − E₋` Dirac-branch splitting energy gives the rest-frame Zitterbewegung phase. -/
theorem generalizedTimeKet_zitterbewegung_eq (t m c : ℝ) (hm : 0 ≤ m) :
    generalizedTimeKet t (2 * (m * c ^ 2)) =
      Complex.exp (-Complex.I *
        ((zitterbewegungFrequency 0 m c (Constants.ℏ : ℝ) : ℝ) : ℂ) * (t : ℂ)) := by
  rw [generalizedTimeKet_eq]
  congr 1
  rw [zitterbewegung_rest_eq_two_compton m c (Constants.ℏ : ℝ) hm]
  simp only [comptonFrequency]
  push_cast
  ring

/-- **[The Fujiwara clock is reversible / unitary]** `‖⟨E|t⟩‖ = 1` — the generalized time-ket has unit
modulus for every energy and time: a purely unitary, entropy-free clock. This is the reversible /
metric-preserving face of `CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge` — the
bare Connes–Rovelli modular tick, as opposed to the dissipative Page–Wootters envelope `e^{−τ_ent}`. -/
theorem generalizedTimeKet_modulus (t E : ℝ) : ‖generalizedTimeKet t E‖ = 1 := by
  rw [generalizedTimeKet_eq,
    show -Complex.I * (E : ℂ) * (t / (Constants.ℏ : ℝ))
        = ((-(E * (t / (Constants.ℏ : ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ## Fujiwara's power-law transition family, Eq. (5.9)–(5.11) -/

/-- Fujiwara Eq. (5.9), the energy variance of the power-law transition family. -/
noncomputable def transitionEnergyVariance (alpha beta c : ℝ) : ℝ :=
  c ^ 2 / (4 * alpha + 4 * beta - 3)

/-- Fujiwara Eq. (5.10), the time variance of the same transition family. -/
noncomputable def transitionTimeVariance (alpha beta c : ℝ) : ℝ :=
  (alpha + beta) * (alpha + beta - 1 / 4) * (Constants.ℏ : ℝ) ^ 2 /
    ((alpha + beta + 1 / 2) * c ^ 2)

/-- The positive correction in Fujiwara Eq. (5.11), written in terms of the
combined transition exponent `s = alpha + beta`. -/
noncomputable def transitionUncertaintyCorrection (s : ℝ) : ℝ :=
  3 / ((2 * s + 1) * (4 * s - 3))

/-- Fujiwara Eq. (5.11), the uncertainty product for the explicit transition family. -/
noncomputable def transitionUncertaintyProduct (s : ℝ) : ℝ :=
  (Constants.ℏ : ℝ) / 2 *
    Real.sqrt (1 + transitionUncertaintyCorrection s)

/-- **[Fujiwara Eq. (5.11)]** the transition-family variance product `Var[T]·Var[H] = (ℏ/2)²(1 +
correction)` — the explicit power-law family saturates the Robertson bound only up to the strictly
positive correction. -/
theorem transition_variance_product_eq (alpha beta c : ℝ)
    (hc : c ≠ 0)
    (hden₁ : 4 * alpha + 4 * beta - 3 ≠ 0)
    (hden₂ : alpha + beta + 1 / 2 ≠ 0) :
    transitionTimeVariance alpha beta c *
        transitionEnergyVariance alpha beta c =
      ((Constants.ℏ : ℝ) / 2) ^ 2 *
        (1 + transitionUncertaintyCorrection (alpha + beta)) := by
  have hden₃ : 2 * (alpha + beta) + 1 ≠ 0 := by
    intro h
    apply hden₂
    linarith
  have hden₄ : 4 * (alpha + beta) - 3 ≠ 0 := by
    intro h
    apply hden₁
    linarith
  have hprod : (2 * (alpha + beta) + 1) * (4 * (alpha + beta) - 3) ≠ 0 :=
    mul_ne_zero hden₃ hden₄
  have hL : (alpha + beta + 1 / 2) * c ^ 2 * (4 * alpha + 4 * beta - 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hden₂ (pow_ne_zero 2 hc)) hden₁
  unfold transitionTimeVariance transitionEnergyVariance transitionUncertaintyCorrection
  rw [div_mul_div_comm, add_div' 3 1 _ hprod, ← mul_div_assoc, div_eq_div_iff hL hprod]
  ring

theorem transitionUncertaintyCorrection_pos {s : ℝ} (hs : 3 / 4 < s) :
    0 < transitionUncertaintyCorrection s := by
  unfold transitionUncertaintyCorrection
  apply div_pos
  · norm_num
  · exact mul_pos (by nlinarith) (by nlinarith)

/-- **[The transition family strictly exceeds the Robertson bound]** `ℏ/2 < ΔT · ΔH` for the power-law
family with `s = α + β > 3/4` — a concrete state family for which the time–energy product is strictly
above the minimum. -/
theorem transitionUncertaintyProduct_strict {s : ℝ} (hs : 3 / 4 < s) :
    (Constants.ℏ : ℝ) / 2 < transitionUncertaintyProduct s := by
  have hc := transitionUncertaintyCorrection_pos hs
  have hrad : 0 ≤ 1 + transitionUncertaintyCorrection s := by linarith
  have hsqrt_sq :
      (Real.sqrt (1 + transitionUncertaintyCorrection s)) ^ 2 =
        1 + transitionUncertaintyCorrection s := Real.sq_sqrt hrad
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (1 + transitionUncertaintyCorrection s) := Real.sqrt_nonneg _
  have hsqrt : 1 < Real.sqrt (1 + transitionUncertaintyCorrection s) := by
    nlinarith
  have hh : 0 < (Constants.ℏ : ℝ) / 2 := half_pos Constants.ℏ_pos
  simpa [transitionUncertaintyProduct] using mul_lt_mul_of_pos_left hsqrt hh

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator

end

end

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator in
#physlib_axiom_clean_all [
  time_energy_ccr,
  time_energy_uncertainty,
  generalizedTimeKet_eigen,
  generalizedTimeKet_restEnergy_eq_comptonClock,
  generalizedTimeKet_zitterbewegung_eq,
  generalizedTimeKet_modulus,
  transition_variance_product_eq,
  transitionUncertaintyProduct_strict ]

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator in
#physlib_non_vacuous_all [
  time_energy_ccr,
  time_energy_uncertainty,
  generalizedTimeKet_eigen,
  generalizedTimeKet_restEnergy_eq_comptonClock,
  generalizedTimeKet_zitterbewegung_eq,
  generalizedTimeKet_modulus,
  transition_variance_product_eq,
  transitionUncertaintyProduct_strict ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.time_energy_ccr where
  formalizes @ "claim:the-fujiwara-time-operator-is-canonically-conjugate-to-energy-commutator-i-hbar",
  supported_by @ "paper:fujiwara-1980-time-operator-and-the-uncertainty-relation"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.time_energy_uncertainty where
  formalizes @ "claim:the-fujiwara-time-energy-robertson-uncertainty-delta-t-delta-h-is-at-least-hbar-over-two",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.time_energy_ccr"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.generalizedTimeKet_eigen where
  formalizes @ "claim:the-fujiwara-generalized-time-ket-is-the-misra-age-operator-eigenfunction-in-the-energy-representation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.MisraAgeFutureIncludedHerglotz.ageOperator_liouvilleEvolve"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.generalizedTimeKet_restEnergy_eq_comptonClock where
  formalizes @ "claim:the-fujiwara-time-ket-at-the-rest-energy-is-the-compton-entropic-clock-phase",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator.generalizedTimeKet_modulus where
  formalizes @ "claim:the-fujiwara-clock-is-reversible-unitary-unit-modulus-the-connes-rovelli-face",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge"

/- ZIL-END -/
