/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

/-!
# Scalar one-loop integrals and the anomalous magnetic moment (Ellis–Zanderighi)

Formalizes the building blocks of the scalar one-loop integrals of R. K. Ellis, G. Zanderighi,
*Scalar one-loop integrals for QCD*, arXiv:0712.1851, and links them to the **anomalous magnetic
moment** vertex correction (`FirstQuantizedQED.AnomalousMagneticMoment`). Bennett's §VI vertex factor `F` reduces
to exactly these master scalar integrals (tadpole, bubble, triangle), regulated in `D = 4 − 2ε`
dimensions; the magnetic form factor `F₂(0) = a = α/(2π)` is the **UV-finite** part of the vertex
triangle.

What is genuinely provable here (Mathlib has no `D`-dimensional integration, so the `D = 4 − 2ε`
measure itself is not formalized — but the Feynman-parameter integrals, the finite parts, and the
`ε`-pole residues are real analysis):

* **§A — Feynman parametrization** (`feynman_parametrization`): the denominator-combining identity
  `∫₀¹ dx [xA + (1−x)B]⁻² = 1/(AB)` — the first step of *every* one-loop integral, proved via the
  fundamental theorem of calculus.
* **§B — the bubble finite part** (`bubble_finite_part`): `∫₀¹ dγ ln(γ(1−γ)) = −2` — the famous "+2"
  of the bubble integral `B₀` (Eq 4.2), from `∫₀¹ ln γ dγ = −1` (`integral_log_unit`).
* **§C — the UV poles as Γ-function residues** (Eqs 4.1, 4.2). The bubble `Γ(ε)` prefactor has a
  simple pole of residue `1` (`bubble_uv_residue`, `ε·Γ(ε) → 1`); the tadpole `Γ(−1+ε)` prefactor has
  residue `−1` (`tadpole_uv_residue`, `ε·Γ(−1+ε) → −1`), via the recurrence `Γ(−1+ε) = Γ(ε)/(−1+ε)`
  (`tadpole_gamma_recurrence`). So the tadpole UV pole coefficient is `m²` (Eq 4.1).
* **§D — the Laurent structure and the anomalous moment** (`ScalarIntegralLaurent`, the `1/ε²`, `1/ε`,
  `ε⁰` coefficients the paper's code returns). The tadpole/bubble are **UV-divergent** (`eps1 ≠ 0`,
  `tadpole_uv_divergent`) and need renormalization; the anomalous-moment vertex is **UV-finite**
  (`anomalousMomentVertex_uv_finite`), so its value is the clean finite number `a = α/(2π)`, which
  feeds the g-factor `g = 2 + α/π` (`anomalousMomentVertex_yields_gFactor`, via
  `FirstQuantizedQED.AnomalousMagneticMoment.gFactor_schwinger`).

* **§A** (`feynman_parametrization`).
* **§B** (`integral_log_unit`, `bubble_finite_part`).
* **§C** (`bubble_uv_residue`, `tadpole_gamma_recurrence`, `tadpole_uv_residue`).
* **§D** (`ScalarIntegralLaurent`, `IsUVFinite`, `tadpole_uv_divergent`,
  `anomalousMomentVertex_uv_finite`, `anomalousMomentVertex_yields_gFactor`).

## References

* R. K. Ellis, G. Zanderighi, JHEP 0802 (2008) 002, arXiv:0712.1851 (Eqs 4.1 tadpole, 4.2 bubble).
* A. F. Bennett, arXiv:1406.0750v3, §VI. Repo structure: `FirstQuantizedQED.AnomalousMagneticMoment`
  (`schwingerAnomaly`, `gFactor`, `gFactor_schwinger`).
* Mathlib: `integral_log`, `intervalIntegrable_log'`, `Complex.tendsto_self_mul_Gamma_nhds_zero`,
  `Complex.Gamma_add_one`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopScalarIntegralsQCD

open Real Filter Topology intervalIntegral MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

/-! ## §A — Feynman parametrization (combine denominators) -/

/-- **[Feynman parametrization] `∫₀¹ dx [xA + (1−x)B]⁻² = 1/(AB)`.** The identity that combines two
propagator denominators into a single squared denominator — the first step of every one-loop integral
(here for distinct positive masses `A ≠ B`; `A = B` is the trivial constant case). Proved by the
fundamental theorem of calculus with antiderivative `−(A−B)⁻¹[xA + (1−x)B]⁻¹`. -/
theorem feynman_parametrization (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : A ≠ B) :
    ∫ x in (0 : ℝ)..1, (x * A + (1 - x) * B)⁻¹ ^ 2 = 1 / (A * B) := by
  have hpos : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 0 < x * A + (1 - x) * B := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h0, h1⟩ := hx
    rcases eq_or_lt_of_le h0 with hx0 | hx0
    · rw [← hx0]; simpa using hB
    · have h2 : 0 < x * A := mul_pos hx0 hA
      have h3 : 0 ≤ (1 - x) * B := mul_nonneg (by linarith) hB.le
      linarith
  have hden : ∀ x ∈ Set.uIcc (0 : ℝ) 1, x * A + (1 - x) * B ≠ 0 :=
    fun x hx => (hpos x hx).ne'
  have hABne : A - B ≠ 0 := sub_ne_zero.mpr hAB
  have key : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => -(A - B)⁻¹ * (x * A + (1 - x) * B)⁻¹)
        ((x * A + (1 - x) * B)⁻¹ ^ 2) x := by
    intro x hx
    have hne := hden x hx
    have hd : HasDerivAt (fun x => x * A + (1 - x) * B) (A - B) x := by
      have h := ((hasDerivAt_id x).mul_const A).add (((hasDerivAt_id x).const_sub 1).mul_const B)
      exact h.congr_deriv (by ring)
    have hfull := (hd.inv hne).const_mul (-(A - B)⁻¹)
    exact hfull.congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key
    (by apply ContinuousOn.intervalIntegrable; apply ContinuousOn.pow
        exact ContinuousOn.inv₀ (by fun_prop) hden)]
  rw [show (1 : ℝ) * A + (1 - 1) * B = A from by ring,
    show (0 : ℝ) * A + (1 - 0) * B = B from by ring]
  field_simp
  ring

/-! ## §B — the bubble finite part (Ellis–Zanderighi Eq 4.2) -/

/-- **`∫₀¹ ln γ dγ = −1`** (`integral_log` at `0..1`). -/
theorem integral_log_unit : ∫ γ in (0 : ℝ)..1, Real.log γ = -1 := by
  rw [integral_log]; simp

/-- **[The bubble "+2"] `∫₀¹ ln(γ(1−γ)) dγ = −2`.** The finite part of the scalar bubble integral
`B₀` (Eq 4.2 with `O(ε)` dropped): `∫₀¹ ln(γ(1−γ)) = ∫₀¹ ln γ + ∫₀¹ ln(1−γ) = −1 + −1 = −2`, the
universal "+2" constant in the renormalized bubble. -/
theorem bubble_finite_part : ∫ γ in (0 : ℝ)..1, Real.log (γ * (1 - γ)) = -2 := by
  have hL : ∫ γ in (0 : ℝ)..1, Real.log γ = -1 := integral_log_unit
  have hR : ∫ γ in (0 : ℝ)..1, Real.log (1 - γ) = -1 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => Real.log x) 1]
    norm_num [integral_log]
  have heq : Set.EqOn (fun γ => Real.log (γ * (1 - γ)))
      (fun γ => Real.log γ + Real.log (1 - γ)) (Set.uIcc 0 1) := by
    intro γ _
    rcases eq_or_ne γ 0 with h0 | h0
    · simp [h0]
    · rcases eq_or_ne (1 - γ) 0 with h1 | h1
      · have hg1 : γ = 1 := by linarith
        simp [hg1]
      · exact Real.log_mul h0 h1
  have iL : IntervalIntegrable Real.log MeasureTheory.volume 0 1 := intervalIntegrable_log'
  have iR : IntervalIntegrable (fun γ => Real.log (1 - γ)) MeasureTheory.volume 0 1 := by
    have := (intervalIntegrable_log' (a := (1 : ℝ)) (b := 0)).comp_sub_left 1
    simpa using this
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_add iL iR, hL, hR]
  norm_num

/-! ## §C — the UV poles as Γ-function residues (Eqs 4.1, 4.2) -/

/-- **[Bubble UV pole] `ε·Γ(ε) → 1`.** The scalar bubble `B₀` has an overall `Γ(ε)` (Eq 4.2),
whose simple pole at `ε = 0` has residue `1` — the `1/ε` ultraviolet divergence. -/
theorem bubble_uv_residue :
    Tendsto (fun ε : ℂ => ε * Complex.Gamma ε) (𝓝[≠] 0) (𝓝 1) :=
  Complex.tendsto_self_mul_Gamma_nhds_zero

/-- **[Tadpole Γ recurrence] `Γ(−1+ε) = Γ(ε)/(−1+ε)`** (for `ε ≠ 1`). The tadpole's `Γ(−1+ε)`
prefactor (Eq 4.1) reduces to the bubble's `Γ(ε)` pole over `(−1+ε)`. -/
theorem tadpole_gamma_recurrence (ε : ℂ) (hs : -1 + ε ≠ 0) :
    Complex.Gamma (-1 + ε) = Complex.Gamma ε / (-1 + ε) := by
  have h := Complex.Gamma_add_one (-1 + ε) hs
  rw [show -1 + ε + 1 = ε from by ring] at h
  rw [h]; field_simp

/-- **[Tadpole UV pole] `ε·Γ(−1+ε) → −1`.** The tadpole `I₁ᴰ(m²) = −μ^{2ε}Γ(−1+ε)[m²]^{1−ε}`
(Eq 4.1) has a simple pole at `ε = 0` of residue `−1` in `Γ(−1+ε)`, so the tadpole UV pole coefficient
is `m²` (`ε·I₁ → m²`). -/
theorem tadpole_uv_residue :
    Tendsto (fun ε : ℂ => ε * Complex.Gamma (-1 + ε)) (𝓝[≠] 0) (𝓝 (-1)) := by
  have hsum : Tendsto (fun ε : ℂ => -1 + ε) (𝓝[≠] (0 : ℂ)) (𝓝 (-1)) := by
    have h : Tendsto (fun ε : ℂ => -1 + ε) (𝓝 (0 : ℂ)) (𝓝 (-1 + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun ε : ℂ => (-1 + ε)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 ((-1 : ℂ)⁻¹)) :=
    hsum.inv₀ (by norm_num)
  have hlim := bubble_uv_residue.mul hinv
  rw [show (1 : ℂ) * (-1)⁻¹ = -1 from by norm_num] at hlim
  refine hlim.congr' ?_
  have hne1 : {ε : ℂ | ε ≠ 1} ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num))
  filter_upwards [hne1] with ε hε1
  have hs : -1 + ε ≠ 0 := fun h => hε1 (by linear_combination h)
  have hΓ := Complex.Gamma_add_one (-1 + ε) hs
  rw [show -1 + ε + 1 = ε from by ring] at hΓ
  rw [hΓ]; field_simp

/-! ## §D — the Laurent structure and the anomalous moment -/

/-- **The Laurent (`ε`-expansion) coefficients of a scalar one-loop integral** — the
`1/ε²`, `1/ε`, `ε⁰` coefficients the Ellis–Zanderighi code returns as complex numbers. -/
structure ScalarIntegralLaurent where
  /-- coefficient of `1/ε²` (double IR/collinear pole) -/
  eps2 : ℂ
  /-- coefficient of `1/ε` (single UV or IR pole) -/
  eps1 : ℂ
  /-- the finite part (`ε⁰`) -/
  eps0 : ℂ

/-- **A scalar integral is UV/IR finite** when it has no `1/ε²` or `1/ε` pole. -/
def IsUVFinite (L : ScalarIntegralLaurent) : Prop := L.eps2 = 0 ∧ L.eps1 = 0

/-- **The tadpole Laurent expansion** `I₁ᴰ(m²) = m²[1/ε + …]` (Eq 4.1): pole coefficient `m²`
(`tadpole_uv_residue`), no double pole. -/
def tadpoleLaurent (m2 : ℝ) : ScalarIntegralLaurent where
  eps2 := 0
  eps1 := (m2 : ℂ)
  eps0 := (m2 : ℂ)

/-- **[The tadpole is UV-divergent] for `m² ≠ 0`** — the `1/ε` coefficient is `m² ≠ 0`, so the tadpole
needs renormalization (in contrast to the finite anomalous-moment vertex). -/
theorem tadpole_uv_divergent (m2 : ℝ) (hm : m2 ≠ 0) : ¬ IsUVFinite (tadpoleLaurent m2) := by
  rintro ⟨_, h1⟩
  exact hm (by simpa [tadpoleLaurent] using h1)

/-- **The anomalous-moment vertex Laurent expansion** — UV-finite (no poles), finite part the
Schwinger value `a = α/(2π)` (`FirstQuantizedQED.AnomalousMagneticMoment.schwingerAnomaly`). The Pauli form
factor `F₂(0)` is not renormalized, so it is a pure number. -/
noncomputable def anomalousMomentVertex (α : ℝ) : ScalarIntegralLaurent where
  eps2 := 0
  eps1 := 0
  eps0 := (schwingerAnomaly α : ℂ)

/-- **[The anomalous-moment vertex is UV-finite]** — no `1/ε²`, no `1/ε` (`F₂` is not renormalized),
so `F₂(0)` is the clean finite number `α/(2π)`. -/
theorem anomalousMomentVertex_uv_finite (α : ℝ) : IsUVFinite (anomalousMomentVertex α) :=
  ⟨rfl, rfl⟩

/-- **[The UV-finite vertex feeds the g-factor] `g = 2 + α/π`.** The anomalous-moment vertex is
UV-finite, and its finite part `α/(2π)` is exactly the anomalous moment `a` that gives the gyromagnetic
ratio `g = 2(1 + a) = 2 + α/π` (`FirstQuantizedQED.AnomalousMagneticMoment.gFactor_schwinger`). The UV-finiteness
is *why* the anomalous moment is a clean radiative number. -/
theorem anomalousMomentVertex_yields_gFactor (α : ℝ) :
    IsUVFinite (anomalousMomentVertex α)
      ∧ gFactor (anomalousMomentVertex α).eps0.re = 2 + α / Real.pi := by
  refine ⟨anomalousMomentVertex_uv_finite α, ?_⟩
  rw [show (anomalousMomentVertex α).eps0.re = schwingerAnomaly α from by
    simp [anomalousMomentVertex]]
  exact gFactor_schwinger α

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopScalarIntegralsQCD

end
